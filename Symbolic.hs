{-# Language PatternSynonyms #-}
{-# Language ScopedTypeVariables #-}

module Symbolic
(
    Expr(..),
    isVariable,
    isConstant,
    simplify,
    negate,
    succ,
    pred,
    mapVariable,
    plugIn,
    evalExpr
)
where

-- infixl 4 :+:
-- infixl 5 :*:, :/:
-- infixr 6 :^:

data Expr a = Variable Char
            | Constant a
            -- Elementary arithmetic
            | Add (Expr a) (Expr a)
            | Mul (Expr a) (Expr a)
            | Div {dividend :: Expr a, divisor :: Expr a}
            | Pow {base :: Expr a, power :: Expr a}
            -- Calculus
            | Derivative {function :: Expr a, differential :: Expr a}
            | Integral {integrand :: Expr a,
                        differential :: Expr a,
                       -- if the bounds are Nothing, it's an indefinite integral
                       -- otherwise it's a definite integral
                       -- bounds : (lowerBound, upperBound)
                        bounds :: Maybe (Expr a, Expr a)}
            -- Functions
            | Sin (Expr a)
            | Cos (Expr a)
            | Tan (Expr a)
            | Log {antilogarithm :: Expr a, base :: Expr a}
            | Abs (Expr a)
            deriving Eq

instance (Eq a, Num a, Show a) => Show (Expr a) where
    -- show :: Expr a -> String
    show (Constant n) = show n
    show (Variable c) = [c]
    show (Add a b) = "(" ++ show a ++ ") + (" ++ show b ++ ")"
    show (Mul a b) | a == NegativeOne = "-(" ++ show b ++ ")"
                   | otherwise = "(" ++ show a ++ ") * (" ++ show b ++ ")"
    show (Div a b) = "(" ++ show a ++ ") / (" ++ show b ++ ")"
    show (Pow a b) = "(" ++ show a ++ ") ^ (" ++ show b ++ ")"
    show (Sin expr) = "sin(" ++ show expr ++ ")"
    show (Cos expr) = "cos(" ++ show expr ++ ")"
    show (Tan expr) = "tan(" ++ show expr ++ ")"
    show (Abs expr) = "|" ++ show expr ++ "|"
    show (Derivative f x) = "d/d(" ++ show x ++ ")  (" ++ show f ++")"
    show (Integral f x Nothing) = "∫ (" ++ show f ++ ") d(" ++ show x ++ ")"
    show (Integral f x (Just (lowerBound, upperBound))) =
        "∫_(" ++ show lowerBound ++ ")^(" ++ show upperBound ++ ") " ++
                "(" ++ show f ++ ") d(" ++ show x ++ ")"
    show (Log x b) = "log_(" ++ show b ++ ")" ++ " (" ++ show x ++ ")"

instance (Num a, Eq a, Ord a, Floating a) => Num (Expr a) where
    (+) = Add -- :: Num a => Expr a -> Expr a -> Expr a
    (*) = Mul -- :: Num a => Expr a -> Expr a -> Expr a

    -- negate :: Num a => Expr a -> Expr a
    negate (Constant n) = Constant (-n)
    negate (Add a b)    = Add (negate a) (negate b)
    negate (Mul a b)    = Mul (negate a) b
    negate (Pow a b)    = Mul NegativeOne (Pow a b)
    negate (Div a b)    = Div (negate a) b
    negate expr         = Mul NegativeOne expr

    -- signum :: Num a => Expr a -> Expr a
    signum (Constant n) = Constant $ signum n
    signum expr         = case simplify expr of
        Constant n -> Constant (signum n)
        _          -> error "Unresolved variables in expression"

    -- fromInteger :: Integer -> Expr a
    fromInteger n    = Constant (fromInteger n)

    -- abs :: Num a => Expr a -> Expr a
    abs (Constant n) = Constant (abs n)
    abs (Mul a b)    = Mul (abs a) (abs b)
    abs expr         = Abs expr

pattern Zero        = Constant 0    -- :: (Num a, Eq a) => Expr a
pattern One         = Constant 1    -- :: (Num a, Eq a) => Expr a
pattern Two         = Constant 2    -- :: (Num a, Eq a) => Expr a
pattern NegativeOne = Constant (-1) -- :: (Num a, Eq a) => Expr a
pattern E           = Constant 2.718281828459045
-- pattern Pi          = Constant 3.141592653589793

isVariable :: Expr a -> Bool
isVariable (Variable _) = True
isVariable _            = False

isConstant :: Expr a -> Bool
isConstant (Constant _) = True
isConstant _            = False

instance (Enum a, Num a, Ord a, Floating a) => Enum (Expr a) where
    -- succ :: (Num a, Eq a) => Expr a -> Expr a
    succ (Constant n) = Constant (n + 1)
    succ     expr     = expr + One

    -- pred :: (Num a, Eq a) => Expr a -> Expr a
    pred (Constant n) = Constant (n - 1)
    pred     expr     = expr - One

    toEnum x = Constant (fromIntegral x)

    fromEnum (Constant x) = fromEnum x
    fromEnum _            = error "Unresolved variables in expression"

sameVariable :: Expr a -> Expr a -> Bool
sameVariable (Variable _1) (Variable _2) = _1 == _2
sameVariable _ _ = False

sampleExpr :: Expr Double
sampleExpr = three * x `to` 2 -- 3x²
            where x = Variable 'x'
                  three = Constant 3

-- | Raise to exponent
to :: Expr a -> Expr a -> Expr a
to = Pow

-- | Get the reciprocal of
invert :: Expr a -> Expr a -> Expr a
invert = Div One

simplify :: (Num a, Ord a, Eq a, Floating a) => Expr a -> Expr a

simplify (Add (Constant a) (Constant b)) = Constant (a + b)
simplify (Add     expr          Zero   ) = simplify expr
simplify (Add     Zero          expr   ) = simplify expr

simplify (Mul (Constant a) (Constant b)) = Constant (a * b)
simplify (Mul      expr         One    ) = simplify expr
simplify (Mul      One          expr   ) = simplify expr
simplify (Mul      Zero          _     ) = Zero
simplify (Mul      _            Zero   ) = Zero

-- division
simplify (Div       _           Zero   ) = error "Division by zero!"
simplify (Div      Zero           _    ) = Zero
simplify (Div (Constant a) (Constant b))
    | a == b                             = One
    | otherwise                          = Constant (a / b)
simplify (Div      expr          One   ) = simplify expr

-- exponents/powers
simplify (Pow      Zero    (Constant b))
    | b <= 0                            = error "Cannot raise zero to non-positive power"
    | otherwise                         = Zero
simplify (Pow (Constant a) (Constant b))        = Constant (a**b)
simplify (Pow      expr         One    )        = simplify expr
simplify (Pow      One          expr   )        = One
simplify (Pow      Zero         expr   )        = Zero
simplify (Pow      expr         Zero   )        = One
simplify (Pow (Pow c (Constant b)) (Constant a)) = Pow c (Constant (a * b))

-- distribute/associate products
simplify (Mul (Constant a) (Mul (Constant b) expr)) = Constant (a*b) * simplify expr
simplify (Mul (Mul (Constant a) expr) Constant b)   = Constant (a*b) * simplify expr
simplify (Mul (Mul expr (Constant a)) Constant b)   = Constant (a*b) * simplify expr
simplify (Mul (Constant a) (Add b c))               =
    (Constant a * simplify b) + (Constant a * simplify c)

simplify (Div a b)          = simplify a `Div` simplify b
simplify (Pow a b)          = simplify a `Pow` simplify b
simplify (Mul a b)          = simplify a `Mul` simplify b
simplify (Add a b)          = simplify a `Add` simplify b
simplify (Abs (Constant n)) = Constant $ abs n
simplify (Abs (Abs expr))   = abs $ simplify expr
simplify (Abs expr)         = abs $ simplify expr
simplify (Sin expr)         = Sin $ simplify expr
simplify (Cos expr)         = Cos $ simplify expr
simplify (Tan expr)         = Tan $ simplify expr
simplify    expr            = expr

fullSimplify expr = fullSimplify' expr Zero
    where fullSimplify' cur last | cur == last = cur
                                 | otherwise   = fullSimplify' (simplify cur) cur

mapVariable :: (Char -> Expr a) -> Expr a -> Expr a
mapVariable f (Variable d) = f d
mapVariable _ (Constant a) = Constant a
mapVariable f (Add a b)    = Add (mapVariable f a) (mapVariable f b)
mapVariable f (Mul a b)    = Mul (mapVariable f a) (mapVariable f b)
mapVariable f (Pow a b)    = Pow (mapVariable f a) (mapVariable f b)
mapVariable f (Div a b)    = Div (mapVariable f a) (mapVariable f b)

plugIn :: Char -> a -> Expr a -> Expr a
plugIn c val = mapVariable (\x -> if x == c then Constant val else Variable x)

evalExpr :: (Num a, Floating a) => Char -> a -> Expr a -> a
evalExpr c x = evalExpr' . plugIn c x

evalExpr' :: (Num a, Floating a) => Expr a -> a
evalExpr' (Constant a) = a
evalExpr' (Variable c) = error $ "Variables ("
                                 ++ [c] ++
                                 ") still exist in formula. Try plugging in a value!"

evalExpr' (Add a b) = evalExpr' a + evalExpr' b
evalExpr' (Mul a b) = evalExpr' a * evalExpr' b
evalExpr' (Pow a b) = evalExpr' a ** evalExpr' b
evalExpr' (Div a b) = evalExpr' a / evalExpr' b

evalExpr' (Sin expr) = sin $ evalExpr' expr
evalExpr' (Cos expr) = cos $ evalExpr' expr
evalExpr' (Tan expr) = tan $ evalExpr' expr

-- differentiate _1 with respect to _2
-- differentiate u x = du(x)/dx
differentiate :: (Num a, Eq a, Floating a, Ord a) => Expr a -> Expr a -> Expr a
differentiate (Variable y) (Variable x)
    | x == y                 = One
 -- | otherwise              = Zero
    | otherwise              = Derivative { function = Variable y , differential = Variable x }
differentiate (Constant n) _ = Zero
differentiate (Add u v)  x   = Add (differentiate u x) (differentiate v x)
differentiate (Sin expr) x   = Cos expr `Mul` differentiate expr x
differentiate (Cos expr) x   = negate (Sin expr) `Mul` differentiate expr x
differentiate (Tan expr) x   = invert (Cos expr `to` 2) `Mul` differentiate expr x
--
-- product rule (f'g + fg')
differentiate (Mul u v) x    = (differentiate u x `Mul` v) `Add` (u `Mul` differentiate v x)
--
-- power rule / chain rule (n a(x)ⁿ⁻¹ a'(x))
-- differentiate (Pow E v) x    = (E `to` v) `Mul` differentiate v x
-- differentiate (Pow u v) x
--     | isConstant v           = (v `Mul` (u `to` pred v)) `Mul` differentiate u x
--     | otherwise              = Derivative { function = u `to` v , differential = x }
--
-- quotient rule ((u'v − v'u) / v²)
differentiate (Div u v) x    = Div (u' * v - v' * u) (v `to` Two)
                                where u' = differentiate u x
                                      v' = differentiate v x
differentiate expr dx        = Derivative expr dx
