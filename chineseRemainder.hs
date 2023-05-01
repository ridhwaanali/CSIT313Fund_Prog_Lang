{-# LANGUAGE UnicodeSyntax,FlexibleInstances #-}
import Control.Monad (foldM)

-- |Extended Euclidean algorithm
-- Given A,B, finds integers X,Y that satisfy Bézout's identity:
--   A*X + B*Y = gcd(A,B)
egcd a b = aux a b 1 0 0 1
  where aux r 0  x y _  _  = (r,x,y)
        aux r r' x y x' y' = aux r' r'' x' y' x'' y''
          where r'' = r `rem` r'
                q   = r `div` r'
                x'' = x - q * x'
                y'' = y - q * y'

-- |Finds the modular multiplicative inverse of @a@ modulo @m@.
-- Returns number X (iff it exists) that satisfy:
--   X*A ≡ 1 (mod m).
invert a m = case egcd a m of
              (1,x,_) -> Just x
              _       -> Nothing 

-- Syntax sugar.
type ℤ = Integer

-- |Solves a system of simultaneous congruences.
-- Chinese Remainder theorem determines a number X:
--   X ≡ a₀ (mod n₀)
--   X ≡ a₁ (mod n₁)
--   X ≡ a₂ (mod n₂)
--   ...
-- The input is a list of tuples: [(a₀,n₀), (a₁,n₁), (a₂,n₂)].
--
-- Note: On empty input, returns X ≡ 0 (mod 1).
class ChineseRemainder r where
  chineseRemainder ∷ [(ℤ,ℤ)] → r

-- Result is a tuple (X,M): X ≡ M
instance ChineseRemainder (Maybe (ℤ,ℤ)) where
  chineseRemainder = foldM aux (0,1)
    where aux (a,p) (b,q)
              | (a-b) `rem` k == 0 = Just (x, kmn)
              | otherwise          = Nothing
              where k       = gcd p q
                    m       = p `div` k
                    n       = q `div` k
                    (_,_,β) = k `egcd` (m*n)
                    (_,_,δ) = m `egcd` q
                    (_,_,ζ) = n `egcd` p
                    kmn     = p*n
                    x       = (a*β*m*n+a*δ*k*n+b*ζ*k*m) `rem` kmn

-- Result is a number X: X ≡ M (where M is a gcd of given modulis).
instance ChineseRemainder (Maybe ℤ) where
  chineseRemainder = fmap fst . (chineseRemainder ∷ [(ℤ,ℤ)] -> Maybe (ℤ,ℤ))

-- Result is a tuple of infinite lists of integers Xs, Ys:
--   ∀x∈Xs: x≥0, x ≡ X (mod M)
--   ∀x∈Xs: y<0, y ≡ X (mod M)
-- where X is a solution to a system of given simultaneous congruences.
instance ChineseRemainder (Maybe ([ℤ], [ℤ])) where
  chineseRemainder = fmap aux . chineseRemainder
    where aux (x,m) | x<0       = ([x+m,x+2*m..], [x,x-m..])
                    | otherwise = ([x,x+m..],     [x-m,x-2*m..])

-- Result is an infinite list of integers Xs:
--   ∀x∈Xs: x ≡ X (mod M)
-- where X is a solution to a system of given simultaneous congruences.
instance ChineseRemainder (Maybe [ℤ]) where
  chineseRemainder = fmap intertwine . chineseRemainder
    where intertwine ([],_) = []
          intertwine (_,[]) = []
          intertwine ((x:xs),(y:ys)) = x:y:intertwine (xs,ys)
