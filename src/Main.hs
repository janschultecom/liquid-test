{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--no-termination" @-}

module Main (
    main,
    columns,
    rows,
    calc,
    vlength,
    llength,
    tempAverage
    ) where

type Matrix a = [[a]]

data Text = Text

pack :: String -> Text
pack _ = undefined

takeWord16 :: Int -> Text -> Text
takeWord16 _ _ = Text


{-@ measure tlen :: Text -> Int @-}
{-@ pack :: s:String -> {t:Text | len s == tlen t} @-}

{-@ divx :: x:{Int | x /= 0} -> Int @-}
divx :: Int -> Int
divx x = 42 `div` x

{-@ headxs :: xs:{ [a] | len xs > 0 } -> a @-}
headxs :: [a] -> a
headxs xs = head xs

{-@ headxsys :: ys:[a] -> xs:{[a] | 0 < len xs + len ys} -> a @-}
headxsys :: [a] -> [a] -> a
headxsys ys xs = head (xs ++ ys)

{-@ avg :: xs:{[Int] | 0 < len xs } -> Int @-}
avg :: [Int] -> Int
avg xs = sum xs `div` length xs

{-@ safeTake :: i:Nat -> xs:{[a] | i <= len xs}-> [a] @-}
safeTake :: Int -> [a] -> [a]
safeTake 0 []     = []
safeTake i (x:xs) = if i == 0 then [] else x:safeTake (i-1) xs
--safeTake i []     = error "Out of bounds indexing!"

{-@ takeWord16 :: i:Nat -> xs:{Text | i <= tlen xs } -> Text @-}
heartbleed :: Text
heartbleed = takeWord16 7  (pack "zurihac")


{-@ measure vlength @-}
{-@ vlength :: [a] -> Nat @-}
vlength :: [a] -> Int
vlength [] = 0
vlength (x : xs) = 1 + vlength xs

{-@ inline rows @-}
{-@ rows :: Matrix a -> Nat @-}
rows :: Matrix a -> Int
rows xs = vlength xs

{-@ measure columns @-}
{-@ columns :: Matrix a -> Nat @-}
columns :: Matrix a -> Int
columns [] = 0
columns (x : xs) = vlength x

-- 3x4 4x6
-- 3x4 5x6
{-@ mult :: m1:{ Matrix a | true } -> m2:{ Matrix a | columns m1 == rows m2 }  -> Matrix a  @-}
mult :: Matrix a -> Matrix a -> Matrix a
mult left right = undefined

{-@ matrix2x3 :: {xs: Matrix Int | columns xs == 3 && rows xs == 2}  @-}
matrix2x3 :: Matrix Int
matrix2x3 = [[1,2,3],[4,5,6]]

{-@ matrix3x1 :: {xs: Matrix Int | columns xs == 2 && rows xs == 3}  @-}
matrix3x1 :: Matrix Int
matrix3x1 = [[10, 1],[20, 1],[30, 1]]

matrix4x1 :: Matrix Int
matrix4x1 = [[10],[20],[30],[40]]

correct :: Matrix Int
correct = mult matrix2x3 matrix3x1

foo :: () -> Int
foo _ = headxsys [1, 2, 3] []

{-@ impossible :: {v:_ | false} -> a @-}
impossible msg = error msg

{-@ safeDiv :: numerator:Int -> denominator:{ Int | denominator > 0 } -> result:Int   @-}
safeDiv :: Int -> Int -> Int
safeDiv _ 0 = impossible "divide-by-zero"
safeDiv x n = x `div` n

{-@ isPositive :: bla:Int -> res : { Bool | res <=> bla > 0 } @-}
isPositive :: Int -> Bool
isPositive x
    | x > 0 = True
    | otherwise = False

result n d
    | isPositive d = "Result = " ++ show (n `safeDiv` d)
    | otherwise = "Humph, please enter positive denominator!"

{-@ type Pos = {v:Int | 0 <= v} @-}
type Pos = Int

{-@ poss :: [Pos]               @-}
poss :: [Int]
poss =  [0, 1, 2, 3]

calc :: IO ()
calc = do
  putStrLn "Enter numerator"
  n <- readLn
  putStrLn "Enter denominator"
  d <- readLn
  putStrLn $ result n d
  calc

{-@ size'    :: { xs: [a] | 0 < len xs } -> Pos @-}
size' :: [a] -> Int
size' [_]    = 1
size' (_:xs) = 1 + size' xs
size' _      = impossible "size"

data List a = Emp               -- Nil
            | (:::) a (List a)  -- Cons

{-@ measure llength @-}
llength :: List a -> Int
llength Emp        = 0
llength (_ ::: xs) = 1 + llength xs

{-@ lhead        :: { xs : List a | llength xs > 0 } -> a @-}
lhead (x ::: _)  = x
lhead _          = impossible "head"

{-@ ltail        :: { xs : List a | llength xs > 0 } -> List a @-}
ltail (_ ::: xs) = xs
ltail _          = impossible "tail"

{-@ type ListNE a = {v:List a| 0 < llength v} @-}

lfoldr :: (a -> b -> b) -> b -> List a -> b
lfoldr _ acc Emp        = acc
lfoldr f acc (x ::: xs) = f x (lfoldr f acc xs)

{-@ lfoldr1 :: (a -> a -> a) -> ListNE a -> a @-}
lfoldr1 f (x ::: xs) = lfoldr f x xs
lfoldr1 _ _          = impossible "foldr1"

{-@ average' :: ListNE Int -> Int @-}
average' xs = total `div` n
  where
    total   = lfoldr1 (+) xs
    n       = llength xs

{-@ type Vect a N = {v: List a | llength v == N} @-}
{-@ data Year a = Year (Vect a 12) @-}
data Year a = Year (List a)

goodYear = Year (1 ::: (2 ::: (3 ::: (4 ::: (5 ::: (6 ::: (7 ::: (8 ::: (9 ::: (10 ::: (11 ::: (12 ::: Emp))))))))))))
--badYear = Year (1 ::: Emp)

{-@ lmap :: (a -> b) -> xs:List a -> res: { List b | llength res == llength xs}  @-}
lmap _ Emp         = Emp
lmap f (x ::: xs)  = f x ::: lmap f xs

data Weather = W { temp :: Int, rain :: Int }

tempAverage :: Year Weather -> Int
tempAverage (Year ms) = average' months -- ListNE
  where
    months            = lmap temp ms -- List Weather -> List Int

{-@ linit :: (Int -> a) -> n:Nat -> res : { List a | n == llength res } @-}
linit :: (Int -> a) -> Int -> List a
linit _ 0 = Emp
linit f n = f n ::: linit f (n-1)

sanDiegoTemp :: Year Int
sanDiegoTemp = Year (linit (const 72) 12)

{-@ init' :: (Int -> a) -> n:Nat -> res : { List a | n == llength res } @-}
init':: (Int -> a) -> Int -> List a
init' f n = go 0
  where
    -- i:0, n:1, llength res == 1 + 0
    -- i:1, n:1, llength res == 1
    {-@ go :: i:Nat -> res : { List a | i <= n <=> n - i == llength res } @-}
    go i | i < n     = f i ::: go (i+1)
         | otherwise = Emp

sanDiegoTemp' :: Year Int
sanDiegoTemp' = Year (init' (const 72) 12)

main :: IO ()
main = putStrLn $ show $ headxs [1]
