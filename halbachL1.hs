import Data.List

data Con = Disjunction | Conjunction | Arrow | DoubleArrow
data Sentence = Atom Int | Compound Con Sentence Sentence | Negation Sentence

sentLetters :: Int -> Char
sentLetters 0 = 'P'
sentLetters 1 = 'Q'
sentLetters 2 = 'R'

instance Show Con where
     show Disjunction = "∨"
     show Conjunction = "∧"
     show Arrow = "->"
     show DoubleArrow = "<->"

instance Show Sentence where
     show (Compound con a b) = '(':show a ++ show con ++ show b ++ ")"
     show (Negation a) = '¬':show a
     show (Atom id) | id > 2    = sentLetters (id `mod` 3):show (id `div` 3)
                    | otherwise = [sentLetters id]

type Structure = [Bool]

foldSent :: (Int -> b) -> (Con -> b -> b -> b) -> (b -> b) -> Sentence -> b
foldSent a c n (Atom x) = a x
foldSent a c n (Compound con x y) = c con (foldSent a c n x) (foldSent a c n y)
foldSent a c n (Negation x) = n (foldSent a c n x)

truthCon :: Con -> Bool -> Bool -> Bool
truthCon Disjunction a b = a || b
truthCon Conjunction a b = a && b
truthCon Arrow a b = (not a) || b
truthCon DoubleArrow a b = a == b

truthSent :: Sentence -> Structure -> Bool
truthSent sent str = foldSent (\x -> str!!x) truthCon (\x -> not x) sent

countLetters :: Sentence -> Int
countLetters sent = (foldSent id (const (max)) id sent) + 1

possibleStructuresOfSize :: Int -> [Structure]
possibleStructuresOfSize n = rmdups $ flatten [permutations ((take a (repeat True)) ++
                                                             (take (n-a) (repeat False)))
                                               | a <- [0..n]]
          where flatten = (foldr (++) [])
                rmdups =  map head . group . sort

possibleStructures :: Sentence -> [Structure]
possibleStructures = possibleStructuresOfSize . countLetters

tautology :: Sentence -> Bool
tautology sent = and (map (truthSent sent) (possibleStructures sent))

data Argument = Entails [Sentence] Sentence

instance Show Argument where
     show (Entails premisses conclusion) = ((intercalate ", ").(map show)) premisses ++ '⊨':show conclusion

truthArg :: Argument -> Structure -> Bool
truthArg (Entails premisses conclusion) struct = truthSent conclusion struct || not (and (map (\x -> truthSent x struct) premisses))

logicallyValid :: Argument -> Bool
logicallyValid (Entails premisses conclusion) = not (or (map (\struct -> and (map (\sent -> truthSent sent struct)
                                                                                  premisses))
                                                             structsFConc)) 
      where structsFConc = filter (\s -> not (truthSent conclusion s)) -- structures in which the conclusion is false
                                  (possibleStructures conclusion)
