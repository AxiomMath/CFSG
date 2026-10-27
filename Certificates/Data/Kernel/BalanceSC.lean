module

public section

namespace CFSG.KC.BalanceSC

@[expose] def bitCount (n m : Nat) : Nat := ((List.range n).filter fun i => m.testBit i).length

@[expose] def rMasks (n r : Nat) : List Nat :=
  (List.range (2 ^ n)).filter fun m => bitCount n m == r

@[expose] def chains : List Nat → Nat → Nat → List (List Nat)
  | _, 0, _ => [[]]
  | [], _ + 1, _ => []
  | m :: S, k + 1, acc =>
    (if Nat.land m acc == 0 then (chains S k (Nat.lor acc m)).map (m :: ·) else []) ++
      chains S (k + 1) acc

@[expose] def partsK (n r k : Nat) : List (List Nat) := chains (rMasks n r) k 0

@[expose] def bitsOf (n m : Nat) : List Nat := (List.range n).filter fun i => m.testBit i

@[expose] def insEvery (a : Nat) : List Nat → List (List Nat)
  | [] => [[a]]
  | b :: l => (a :: b :: l) :: (insEvery a l).map (b :: ·)

@[expose] def perms : List Nat → List (List Nat)
  | [] => [[]]
  | a :: l => (perms l).flatMap (insEvery a)

@[expose] def lookImg (P I : List Nat) (x : Nat) : Nat := ((P.zip I).lookup x).getD x

@[expose] def cycMaps (b : Nat) (rest : List Nat) : List (List Nat × List Nat) :=
  (perms rest).map fun c => (b :: c, c ++ [b])

@[expose] def blockMaps : List (List Nat) → List (List Nat × List Nat)
  | [] => [([], [])]
  | [] :: _ => []
  | (b :: rest) :: Ls => (blockMaps Ls).flatMap fun PI =>
      (cycMaps b rest).map fun c => (c.1 ++ PI.1, c.2 ++ PI.2)

@[expose] def elemsOfPts (n : Nat) (Ls : List (List Nat)) : List (List Nat) :=
  (blockMaps Ls).map fun PI => (List.range n).map (lookImg PI.1 PI.2)

@[expose] def elemsOf (n : Nat) (L : List Nat) : List (List Nat) := elemsOfPts n (L.map (bitsOf n))

end CFSG.KC.BalanceSC
