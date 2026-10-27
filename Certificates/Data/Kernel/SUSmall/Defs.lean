module

public import Certificates.Data.SUSmallCheck

public section

namespace CFSG.KC.SUSmall

open Certificates.SUSmall CFSG.StandardType.HdRo7SU.Small

@[expose] def pairOf (m : ℕ) (s : List ℕ) : Pair m :=
  (fun i => ((s.getD i.val 0 / 3 : ℕ) : ZMod 3), fun i => ((s.getD i.val 0 % 3 : ℕ) : ZMod 3))

@[expose] def noneOK {m : ℕ} (cat : List (Pair m)) (K : List (List ℕ)) (N : ℕ)
    (w : ℕ × ℕ × List ℕ) : Bool :=
  Nat.blt w.2.1 N && ckey (pairOf m w.2.2) == K.getD w.2.1 [] &&
    badPair (cat.getD w.1 0) (pairOf m w.2.2)

@[expose] def outOK {m : ℕ} (cat : List (Pair m)) (K : List (List ℕ)) (N : ℕ)
    (w : ℕ × ℕ × ℕ × List ℕ) : Bool :=
  Nat.blt w.2.1 N && Nat.blt w.2.2.1 N && ckey (pairOf m w.2.2.2) == K.getD w.2.1 [] &&
    ckey (conj (cat.getD w.1 0) (pairOf m w.2.2.2)) == K.getD w.2.2.1 []

@[expose] def cellNone (NW : List (ℕ × ℕ × List ℕ)) (x y : ℕ) : Bool :=
  NW.any fun w => w.1 == x && w.2.1 == y

@[expose] def cellOut (OW : List (ℕ × ℕ × ℕ × List ℕ)) (x y c : ℕ) : Bool :=
  OW.any fun w => w.1 == x && w.2.1 == y && w.2.2.1 == c

@[expose] def outsOf (OW : List (ℕ × ℕ × ℕ × List ℕ)) (x y : ℕ) : List ℕ :=
  (OW.filter fun w => w.1 == x && w.2.1 == y).map fun w => w.2.2.1

@[expose] def derivGo (NW : List (ℕ × ℕ × List ℕ)) (OW : List (ℕ × ℕ × ℕ × List ℕ)) :
    List ℕ → List (ℕ × ℕ × ℕ) → ℕ × ℕ → Bool
  | S, [], f => S.contains f.1 && S.contains f.2 && cellNone NW f.1 f.2
  | S, st :: t, f => S.contains st.1 && S.contains st.2.1 && cellOut OW st.1 st.2.1 st.2.2 &&
      derivGo NW OW (st.2.2 :: S) t f

@[expose] def survOK (N : ℕ) (SV : List ℕ) (DV : List (ℕ × List (ℕ × ℕ × ℕ) × ℕ × ℕ))
    (NW : List (ℕ × ℕ × List ℕ)) (OW : List (ℕ × ℕ × ℕ × List ℕ)) : Bool :=
  (List.range N).all fun a =>
    SV.contains a || DV.any fun d => d.1 == a && derivGo NW OW [2, a] d.2.1 d.2.2

@[expose] def admOK (NW : List (ℕ × ℕ × List ℕ)) (OW : List (ℕ × ℕ × ℕ × List ℕ))
    (S : List ℕ) : Bool :=
  S.contains 2 && S.all fun i => S.all fun j =>
    !cellNone NW i j && (outsOf OW i j).all S.contains

@[expose] def allSubs (P : List ℕ → Bool) : List ℕ → List ℕ → Bool
  | acc, [] => P acc.reverse
  | acc, x :: xs => allSubs P acc xs && allSubs P (x :: acc) xs

@[expose] def subsOK (SV : List ℕ) (AL : List (List ℕ)) (NW : List (ℕ × ℕ × List ℕ))
    (OW : List (ℕ × ℕ × ℕ × List ℕ)) : Bool :=
  allSubs (fun S => !admOK NW OW S || AL.contains S) [] SV

@[expose] def matchOK {m : ℕ} (K : List (List ℕ)) (N : ℕ) (S : List ℕ) (X : List (Pair m)) :
    Bool :=
  S.all (fun c => c == 2 || X.any fun q => ckey q == K.getD c []) &&
    X.all fun q => S.any fun c => Nat.blt c N && ckey q == K.getD c []

@[expose] def alOK {m : ℕ} (K : List (List ℕ)) (N : ℕ) (AL : List (List ℕ))
    (Xs : List (List (Pair m))) : Bool :=
  AL.all fun S => Xs.any (matchOK K N S)

@[expose] def zt (k l : ℕ) : Bool := (k / 3 == l / 3) == (k % 3 == l % 3)

@[expose] def allCompsZ (P : List ℕ → Bool) : ℕ → ℕ → ℕ → List ℕ → List ℕ → Bool
  | n, _, 0, _, acc => !(n == 0) || P acc.reverse
  | n, pos, k + 1, sup, acc => allCompsZ P n (pos + 1) k sup (0 :: acc) &&
      (!(sup.all fun s => zt s pos) || (List.range n).all fun a =>
        allCompsZ P (n - (a + 1)) (pos + 1) k (pos :: sup) ((a + 1) :: acc))

@[expose] def coverOK (m : ℕ) (K : List (List ℕ)) : Bool :=
  allCompsZ (fun c => !validCount c || K.contains (ckeyOfList c)) m 0 9 [] []

@[expose] def catOK {m : ℕ} (cat : List (Pair m)) (K : List (List ℕ)) (N : ℕ) : Bool :=
  (cat.length == N) && Nat.blt 2 N && isTranspositionPair (cat.getD 2 0) && (cat.map ckey == K)

end CFSG.KC.SUSmall

end
