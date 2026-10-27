module

public import CFSG.Sporadic.Th.Max3.Data

@[expose] public section

namespace CFSG.Sporadic.Th.Max3.Rank

open CFSG.Sporadic.Th.Native

def rkTup (a b c d : Fin 9) : Fin 9 → Fin 9 :=
  ![a, aPerm a, b, aPerm b, c, aPerm c, d, aPerm d, 8]

def RkCand (f : Fin 9 → Fin 9) : Prop :=
  (∀ j, f (f j) = j) ∧ (∃ j, f j ≠ aPerm j) ∧ (Finset.univ.filter fun j => f j ≠ j).card = 8 ∧
    (Finset.univ.filter fun j => f (aPerm j) ≠ j).card = 8

instance (f : Fin 9 → Fin 9) : Decidable (RkCand f) := by
  unfold RkCand
  infer_instance

def rkWordStr : Fin 12 → String :=
  !["yyxyyyyyxyxyyxyxyxyyxyyyy", "xyyxyyxyyyyxyyxyyyyxyyyy", "yyxyyxyyyyxyyxyyyyxyyyy",
    "xyyxyyyyyxyxyyxyxyxyyxyyyy", "xyyyxyyyxyyyyxyyxyyyxyyy", "yxyyyyxyxyyxyyyxyxyxyy",
    "xyxyyyyxyxyyxyyyxyxyxyy", "yyyxyyyxyyyyxyyxyyyxyyy", "yyyyyxyyyxyyyxyyyxy",
    "yxyyyxyxyyyyyxyyyxyyxyxyyxyy", "xyxyyyxyxyyyyyxyyyxyyxyxyyxyy", "xyyyyyxyyyxyyyxyyyxy"]

def rkWord (i : Fin 12) : List Gen := InvRep.wordOfString (rkWordStr i)

def rkPerm (i : Fin 12) : Equiv.Perm (Fin 9) := ((rkWord i).map (Gen.eval aPerm bPerm)).prod

def rkK0 : Fin 12 → Fin 512 := ![76, 0, 0, 76, 40, 102, 96, 40, 74, 68, 68, 74]

def rkTypeB : Fin 12 → Bool :=
  ![false, true, true, false, false, true, true, false, false, true, true, false]

def rkRows (i : Fin 12) : Array V4 :=
  mulRows (rowsNfAt (rkK0 i)) (wordRows rowsX rowsY (rkWord i))

def commList (C : List (Fin 512)) (R : Array V4) : List (Fin 512) :=
  C.filter fun k => eqRows (mulRows (rowsNfAt k) R) (mulRows R (rowsNfAt k))

def cqxList (_ : Unit := ()) : List (Fin 512) := commList (List.finRange 512) rowsX

structure RkData where
  C : List (Fin 512)
  R : Array (Array V4)
  D : Array (List (Fin 512))

def rkData (_ : Unit := ()) : RkData :=
  let C := cqxList ()
  let R := Array.ofFn rkRows
  ⟨C, R, R.map (commList C)⟩

def RkFacts (d : RkData) : Prop :=
  d.C.length = 16 ∧
    (∀ k ∈ d.C, ∀ l ∈ d.C,
      eqRows (mulRows (rowsNfAt k) (rowsNfAt l)) (mulRows (rowsNfAt l) (rowsNfAt k)) = true) ∧
    (∀ i : Fin 12, eqRows (mulRows d.R[i.val]! rowsX) (mulRows rowsX d.R[i.val]!) = true) ∧
    (∀ i : Fin 12, d.D[i.val]!.length ≤ 8) ∧
    (∀ i : Fin 12, rkTypeB i = false → ∀ k ∈ d.C,
      eqRows (powRows (mulRows (rowsNfAt k) d.R[i.val]!) 2) idRows = false) ∧
    (∀ i j : Fin 12, rkTypeB i = true → rkTypeB j = true →
      rkPerm i * rkPerm j = rkPerm j * rkPerm i → rkPerm j ≠ rkPerm i →
      rkPerm j ≠ rkPerm i * aPerm →
      (d.D[i.val]!.filter fun k => decide (k ∈ d.D[j.val]!)).length ≤ 4)

instance (d : RkData) : Decidable (RkFacts d) := by
  unfold RkFacts
  refine @instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_
    (@instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ ?_)))) <;> infer_instance

end CFSG.Sporadic.Th.Max3.Rank
