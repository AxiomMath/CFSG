module

public import CFSG.Monster.B.Dyadic.Max2K
public import Certificates.Data.CFSGNative.CTIB.Data
public import Certificates.Data.CFSGNative.CTIB.Lift
public import Certificates.Data.Kernel.BabyMonster.CTIB.CentWords

public section

namespace CFSG.Monster.B.Dyadic

open CFSG.Monster.B.CTIB.Native
open scoped Matrix

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

@[expose] noncomputable def prodK : List MatB → MatB
  | [] => 1
  | M :: l => M * prodK l

@[expose] noncomputable def qK (m : ℕ) : MatB :=
  (if m.testBit 22 then XK else 1) *
    prodK ((List.range 22).map fun j => if m.testBit j then EK j else 1)

@[expose] noncomputable def seedK : MatB :=
  prodK ([1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1].map fun l : ℕ => if l = 0 then G1K else G2K)

@[expose] noncomputable def hK (k : ℕ) : MatB :=
  if k = 6 then G2K ^ 12 else if k = 8 then G1K else if k = 10 then seedK ^ 10 else 1

@[expose] noncomputable def repK (i : ℕ) : MatB :=
  hK (repTable.getD i (0, 0)).1 * qK (repTable.getD i (0, 0)).2

@[expose] noncomputable def letterK (l : ℤ) : MatB :=
  if l = 1 ∨ l = -1 then G1K else if l = 2 then G2K else if l = -2 then Gi2K
  else if l = 3 then QnK 25 else QnK 25 * QnK 25

@[expose] noncomputable def wordK (w : List ℤ) : MatB := prodK (w.map letterK)

@[expose] def FactFourteen : Prop := ∀ i < 14, (repK i - 1).rank = repRanks.getD i 0

@[expose] def FactFusion : Prop :=
  ∀ f ∈ globalFusion, ∃ C : MatB, wordK f.2.2.2 * C = repK f.1 * wordK f.2.2.2 ∧
    (repK f.2.1 * C) ^ f.2.2.1 = 1

@[expose] def matRows (rows : List ℕ) : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  Matrix.of fun i j => if (rows.getD i 0).testBit j then 1 else 0

@[expose] def liftData (k : ℕ) : List ℕ × List ℕ × List ℕ :=
  if k = 6 then (liftWord6, liftImgs6, liftRows6)
  else if k = 8 then (liftWord8, liftImgs8, liftRows8) else (liftWord10, liftImgs10, liftRows10)

@[expose] def FactAct : Prop :=
  (∀ t < 22, CFSG.KC.BM.e0 ᵥ* (G1K * EK t * G1K) =
    CFSG.KC.BM.e0 ᵥ* qK (signedImg CFSG.Monster.B.Bin.quotRows1 3711077 t)) ∧
  (∀ t < 22, CFSG.KC.BM.e0 ᵥ* (Gi2K * EK t * G2K) =
    CFSG.KC.BM.e0 ᵥ* qK (signedImg CFSG.Monster.B.Bin.quotRows2 3015616 t)) ∧
  (∀ k, (k = 6 ∨ k = 8 ∨ k = 10) →
    (autWord gArr genImgs (liftData k).1).toList = (liftData k).2.1 ∧
    matRows (liftData k).2.2 * matRows (liftData k).2.2 = 1 ∧
    (matRows (liftData k).2.2 - 1).rank = k) ∧
  repK 12 * repK 12 = 1

@[expose] def redStep : List ℤ → ℤ → List ℤ
  | y :: r, x => if y = -x ∨ (x.natAbs = 1 ∧ y.natAbs = 1) then r else x :: y :: r
  | [], x => [x]

@[expose] def freeRed (w : List ℤ) : List ℤ := (w.foldl redStep []).reverse

@[expose] def invWordK (w : List ℤ) : List ℤ := (w.map (- ·)).reverse

@[expose] def rankOfT (t : ℕ) : ℕ := if t < 15 then 6 else if t < 30 then 8 else 10

@[expose] def liftWordZK (k : ℕ) : List ℤ := (liftData k).1.map fun l => (l : ℤ) + 1

@[expose] def deltaWord (t : ℕ) : List ℤ :=
  freeRed (invWordK (liftWordZK (rankOfT t)) ++ invWordK (centWordsL.getD t []) ++
    liftWordZK (rankOfT t) ++ centWordsL.getD t [])

@[expose] def FactDelta : Prop :=
  ∀ t < 45, CFSG.KC.BM.e0 ᵥ* wordK (deltaWord t) = CFSG.KC.BM.e0 ᵥ* qK (deltaVals.getD t 0)

@[expose] def caseBWordK : List ℤ := [3, -1, -2, -3, -3, 2, -3, -1, -3]

@[expose] def FactCaseB : Prop :=
  ∃ A C : MatB, wordK caseBWordK * A = repK 6 * wordK caseBWordK ∧
    wordK caseBWordK * C = qK 854 * wordK caseBWordK ∧
    (A * qK 1 * C * qK 1 * A * qK 4356) ^ 9 = 1

end CFSG.Monster.B.Dyadic

end
