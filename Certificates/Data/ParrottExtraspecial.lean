module

public import CFSG.RankThree.GF2n.Parrott.HeisenbergModel
public import Certificates.Data.ParrottSpin
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.LocalAnalysis.RankThreeUC.Notation
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

open scoped Matrix BigOperators

namespace CFSG.RankThree.GF2n.Parrott

@[expose] def Ms1H : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 0, 0, 0, 1, 0, 1, 1;
     1, 0, 1, 0, 0, 0, 0, 0;
     1, 1, 1, 0, 1, 0, 1, 1;
     0, 0, 0, 0, 0, 0, 0, 1;
     0, 1, 1, 0, 1, 1, 1, 0;
     1, 1, 1, 0, 1, 1, 0, 0;
     1, 0, 1, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 0, 1, 1]

@[expose] def Ms1HInv : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 1, 1, 1, 1, 0, 1, 0;
     1, 1, 1, 0, 0, 0, 0, 0;
     1, 0, 1, 1, 1, 0, 1, 0;
     0, 0, 1, 1, 1, 0, 1, 1;
     0, 1, 1, 0, 0, 1, 1, 0;
     1, 1, 0, 0, 0, 0, 1, 0;
     1, 1, 1, 1, 0, 1, 1, 0;
     0, 0, 0, 1, 0, 0, 0, 0]

@[expose] def Ms2H : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 1, 1, 1, 1, 0, 1, 1;
     1, 0, 1, 0, 0, 0, 0, 0;
     1, 0, 0, 1, 1, 0, 1, 1;
     0, 1, 1, 0, 0, 0, 0, 1;
     0, 1, 1, 0, 1, 1, 1, 0;
     1, 0, 0, 1, 1, 1, 0, 1;
     1, 0, 1, 0, 1, 1, 1, 0;
     0, 1, 1, 1, 0, 0, 0, 0]

@[expose] def Ms2HInv : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 1, 1, 0, 1, 0, 1, 0;
     1, 1, 1, 0, 0, 0, 0, 0;
     1, 0, 1, 0, 1, 0, 1, 0;
     0, 1, 0, 0, 1, 0, 1, 1;
     0, 1, 1, 0, 0, 1, 1, 0;
     1, 0, 0, 1, 1, 0, 0, 1;
     1, 0, 1, 1, 1, 1, 0, 1;
     0, 1, 0, 1, 1, 0, 1, 0]

@[expose] def Ms1s2H : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 1, 1, 0, 0, 0, 0;
     1, 1, 1, 0, 0, 0, 0, 0;
     1, 1, 1, 1, 0, 0, 0, 0;
     0, 1, 1, 1, 0, 0, 0, 0;
     0, 1, 1, 0, 0, 1, 1, 0;
     1, 0, 1, 1, 0, 0, 1, 1;
     1, 1, 0, 0, 1, 1, 0, 1;
     0, 1, 0, 0, 1, 0, 1, 0]

@[expose] def Ms1s2HInv : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 0, 1, 1, 0, 0, 0, 0;
     1, 0, 1, 0, 0, 0, 0, 0;
     1, 1, 0, 1, 0, 0, 0, 0;
     0, 1, 1, 0, 0, 0, 0, 0;
     0, 1, 1, 0, 1, 1, 1, 0;
     1, 0, 1, 1, 0, 1, 1, 1;
     1, 1, 0, 0, 1, 1, 1, 1;
     0, 1, 0, 0, 1, 0, 1, 1]

@[expose] def Ms1s2invH : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 1;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 1;
     0, 1, 0, 1, 1, 0, 1, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 1, 0, 1, 1, 1, 1, 1;
     0, 1, 0, 1, 1, 0, 0, 0;
     0, 1, 1, 0, 0, 0, 0, 0]

@[expose] def Ms1s2invHInv : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 1, 1, 0, 0, 0, 0, 1;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 1;
     0, 1, 0, 0, 1, 0, 1, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 1, 1, 1, 0, 1, 0, 1;
     0, 0, 0, 1, 0, 0, 1, 0;
     0, 1, 1, 0, 0, 0, 0, 1]

@[expose] def cMs1 : List Nat :=
  [0x01, 0x03, 0x06, 0x11, 0x12, 0x41, 0x42, 0x81, 0x82, 0x84, 0x88, 0x90, 0xc0]

@[expose] def cMs2 : List Nat :=
  [0x05, 0x08, 0x09, 0x0a, 0x11, 0x12, 0x41, 0x42, 0x81, 0x84, 0x88]

@[expose] def cMs1s2 : List Nat := [0x06, 0x09, 0x0a, 0x0c]

@[expose] def cMs1s2inv : List Nat :=
  [0x02, 0x06, 0x0a, 0x0c, 0x12, 0x14, 0x42, 0x44, 0x82, 0x88]

@[expose] def monomial (m v : Nat) : Nat := if m &&& v = m then 1 else 0

@[expose] def cMask (ms : List Nat) (v : Nat) : Nat := (ms.map (fun m => monomial m v)).sum % 2

@[expose] def bhMask (p q : Nat) : Nat :=
  (((p >>> 0) % 2) * ((q >>> 4) % 2) + ((p >>> 1) % 2) * ((q >>> 5) % 2) +
    ((p >>> 2) % 2) * ((q >>> 6) % 2) + ((p >>> 3) % 2) * ((q >>> 7) % 2)) % 2

@[expose] def mulMask (p q : Nat) : Nat :=
  ((p % 256) ^^^ (q % 256)) |||
    ((((p >>> 8) % 2) ^^^ ((q >>> 8) % 2) ^^^ bhMask (p % 256) (q % 256)) <<< 8)

@[expose] def phiMask (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (ms : List Nat) (p : Nat) : Nat :=
  bitRow M (p % 256) ||| ((((p >>> 8) % 2) ^^^ cMask ms (p % 256)) <<< 8)

@[expose] def packX (i : Fin 4) : Fin 8 := ⟨i.val, by omega⟩

@[expose] def packY (i : Fin 4) : Fin 8 := ⟨4 + i.val, by omega⟩

@[expose] def packE8 (e : E8) : Fin 8 → ZMod 2 := fun i =>
  if h : i.val < 4 then e.x ⟨i.val, h⟩ else e.y ⟨i.val - 4, by omega⟩

theorem packE8_x (e : E8) (i : Fin 4) : packE8 e (packX i) = e.x i := by
  simp only [packE8, packX, i.isLt, ↓reduceDIte]

theorem packE8_y (e : E8) (i : Fin 4) : packE8 e (packY i) = e.y i := by
  have h : ¬ 4 + i.val < 4 := by omega
  simp only [packE8, packY, h, ↓reduceDIte]
  congr 1
  apply Fin.ext
  show 4 + i.val - 4 = i.val
  omega

end CFSG.RankThree.GF2n.Parrott
