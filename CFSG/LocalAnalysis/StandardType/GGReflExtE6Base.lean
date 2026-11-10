
module

public import CFSG.LocalAnalysis.StandardType.GGReflExtFinal
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6AllDefs
public import Certificates.Data.CFSGNative.ReflExt.E6
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

namespace CFSG.ReflExt

open CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

def e6C : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![2, 0, 2, 0, 0, 0; 0, 2, 0, 2, 0, 0; 2, 0, 2, 2, 0, 0; 0, 2, 2, 2, 2, 0; 0, 0, 0, 2, 2, 2;
    0, 0, 0, 0, 2, 2]

def e6B : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![0, 1, 0, 2, 0, 2; 1, 2, 2, 0, 2, 1; 0, 2, 2, 1, 1, 0; 2, 0, 1, 0, 1, 2; 0, 2, 1, 1, 2, 0;
    2, 1, 0, 2, 0, 0]

def e6X : Fin 6 → ZMod 3 := ![1, 0, 2, 0, 1, 2]

theorem e6_cart : ∀ i j : Fin 6, ((CartanMatrix.E 6 i j : ℤ) : ZMod 3) = e6C i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem e6_row : ∀ i j : Fin 6, (((e6Row i).getD j 0 : ℕ) : ZMod 3) = e6C i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem e6_xl : ∀ j : Fin 6, (([1, 0, 2, 0, 1, 2].getD j 0 : ℕ) : ZMod 3) = e6X j := by decide +kernel

theorem e6_len : ∀ i, (e6Row i).length = 6 := by
  intro i
  simp [e6Row]

theorem e6_ker : ∀ y : Fin 6 → ZMod 3, e6C.mulVec y = 0 → ∃ c : ZMod 3, y = c • e6X := by
  decide +kernel

theorem e6_B : ∀ u : Fin 6 → ZMod 3, e6X ⬝ᵥ u = 0 → e6C.mulVec (e6B.mulVec u) = u := by
  decide +kernel

end CFSG.ReflExt

namespace CFSG.StandardType

open CFSG.ReflExt CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem lr6E6All_of_frames
    (hc6 : ∃ T, verifyAll (e6Frame 6 0) T = true) (hc71 : ∃ T, verifyAll (e6Frame 7 1) T = true)
    (hc70 : ∃ T, verifyAll (e6Frame 7 0) T = true) : LR6E6All := by
  intro p _ hp3 V _ _ _ hdim h α x r hF hr A hrA hgen hnt hcard hmov
  subst hp3
  obtain ⟨t, htA, htr, htm⟩ := hmov
  have hcard' : Nat.card A ≤ 1360488960 :=
    le_trans hcard (le_of_eq (by decide +kernel))
  exact frame_classification e6Row [1, 0, 2, 0, 1, 2] 1360488960 0 e6C e6X e6B (0 : Fin 6) rfl e6_row
    e6_len e6_xl rfl (by decide) e6_ker e6_B hc6 hc71 hdim h α x
    (fun i j => (hF.pair i j).trans (e6_cart i j)) hF.indep hF.x_ne hF.x_ker hF.x_mem
    (Or.inr hc70) r hr A hrA hgen hnt hcard' t htA htr htm

end CFSG.StandardType

end
