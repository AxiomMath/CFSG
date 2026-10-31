
module

public import CFSG.LocalAnalysis.StandardType.GGReflExtFinal
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeA5AllDefs
public import Certificates.Data.CFSGNative.ReflExt.A5
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

namespace CFSG.ReflExt

open CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

def a5C : Matrix (Fin 5) (Fin 5) (ZMod 3) :=
  !![2, 2, 0, 0, 0; 2, 2, 2, 0, 0; 0, 2, 2, 2, 0; 0, 0, 2, 2, 2; 0, 0, 0, 2, 2]

def a5B : Matrix (Fin 5) (Fin 5) (ZMod 3) :=
  !![1, 2, 2, 2, 0; 2, 0, 1, 2, 2; 2, 1, 0, 1, 2; 2, 2, 1, 0, 2; 0, 2, 2, 2, 1]

def a5X : Fin 5 → ZMod 3 := ![1, 2, 0, 1, 2]

theorem a5_cart : ∀ i j : Fin 5, ((CartanMatrix.A 5 i j : ℤ) : ZMod 3) = a5C i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem a5_row : ∀ i j : Fin 5, (((a5Row i).getD j 0 : ℕ) : ZMod 3) = a5C i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem a5_xl : ∀ j : Fin 5, (([1, 2, 0, 1, 2].getD j 0 : ℕ) : ZMod 3) = a5X j := by decide +kernel

theorem a5_len : ∀ i, (a5Row i).length = 5 := by
  intro i
  simp [a5Row]

theorem a5_ker : ∀ y : Fin 5 → ZMod 3, a5C.mulVec y = 0 → ∃ c : ZMod 3, y = c • a5X := by
  decide +kernel

theorem a5_B : ∀ u : Fin 5 → ZMod 3, a5X ⬝ᵥ u = 0 → a5C.mulVec (a5B.mulVec u) = u := by
  decide +kernel

end CFSG.ReflExt

namespace CFSG.StandardType

open CFSG.ReflExt CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem lr6A5All_of_frames
    (hc5 : ∃ T, verifyAll (a5Frame 5) T = true) (hc6 : ∃ T, verifyAll (a5Frame 6) T = true) :
    LR6A5All := by
  intro p _ hp3 V _ _ _ hdim h α x r hF hr A hrA hgen hnt hcard hmov
  subst hp3
  obtain ⟨t, htA, htr, htm⟩ := hmov
  have hcard' : Nat.card A ≤ 6298560 :=
    le_trans hcard (le_of_eq (by decide +kernel))
  exact frame_classification a5Row [1, 2, 0, 1, 2] 6298560 1 a5C a5X a5B (0 : Fin 5) rfl a5_row
    a5_len a5_xl rfl (by decide) a5_ker a5_B hc5 hc6 hdim h α x
    (fun i j => (hF.pair i j).trans (a5_cart i j)) hF.indep hF.x_ne hF.x_ker hF.x_mem
    (Or.inl hF.fix) r hr A hrA hgen hnt hcard' t htA htr htm

end CFSG.StandardType

end
