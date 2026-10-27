module

public import CFSG.RankThree.PartOne.KF4.MinNative
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {n : ℕ} {J : Set (Fin τ.rank)} {w : Fin n → Fin τ.rank → ℤ}
  {K L : Type} [Field K] [Field L]

theorem baseChangeGL_mem_subsystemGroup (f : K →+* L) {g : ModGL τ K}
    (hg : g ∈ subsystemGroup τ K J) : baseChangeGL f g ∈ subsystemGroup τ L J := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rw [baseChangeGL_xUnit]
      exact xUnit_mem_subsystemGroup hi _
    · rw [baseChangeGL_yUnit]
      exact yUnit_mem_subsystemGroup hi _
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

namespace MinNativeData

variable (D : MinNativeData τ n J w)

theorem Mat_baseChangeGL (f : K →+* L) (g : ModGL τ K) :
    D.Mat (baseChangeGL f g) = (D.Mat g).map f := by
  ext a c
  rw [Mat, Matrix.of_apply, Matrix.map_apply, Mat, Matrix.of_apply]
  have h1 : D.vec L c = Finsupp.single (D.label c) 1 := rfl
  have h2 : D.vec K c = Finsupp.single (D.label c) 1 := rfl
  rw [h1, baseChangeGL_apply_single, Finsupp.mapRange_apply, h2]

end MinNativeData

end CFSG.RankThree.PartOne.KF4
