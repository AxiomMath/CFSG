module

public import CFSG.LocalAnalysis.StandardType.SpEightCoordinates

public section

namespace CFSG.StandardType.SpEight

open Matrix CFSG.Open CFSG.Blueprint.EvenSource

@[expose] def frameMat (bas : Idx → Vec) : Matrix Idx Idx (ZMod 2) :=
  Matrix.of fun i j => bas j i

theorem frameMat_mulVec_expand (bas : Idx → Vec) (u : Vec) :
    frameMat bas *ᵥ u = ∑ i, u i • bas i := by
  ext k
  simp only [Matrix.mulVec, dotProduct, frameMat, Matrix.of_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem frameMat_single_eq_one :
    frameMat (fun i : Idx => Pi.single i 1) = (1 : Matrix Idx Idx (ZMod 2)) := by
  ext i j
  simp only [frameMat, Matrix.of_apply, Matrix.one_apply, Pi.single_apply, eq_comm]

theorem omega_sum_left {ι : Type*} (s : Finset ι) (f : ι → Vec) (v : Vec) :
    omega (∑ i ∈ s, f i) v = ∑ i ∈ s, omega (f i) v := by
  simp only [omega]
  exact sum_dotProduct s f (Jm *ᵥ v)

theorem omega_sum_right {ι : Type*} (u : Vec) (s : Finset ι) (g : ι → Vec) :
    omega u (∑ j ∈ s, g j) = ∑ j ∈ s, omega u (g j) := by
  simp only [omega]
  rw [mulVec_sum, dotProduct_sum]

theorem omega_smul_left (c : ZMod 2) (x y : Vec) : omega (c • x) y = c * omega x y := by
  simp only [omega, smul_dotProduct, smul_eq_mul]

theorem omega_smulVec_right (c : ZMod 2) (x y : Vec) : omega x (c • y) = c * omega x y := by
  simp only [omega, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem omega_frameMat_bilinear (f g : Idx → Vec) (u v : Vec) :
    omega (frameMat f *ᵥ u) (frameMat g *ᵥ v) =
      ∑ i, ∑ j, u i * v j * omega (f i) (g j) := by
  rw [frameMat_mulVec_expand, frameMat_mulVec_expand]
  rw [omega_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [omega_smul_left, omega_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [omega_smulVec_right]
  ring

theorem omega_single_single (i j : Idx) : omega (Pi.single i 1) (Pi.single j 1) = Jm i j := by
  rw [omega, Matrix.mulVec_single_one, single_one_dotProduct]
  rfl

theorem omega_eq_sum_sum (u v : Vec) :
    omega u v = ∑ i, ∑ j, u i * v j * Jm i j := by
  have h : omega u v = omega (frameMat (fun i : Idx => Pi.single i 1) *ᵥ u)
      (frameMat (fun i : Idx => Pi.single i 1) *ᵥ v) := by
    simp only [frameMat_single_eq_one, Matrix.one_mulVec]
  rw [h, omega_frameMat_bilinear]
  simp only [omega_single_single]

theorem frameMat_mulVec_single (bas : Idx → Vec) (j : Idx) :
    frameMat bas *ᵥ Pi.single j 1 = bas j := by
  rw [Matrix.mulVec_single_one]
  ext i
  rfl

theorem omega_frameMat_mulVec (bas : Idx → Vec) (hgram : ∀ i j, omega (bas i) (bas j) = Jm i j)
    (u v : Vec) : omega (frameMat bas *ᵥ u) (frameMat bas *ᵥ v) = omega u v := by
  rw [omega_frameMat_bilinear, omega_eq_sum_sum u v]
  simp only [hgram]

theorem exists_mem_statedSp_of_frame (bas : Idx → Vec)
    (hgram : ∀ i j, omega (bas i) (bas j) = Jm i j) :
    ∃ A : GL Idx (ZMod 2), (A : Matrix Idx Idx (ZMod 2)) = frameMat bas ∧
      A ∈ StatedSp 4 (ZMod 2) := by
  have hker : ∀ z : Vec, frameMat bas *ᵥ z = 0 → z = 0 := by
    intro z hz
    apply eq_zero_of_omega_eq_zero
    intro w
    calc omega z w = omega (frameMat bas *ᵥ z) (frameMat bas *ᵥ w) :=
          (omega_frameMat_mulVec bas hgram z w).symm
      _ = omega 0 (frameMat bas *ᵥ w) := by rw [hz]
      _ = 0 := by simp [omega]
  have hinj : Function.Injective (frameMat bas).mulVec := by
    intro u v huv
    have h : frameMat bas *ᵥ (u - v) = 0 := by
      rw [Matrix.mulVec_sub, huv, sub_self]
    exact sub_eq_zero.mp (hker (u - v) h)
  have hunit : IsUnit (frameMat bas) := (Matrix.mulVec_injective_iff_isUnit).1 hinj
  refine ⟨hunit.unit, hunit.unit_spec, ?_⟩
  rw [mem_statedSp_iff_omega, hunit.unit_spec]
  exact omega_frameMat_mulVec bas hgram

theorem mul_frameMat_eq (bas : Idx → Vec) (x y : Matrix Idx Idx (ZMod 2))
    (h : ∀ j, x *ᵥ bas j = ∑ i, y i j • bas i) :
    x * frameMat bas = frameMat bas * y := by
  apply Matrix.ext_of_mulVec_single
  intro j
  calc (x * frameMat bas) *ᵥ Pi.single j 1
      = x *ᵥ (frameMat bas *ᵥ Pi.single j 1) := by rw [Matrix.mulVec_mulVec]
    _ = x *ᵥ bas j := by rw [frameMat_mulVec_single]
    _ = ∑ i, y i j • bas i := h j
    _ = frameMat bas *ᵥ y.col j := (frameMat_mulVec_expand bas (y.col j)).symm
    _ = frameMat bas *ᵥ (y *ᵥ Pi.single j 1) := by rw [Matrix.mulVec_single_one]
    _ = (frameMat bas * y) *ᵥ Pi.single j 1 := by rw [Matrix.mulVec_mulVec]

theorem exists_conj_aStd_bStd_of_frame {a' b' : GL Idx (ZMod 2)} (bas : Idx → Vec)
    (hgram : ∀ i j, omega (bas i) (bas j) = Jm i j)
    (ha : ∀ j, (a' : Matrix Idx Idx (ZMod 2)) *ᵥ bas j = ∑ i, aStdM i j • bas i)
    (hb : ∀ j, (b' : Matrix Idx Idx (ZMod 2)) *ᵥ bas j = ∑ i, bStdM i j • bas i) :
    ∃ A : GL Idx (ZMod 2), A ∈ StatedSp 4 (ZMod 2) ∧ A⁻¹ * a' * A = aStd ∧
      A⁻¹ * b' * A = bStd := by
  obtain ⟨A, hAM, hASp⟩ := exists_mem_statedSp_of_frame bas hgram
  refine ⟨A, hASp, ?_, ?_⟩
  · have h : a' * A = A * aStd := Units.ext (by
      rw [Units.val_mul, Units.val_mul, hAM]
      exact mul_frameMat_eq bas _ _ ha)
    rw [mul_assoc, h, inv_mul_cancel_left]
  · have h : b' * A = A * bStd := Units.ext (by
      rw [Units.val_mul, Units.val_mul, hAM]
      exact mul_frameMat_eq bas _ _ hb)
    rw [mul_assoc, h, inv_mul_cancel_left]

end CFSG.StandardType.SpEight
