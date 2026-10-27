module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.ASVolI

open Matrix

variable {F : Type} [Field F]

@[expose] def burnsideC48_row (f : (Fin 3 → F) →ₗ[F] F) : Fin 3 → F :=
  fun i => f fun j => if i = j then 1 else 0

theorem burnsideC48_row_dotProduct (f : (Fin 3 → F) →ₗ[F] F) (z : Fin 3 → F) :
    burnsideC48_row f ⬝ᵥ z = f z := by
  rw [LinearMap.pi_apply_eq_sum_univ f z, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, mul_comm]
  rfl

@[expose] def burnsideC48_tvMat (f : (Fin 3 → F) →ₗ[F] F) (w : Fin 3 → F) :
    Matrix (Fin 3) (Fin 3) F :=
  1 + replicateCol (Fin 1) w * replicateRow (Fin 1) (burnsideC48_row f)

theorem burnsideC48_tvMat_mulVec (f : (Fin 3 → F) →ₗ[F] F) (w z : Fin 3 → F) :
    (burnsideC48_tvMat f w).mulVec z = z + f z • w := by
  unfold burnsideC48_tvMat
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
    replicateRow_mulVec_eq_const, burnsideC48_row_dotProduct]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct, replicateCol, mul_comm]

theorem burnsideC48_tvMat_det (f : (Fin 3 → F) →ₗ[F] F) (w : Fin 3 → F) (h : f w = 0) :
    (burnsideC48_tvMat f w).det = 1 := by
  unfold burnsideC48_tvMat
  have e := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) w (burnsideC48_row f)
  rw [burnsideC48_row_dotProduct, h, add_zero] at e
  exact e

@[expose] noncomputable def burnsideC48_tvSL (f : (Fin 3 → F) →ₗ[F] F) (w : Fin 3 → F)
    (h : f w = 0) : ↥(CFSG.Open.StatedSL 3 F) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (burnsideC48_tvMat f w)
      (by rw [burnsideC48_tvMat_det f w h]; exact one_ne_zero),
    Subgroup.subset_closure (by
      show (burnsideC48_tvMat f w).det = 1
      exact burnsideC48_tvMat_det f w h)⟩

theorem burnsideC48_tvSL_coe (f : (Fin 3 → F) →ₗ[F] F) (w : Fin 3 → F) (h : f w = 0) :
    (((burnsideC48_tvSL f w h : ↥(CFSG.Open.StatedSL 3 F)) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = burnsideC48_tvMat f w := rfl

theorem burnsideC48_tvSL_mulVec (f : (Fin 3 → F) →ₗ[F] F) (w : Fin 3 → F) (h : f w = 0)
    (z : Fin 3 → F) :
    (((burnsideC48_tvSL f w h : ↥(CFSG.Open.StatedSL 3 F)) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).mulVec z = z + f z • w := by
  rw [burnsideC48_tvSL_coe, burnsideC48_tvMat_mulVec]

theorem burnsideC48_eq_top_of_invariant {S : AddSubgroup (Fin 3 → F)}
    (hS : ∀ g : ↥(CFSG.Open.StatedSL 3 F), ∀ x ∈ S,
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x ∈ S)
    {x : Fin 3 → F} (hx : x ∈ S) (hx0 : x ≠ 0) : S = ⊤ := by
  have key : ∀ (f : (Fin 3 → F) →ₗ[F] F) (w y : Fin 3 → F), f w = 0 → y ∈ S → f y • w ∈ S := by
    intro f w y hfw hy
    have h1 := hS (burnsideC48_tvSL f w hfw) y hy
    rw [burnsideC48_tvSL_mulVec] at h1
    simpa using S.sub_mem h1 hy
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx0 (funext hcon)
  have hother : ∀ i, i ≠ j → ∀ c : F, (Pi.single i c : Fin 3 → F) ∈ S := by
    intro i hij c
    have h1 := key (LinearMap.proj j) (Pi.single i ((x j)⁻¹ * c)) x
      (by simp [Pi.single_apply, Ne.symm hij]) hx
    have e : (LinearMap.proj j : (Fin 3 → F) →ₗ[F] F) x • (Pi.single i ((x j)⁻¹ * c) : Fin 3 → F) =
        Pi.single i c := by
      rw [LinearMap.proj_apply, ← Pi.single_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hj,
        one_mul]
    rwa [e] at h1
  have hall : ∀ i (c : F), (Pi.single i c : Fin 3 → F) ∈ S := by
    intro i c
    by_cases hij : i = j
    · subst hij
      obtain ⟨k, hki⟩ : ∃ k : Fin 3, k ≠ i := by
        fin_cases i
        exacts [⟨1, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]
      have h1 := key (LinearMap.proj k) (Pi.single i c) (Pi.single k 1)
        (by simp [Pi.single_apply, Ne.symm hki]) (hother k hki 1)
      simpa using h1
    · exact hother i hij c
  refine eq_top_iff.mpr fun z _ => ?_
  rw [← Finset.univ_sum_single z]
  exact AddSubgroup.sum_mem S fun i _ => hall i (z i)

end CFSG.ASVolI
