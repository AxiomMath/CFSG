module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinear

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TableB

section ProjConj

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem scalars_le_center : LargeEvenScalars ι K ≤ Subgroup.center (GL ι K) := by
  rw [largeEvenScalars_def, ← Matrix.GeneralLinearGroup.center_eq_range_scalar]

theorem normalizerMonoidHom_scalar_eq (H : Subgroup (GL ι K))
    (A : Subgroup.normalizer (H : Set (GL ι K))) (z : H)
    (hz : z ∈ (LargeEvenScalars ι K).subgroupOf H) : H.normalizerMonoidHom A z = z := by
  have hc : ∀ g : GL ι K, g * (z : GL ι K) = z * g :=
    Subgroup.mem_center_iff.mp (scalars_le_center (Subgroup.mem_subgroupOf.mp hz))
  apply Subtype.ext
  show (A : GL ι K) * z * (A : GL ι K)⁻¹ = z
  rw [hc]
  group

@[expose] noncomputable def projConj (H : Subgroup (GL ι K)) :
    Subgroup.normalizer (H : Set (GL ι K)) →* MulAut (LargeEvenProj H) where
  toFun A := QuotientGroup.congr _ _ (H.normalizerMonoidHom A)
    (map_eq_self_of_forall_eq _ (normalizerMonoidHom_scalar_eq H A))
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    simp
  map_mul' A B := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H h =>
      show ((H.normalizerMonoidHom (A * B) h : H) : LargeEvenProj H) =
        ((H.normalizerMonoidHom A (H.normalizerMonoidHom B h) : H) : LargeEvenProj H)
      rw [map_mul, MulAut.mul_apply]

theorem projConj_mk (H : Subgroup (GL ι K)) (A : Subgroup.normalizer (H : Set (GL ι K))) (h : H) :
    projConj H A (h : LargeEvenProj H) =
      ((H.normalizerMonoidHom A h : H) : LargeEvenProj H) :=
  rfl

theorem projConj_of_mem (H : Subgroup (GL ι K)) (A : GL ι K) (hA : A ∈ H) :
    projConj H ⟨A, Subgroup.le_normalizer hA⟩ =
      MulAut.conj ((⟨A, hA⟩ : H) : LargeEvenProj H) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H h =>
    rw [projConj_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    rfl

theorem scalar_mem_normalizer (H : Subgroup (GL ι K)) {z : GL ι K}
    (hz : z ∈ LargeEvenScalars ι K) : z ∈ Subgroup.normalizer (H : Set (GL ι K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [← (Subgroup.mem_center_iff.mp (scalars_le_center hz)) h, mul_inv_cancel_right]

theorem projConj_of_scalar (H : Subgroup (GL ι K)) {z : GL ι K} (hz : z ∈ LargeEvenScalars ι K) :
    projConj H ⟨z, scalar_mem_normalizer H hz⟩ = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H h =>
    rw [projConj_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    show z * h * z⁻¹ = h
    rw [← (Subgroup.mem_center_iff.mp (scalars_le_center hz)) h, mul_inv_cancel_right]

theorem exists_eq_projConj {H : Subgroup (GL ι K)} {S : Set (GL ι K)}
    (hS : S ⊆ Subgroup.normalizer (H : Set (GL ι K))) {φ : MulAut (LargeEvenProj H)}
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk H) S) :
    ∃ (A : GL ι K) (hA : A ∈ S), φ = projConj H ⟨A, hS hA⟩ := by
  obtain ⟨A, hA, hrel⟩ := hφ
  refine ⟨A, hA, ?_⟩
  ext x
  induction x using QuotientGroup.induction_on with
  | H h => exact hrel h (H.normalizerMonoidHom ⟨A, hS hA⟩ h) rfl

theorem ggOutdiagCyclic_of_decomp {H : Subgroup (GL ι K)} {S : Set (GL ι K)}
    (hS : S ⊆ Subgroup.normalizer (H : Set (GL ι K)))
    (A₀ : Subgroup.normalizer (H : Set (GL ι K)))
    (hdec : ∀ A ∈ S, ∃ (h : GL ι K) (k : ℤ) (z : GL ι K), h ∈ H ∧ z ∈ LargeEvenScalars ι K ∧
      A = h * (A₀ : GL ι K) ^ k * z) :
    GGOutdiagCyclic (LargeEvenProj H) (LargeEvenMatConjImage (LargeEvenProjMk H) S) := by
  refine ⟨projConj H A₀, fun φ hφ => ?_⟩
  obtain ⟨A, hA, rfl⟩ := exists_eq_projConj hS hφ
  obtain ⟨h, k, z, hh, hz, hAeq⟩ := hdec A hA
  have hsplit : (⟨A, hS hA⟩ : Subgroup.normalizer (H : Set (GL ι K))) =
      ⟨h, Subgroup.le_normalizer hh⟩ * A₀ ^ k * ⟨z, scalar_mem_normalizer H hz⟩ := by
    apply Subtype.ext
    simp [hAeq]
  rw [hsplit, map_mul, map_mul, projConj_of_scalar H hz, mul_one, projConj_of_mem H h hh, map_zpow]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨_, rfl⟩)
    (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))

end ProjConj

end TableB

end CFSG.StandardType
