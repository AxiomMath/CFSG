module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RepresentationTheory.Invariants

public section

namespace CFSG.StandardType.GGStepTwoToralLemmaI

section IndexLemma

variable {F : Type*} [Field F] {Y W : Type*} [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y]
  [AddCommGroup W] [Module F W]

omit [FiniteDimensional F Y] in
theorem eigenspace_eq_sup_inf (M : Module.End F Y) (lam : F) {U U' : Submodule F Y}
    (hc : IsCompl U U') (hU : ∀ y ∈ U, M y ∈ U) (hU' : ∀ y ∈ U', M y ∈ U') :
    Module.End.eigenspace M lam = (Module.End.eigenspace M lam ⊓ U) ⊔
      (Module.End.eigenspace M lam ⊓ U') := by
  refine le_antisymm (fun v hv => ?_) (sup_le inf_le_left inf_le_left)
  obtain ⟨u, hu, u', hu', rfl⟩ :=
    Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
  have h1 : M u - lam • u ∈ U := U.sub_mem (hU u hu) (U.smul_mem lam hu)
  have h2 : M u' - lam • u' ∈ U' := U'.sub_mem (hU' u' hu') (U'.smul_mem lam hu')
  rw [Module.End.mem_eigenspace_iff, map_add, smul_add] at hv
  have h3 : M u - lam • u = -(M u' - lam • u') := by
    rw [eq_neg_iff_add_eq_zero, ← sub_eq_zero.mpr hv]
    abel
  have h4 : M u - lam • u = 0 := by
    have : M u - lam • u ∈ U ⊓ U' := ⟨h1, h3 ▸ U'.neg_mem h2⟩
    rwa [hc.inf_eq_bot, Submodule.mem_bot] at this
  have h5 : M u' - lam • u' = 0 := by
    rw [h4, eq_comm, neg_eq_zero] at h3
    exact h3
  exact Submodule.add_mem_sup ⟨Module.End.mem_eigenspace_iff.mpr (sub_eq_zero.mp h4), hu⟩
    ⟨Module.End.mem_eigenspace_iff.mpr (sub_eq_zero.mp h5), hu'⟩

theorem inf_ne_bot_of_finrank {V D S : Submodule F Y} (hD : D ≤ V) (hS : S ≤ V)
    (h : Module.finrank F ↥V < Module.finrank F ↥D + Module.finrank F ↥S) : D ⊓ S ≠ ⊥ := by
  intro hbot
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq D S
  rw [hbot, finrank_bot, add_zero] at h1
  have h2 : Module.finrank F ↥(D ⊔ S) ≤ Module.finrank F ↥V :=
    Submodule.finrank_mono (sup_le hD hS)
  omega

end IndexLemma

section CoprimeSaturation

theorem mem_of_smul_mem_of_coprime {M H : Type*} [AddCommGroup M] [NoZeroSMulDivisors ℤ M]
    [Group H] [Fintype H] [DistribMulAction H M] (Λ : AddSubgroup M)
    (hsub : ∀ (h : H) (y : M), y - h • y ∈ Λ) (hsum : ∀ x ∈ Λ, ∑ h : H, h • x = 0)
    {p : ℕ} (hp : p.Prime) (hH : ¬ p ∣ Fintype.card H) {y : M} (hy : (p : ℤ) • y ∈ Λ) : y ∈ Λ := by
  have hN : ∑ h : H, h • y = 0 := by
    have h0 := hsum _ hy
    simp only [smul_comm _ (p : ℤ)] at h0
    rw [← Finset.smul_sum] at h0
    exact (smul_eq_zero.mp h0).resolve_left (by exact_mod_cast hp.ne_zero)
  have hcard : (Fintype.card H : ℤ) • y ∈ Λ := by
    have : (Fintype.card H : ℤ) • y = ∑ h : H, (y - h • y) := by
      rw [Finset.sum_sub_distrib, hN, sub_zero, Finset.sum_const, Finset.card_univ, natCast_zsmul]
    rw [this]
    exact Λ.sum_mem fun h _ => hsub h y
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hH)
  have : y = a • ((p : ℤ) • y) + b • ((Fintype.card H : ℤ) • y) := by
    rw [smul_smul, smul_smul, ← add_smul, hab, one_smul]
  rw [this]
  exact Λ.add_mem (Λ.zsmul_mem hy a) (Λ.zsmul_mem hcard b)

end CoprimeSaturation

section CoprimeDecomposition

theorem isCompl_span_sub_invariants {F V H : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Group H] [Fintype H] (ρ : Representation F H V) (hH : (Fintype.card H : F) ≠ 0) :
    IsCompl (Submodule.span F {v | ∃ (h : H) (u : V), v = u - ρ h u}) ρ.invariants := by
  have hN : ∀ v, Representation.norm ρ v = ∑ g, ρ g v := fun v => by
    simp [Representation.norm]
  have hinv : ∀ v ∈ ρ.invariants, Representation.norm ρ v = (Fintype.card H : F) • v := by
    intro v hv
    rw [hN, Finset.sum_congr rfl fun g _ => (Representation.mem_invariants ρ v).mp hv g,
      Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hspan : ∀ v ∈ Submodule.span F {v | ∃ (h : H) (u : V), v = u - ρ h u},
      Representation.norm ρ v = 0 := by
    intro v hv
    refine Submodule.span_induction (p := fun v _ => Representation.norm ρ v = 0) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨h, u, rfl⟩
      simp
    · simp
    · intro x y _ _ hx hy
      simp [hx, hy]
    · intro a x _ hx
      simp [hx]
  refine IsCompl.of_eq (eq_bot_iff.mpr fun v hv => ?_) (eq_top_iff.mpr fun v _ => ?_)
  · have h1 := hinv v hv.2
    rw [hspan v hv.1] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_left hH
  · have hv : v = (v - (Fintype.card H : F)⁻¹ • Representation.norm ρ v) +
        (Fintype.card H : F)⁻¹ • Representation.norm ρ v := by abel
    rw [hv]
    refine Submodule.add_mem_sup ?_ ?_
    · have : v - (Fintype.card H : F)⁻¹ • Representation.norm ρ v =
          (Fintype.card H : F)⁻¹ • ∑ g : H, (v - ρ g v) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← hN, smul_sub,
          ← Nat.cast_smul_eq_nsmul F, smul_smul, inv_mul_cancel₀ hH, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ =>
        Submodule.subset_span ⟨g, v, rfl⟩)
    · refine (Representation.mem_invariants ρ _).mpr fun g => ?_
      rw [map_smul, Representation.self_norm_apply]

end CoprimeDecomposition

end CFSG.StandardType.GGStepTwoToralLemmaI
