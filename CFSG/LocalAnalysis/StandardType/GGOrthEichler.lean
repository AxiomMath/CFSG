module

public import CFSG.LocalAnalysis.StandardType.GGOrthEichlerPlane
public import CFSG.LocalAnalysis.StandardType.GGQ2EichlerDefs
public import CFSG.LocalAnalysis.StandardType.GGWAutDefs
public import CFSG.LocalAnalysis.StandardType.GGWAutOrthCosets

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin
open CFSG.ClassicalGroups.Orthogonal QuadraticMap

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggOrthE_isIsom_mul {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) {g h : V ≃ₗ[ZMod 3] V}
    (hg : ZS.IsIsom 3 Q g) (hh : ZS.IsIsom 3 Q h) : ZS.IsIsom 3 Q (g * h) := by
  intro v
  rw [LinearEquiv.mul_apply, hg, hh]

private lemma ggOrthE_isIsom_inv {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) {g : V ≃ₗ[ZMod 3] V} (hg : ZS.IsIsom 3 Q g) :
    ZS.IsIsom 3 Q g⁻¹ := by
  intro v
  simpa [LinearEquiv.apply_symm_apply] using (hg (g⁻¹ v)).symm

private lemma ggOrthE_conj_mem_ggOmega {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) {k c : V ≃ₗ[ZMod 3] V}
    (hk : ZS.IsIsom 3 Q k) (hc : c ∈ ggOmega Q) : k * c * k⁻¹ ∈ ggOmega Q := by
  have hle : ggOmega Q ≤ (ggOmega Q).comap (MulAut.conj k).toMonoidHom := by
    rw [ggOmega, Subgroup.closure_le]
    rintro x ⟨g, h, hg, hh, rfl⟩
    refine Subgroup.mem_comap.mpr ?_
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Subgroup.subset_closure
      ⟨k * g * k⁻¹, k * h * k⁻¹,
        ggOrthE_isIsom_mul Q (ggOrthE_isIsom_mul Q hk hg) (ggOrthE_isIsom_inv Q hk),
        ggOrthE_isIsom_mul Q (ggOrthE_isIsom_mul Q hk hh) (ggOrthE_isIsom_inv Q hk),
        by group⟩
  exact hle hc

private lemma ggOrthE_refl_mul_self {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {t : V ≃ₗ[ZMod 3] V} (ht : IsReflLin t) : t * t = 1 := by
  obtain ⟨c, φ, hφ, rfl⟩ := ht
  exact LinearEquiv.ext fun v => involutive_reflection hφ v

theorem ggOrth_eichler_exists {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Module.Finite (ZMod 3) V] (hdim : 6 ≤ Module.finrank (ZMod 3) V)
    (Q : QuadraticForm (ZMod 3) V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {x : V} (hx : x ≠ 0) :
    ∃ g : V ≃ₗ[ZMod 3] V, g ∈ ggOmega Q ∧ g x = x ∧ GGEichler g := by
  have _ := hx
  obtain ⟨u, w, hind, hu, hw, huw, hxu, hxw⟩ := ggOrth_totallySingularPlane hdim Q x
  have hu_ne : u ≠ 0 := by simpa using hind.ne_zero 0
  let g : V ≃ₗ[ZMod 3] V := eichler Q u w
  have hg_iso : ZS.IsIsom 3 Q g :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (eichler_mem_orthogonalGroup Q u w)
  have hgx : g x = x := eichler_apply_of_polar_eq_zero hxu hxw
  have hg_rel : ∀ v : V, g (g v) + g v + v = 0 := by
    intro v
    have hgv : g v = v + polar Q v u • w - polar Q v w • u := by
      rw [eichler_apply hu huw v, hw, zero_mul, add_zero]
    have hgu : polar Q (g v) u = polar Q v u := by
      rw [hgv, polar_sub_left, polar_add_left, polar_smul_left, polar_smul_left]
      simp only [polar_comm Q w u, huw, polar_self, hu, smul_zero, sub_zero, add_zero]
    have hgw : polar Q (g v) w = polar Q v w := by
      rw [hgv, polar_sub_left, polar_add_left, polar_smul_left, polar_smul_left]
      simp only [polar_self, hw, huw, smul_zero, sub_zero, add_zero]
    have hgg : g (g v) = g v + polar Q v u • w - polar Q v w • u := by
      rw [eichler_apply hu huw (g v), hw, zero_mul, add_zero, hgu, hgw]
    rw [hgg, hgv]
    have h3 : (3 : ℕ) • (v + polar Q v u • w - polar Q v w • u) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod 3) 3 _, CharP.cast_eq_zero (ZMod 3) 3, zero_smul]
    have hgoal : ((v + polar Q v u • w - polar Q v w • u) + polar Q v u • w -
        polar Q v w • u) + (v + polar Q v u • w - polar Q v w • u) + v =
        3 • (v + polar Q v u • w - polar Q v w • u) := by
      module
    rw [hgoal]
    exact h3
  have hg3 : g ^ 3 = 1 := by
    ext v
    have hv2 : g (g v) + g v + v = 0 := hg_rel v
    have hv : g (g (g v)) + g (g v) + g v = 0 := hg_rel (g v)
    have h1 : g (g v) + g v = -v := eq_neg_iff_add_eq_zero.mpr hv2
    have h2 : g (g (g v)) + (g (g v) + g v) = 0 := by rw [← add_assoc]; exact hv
    rw [h1] at h2
    have h3 : g (g (g v)) = v := add_neg_eq_zero.mp h2
    rw [show g ^ 3 = (g * g) * g by rw [pow_succ, pow_two]]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    simpa using h3
  have hg_mem : g ∈ ggOmega Q := by
    have hgg_mem : g * g ∈ ggOmega Q := by
      obtain ⟨t₁, t₂, ⟨ht1r, ht1i⟩, ⟨ht2r, ht2i⟩, hcover⟩ :=
        ggWAut_orth_cosets Q hQ (by omega)
      obtain ⟨ω, hω, hcase⟩ := hcover g hg_iso
      rcases hcase with h | h | h | h
      · rw [h]; exact mul_mem hω hω
      · have hsq : t₁ * t₁ = 1 := ggOrthE_refl_mul_self ht1r
        have ht1inv : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_right hsq
        have heq : g * g = ω * (t₁ * ω * t₁⁻¹) := by rw [h, ht1inv]; simp only [mul_assoc]
        rw [heq]
        exact mul_mem hω (ggOrthE_conj_mem_ggOmega Q ht1i hω)
      · have hsq : t₂ * t₂ = 1 := ggOrthE_refl_mul_self ht2r
        have ht2inv : t₂⁻¹ = t₂ := inv_eq_of_mul_eq_one_right hsq
        have heq : g * g = ω * (t₂ * ω * t₂⁻¹) := by rw [h, ht2inv]; simp only [mul_assoc]
        rw [heq]
        exact mul_mem hω (ggOrthE_conj_mem_ggOmega Q ht2i hω)
      · have hsq1 : t₁ * t₁ = 1 := ggOrthE_refl_mul_self ht1r
        have hsq2 : t₂ * t₂ = 1 := ggOrthE_refl_mul_self ht2r
        have ht1inv : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_right hsq1
        have ht2inv : t₂⁻¹ = t₂ := inv_eq_of_mul_eq_one_right hsq2
        have h12 : ZS.IsIsom 3 Q (t₁ * t₂) := ggOrthE_isIsom_mul Q ht1i ht2i
        have hcomm : t₁ * t₂ * t₁⁻¹ * t₂⁻¹ ∈ ggOmega Q :=
          Subgroup.subset_closure ⟨t₁, t₂, ht1i, ht2i, rfl⟩
        have hsq : (t₁ * t₂) * (t₁ * t₂) = t₁ * t₂ * t₁⁻¹ * t₂⁻¹ := by
          rw [ht1inv, ht2inv]; simp only [mul_assoc]
        have heq : g * g =
            ω * ((t₁ * t₂) * ω * (t₁ * t₂)⁻¹) * ((t₁ * t₂) * (t₁ * t₂)) := by
          rw [h]; group
        rw [heq, hsq]
        exact mul_mem (mul_mem hω (ggOrthE_conj_mem_ggOmega Q h12 hω)) hcomm
    have h4 : (g * g) * (g * g) = g ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_two, pow_two]
    have hg4 : g ^ 4 = g := by
      rw [show g ^ 4 = g ^ 3 * g by rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ],
        hg3, one_mul]
    have heq : g = (g * g) * (g * g) := by rw [h4, hg4]
    rw [heq]
    exact mul_mem hgg_mem hgg_mem
  have hne : g ≠ 1 := by
    have hker : LinearMap.ker (QuadraticMap.polarBilin Q) = ⊥ :=
      LinearMap.BilinForm.Nondegenerate.ker_eq_bot hQ
    have hBu_ne : QuadraticMap.polarBilin Q u ≠ 0 := by
      intro h0
      have : u ∈ LinearMap.ker (QuadraticMap.polarBilin Q) := LinearMap.mem_ker.mpr h0
      rw [hker, Submodule.mem_bot] at this
      exact hu_ne this
    obtain ⟨v, hv⟩ : ∃ v, polar Q v u ≠ 0 := by
      by_contra h
      exact hBu_ne (by
        ext w
        rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
        exact not_not.mp (not_exists.mp h w))
    intro hg1
    have hgv_exp : g v = v + polar Q v u • w - polar Q v w • u := by
      rw [eichler_apply hu huw v, hw, zero_mul, add_zero]
    have hgv_eq : g v = v := by rw [hg1]; rfl
    have hzero : polar Q v u • w - polar Q v w • u = 0 := by
      have h : v + (polar Q v u • w - polar Q v w • u) = v + 0 := by
        rw [add_zero, ← add_sub_assoc]
        exact hgv_exp.symm.trans hgv_eq
      exact add_left_cancel h
    have hsum : (polar Q v w) • u + (-(polar Q v u)) • w = 0 := by
      rw [neg_smul, ← sub_eq_add_neg, sub_eq_zero]
      exact (sub_eq_zero.mp hzero).symm
    have hcoef := (LinearIndependent.pair_iff.mp hind) (polar Q v w) (-(polar Q v u)) hsum
    exact hv (neg_eq_zero.mp hcoef.2)
  exact ⟨g, hg_mem, hgx, hne, hg_rel⟩

end CFSG.StandardType

end
