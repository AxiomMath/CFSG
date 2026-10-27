module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalCore

public section

namespace CFSG.StandardType.LieKnownR2.POmega.Radical

open CFSG.Open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin
open scoped commutatorElement

private theorem flag_eq_of_mem_siegelY {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') {y : V}
    (hy : y ∈ siegelY K P.e P'.e) :
    y = polar Q P.f y • P.e + polar Q P'.f y • P'.e := by
  obtain ⟨c₁, c₂, hc⟩ := Submodule.mem_span_pair.mp hy
  have h1 : polar Q P.f y = c₁ := by
    rw [← hc]
    simp only [polar_add_right, polar_smul_right_eq, P.polar_fe, h.fe, mul_one, mul_zero,
      add_zero]
  have h2 : polar Q P'.f y = c₂ := by
    rw [← hc]
    simp only [polar_add_right, polar_smul_right_eq, polar_comm Q P'.f P.e, h.ef, P'.polar_fe,
      mul_one, mul_zero, add_zero, zero_add]
  rw [h1, h2]
  exact hc.symm

private theorem flag_polar_eq_zero_of_mem_siegelY {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P')
    {x y : V} (hx : x ∈ siegelY K P.e P'.e) (hy : y ∈ siegelY K P.e P'.e) :
    polar Q x y = 0 := by
  obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨d₁, d₂, rfl⟩ := Submodule.mem_span_pair.mp hy
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq,
    P.polar_ee, P'.polar_ee, h.ee, polar_comm Q P'.e P.e]
  ring

private theorem flag_mul_eichler_apply {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') {w₁ w₂ v : V}
    (hve : polar Q v P.e = 0) (hve' : polar Q v P'.e = 0)
    (hwe : polar Q P.e w₁ = 0) (hwe' : polar Q P'.e w₁ = 0)
    (hw2 : polar Q P'.e w₂ = 0) :
    (eichler Q P.e w₁ * eichler Q P'.e w₂) v
      = v - polar Q v w₁ • P.e - polar Q v w₂ • P'.e := by
  rw [LinearEquiv.mul_apply]
  have hinner : eichler Q P'.e w₂ v = v - polar Q v w₂ • P'.e := by
    rw [eichler_apply P'.Q_e hw2, hve']
    simp
  rw [hinner]
  have hcross : polar Q (v - polar Q v w₂ • P'.e) P.e = 0 := by
    rw [polar_sub_left, polar_smul_left_eq, hve]
    simp [polar_comm Q P'.e P.e, h.ee]
  have hcross1 : polar Q (v - polar Q v w₂ • P'.e) w₁ = polar Q v w₁ := by
    rw [polar_sub_left, polar_smul_left_eq]
    simp [hwe']
  rw [eichler_apply P.Q_e hwe, hcross, hcross1]
  simp only [zero_smul, mul_zero, add_zero, sub_zero]
  abel

theorem mem_axisRadical_of_flag {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) {P P' : HypPair Q}
    (h : P.Orth P') [CharP K 2] [FiniteDimensional K V]
    (hV : 6 ≤ Module.finrank K V) {T : V ≃ₗ[K] V} (hT : ∀ v, Q (T v) = Q v)
    (hTY : ∀ v ∈ siegelY K P.e P'.e, T v = v)
    (hTperp : ∀ v, (∀ x ∈ siegelY K P.e P'.e, polar Q v x = 0) →
      T v - v ∈ siegelY K P.e P'.e) :
    T ∈ axisRadical Q P.e P'.e := by
  have hTorth : T ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hT
  have mem_P : P.e ∈ siegelY K P.e P'.e :=
    Submodule.mem_span_pair.mpr ⟨1, 0, by rw [one_smul, zero_smul, add_zero]⟩
  have mem_P' : P'.e ∈ siegelY K P.e P'.e :=
    Submodule.mem_span_pair.mpr ⟨0, 1, by rw [zero_smul, one_smul, zero_add]⟩
  let B : LinearMap.BilinForm K V := polarBilin Q
  have hB : B.Nondegenerate := hQ
  let φ₁ : Module.Dual K V := (B P.f).comp ((T : V →ₗ[K] V) - LinearMap.id)
  let φ₂ : Module.Dual K V := (B P'.f).comp ((T : V →ₗ[K] V) - LinearMap.id)
  let w₁ : V := (B.toDual hB).symm φ₁
  let w₂ : V := (B.toDual hB).symm φ₂
  have hw₁ : ∀ v, polar Q w₁ v = polar Q P.f (T v - v) := by
    intro v
    have h1 : B w₁ v = φ₁ v :=
      LinearMap.BilinForm.apply_toDual_symm_apply (B := B) (hB := hB) φ₁ v
    have h2 : polar Q w₁ v = B w₁ v := by simp [B]
    have h3 : φ₁ v = polar Q P.f (T v - v) := by
      simp [φ₁, B, LinearMap.sub_apply, LinearMap.id_apply]
    exact h2.trans (h1.trans h3)
  have hw₂ : ∀ v, polar Q w₂ v = polar Q P'.f (T v - v) := by
    intro v
    have h1 : B w₂ v = φ₂ v :=
      LinearMap.BilinForm.apply_toDual_symm_apply (B := B) (hB := hB) φ₂ v
    have h2 : polar Q w₂ v = B w₂ v := by simp [B]
    have h3 : φ₂ v = polar Q P'.f (T v - v) := by
      simp [φ₂, B, LinearMap.sub_apply, LinearMap.id_apply]
    exact h2.trans (h1.trans h3)
  have hw₁mem : ∀ x ∈ siegelY K P.e P'.e, polar Q w₁ x = 0 := by
    intro x hx
    rw [hw₁ x, hTY x hx, sub_self, polar_zero_right]
  have hw₂mem : ∀ x ∈ siegelY K P.e P'.e, polar Q w₂ x = 0 := by
    intro x hx
    rw [hw₂ x, hTY x hx, sub_self, polar_zero_right]
  have key : ∀ v, (∀ x ∈ siegelY K P.e P'.e, polar Q v x = 0) →
      T v = v + polar Q P.f (T v - v) • P.e + polar Q P'.f (T v - v) • P'.e := by
    intro v hv
    have hmem : T v - v ∈ siegelY K P.e P'.e := hTperp v hv
    have hcoe := flag_eq_of_mem_siegelY (Q := Q) h hmem
    calc T v = v + (T v - v) := (add_sub_cancel v (T v)).symm
      _ = v + (polar Q P.f (T v - v) • P.e + polar Q P'.f (T v - v) • P'.e) := by
            conv_lhs => rw [hcoe]
      _ = v + polar Q P.f (T v - v) • P.e + polar Q P'.f (T v - v) • P'.e := by abel
  let Pe : V ≃ₗ[K] V := eichler Q P.e w₁ * eichler Q P'.e w₂
  have hPe_orth : Pe ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    mul_mem (eichler_mem_orthogonalGroup Q P.e w₁) (eichler_mem_orthogonalGroup Q P'.e w₂)
  have hPe : ∀ v, (∀ x ∈ siegelY K P.e P'.e, polar Q v x = 0) → Pe v = T v := by
    intro v hv
    have heval := flag_mul_eichler_apply (Q := Q) (P := P) (P' := P') h (w₁ := w₁)
      (w₂ := w₂) (v := v) (hv P.e mem_P) (hv P'.e mem_P')
      (by rw [polar_comm]; exact hw₁mem P.e mem_P)
      (by rw [polar_comm]; exact hw₁mem P'.e mem_P')
      (by rw [polar_comm]; exact hw₂mem P'.e mem_P')
    have hα₁ : polar Q v w₁ = polar Q P.f (T v - v) := by rw [polar_comm, hw₁ v]
    have hα₂ : polar Q v w₂ = polar Q P'.f (T v - v) := by rw [polar_comm, hw₂ v]
    rw [heval, key v hv, hα₁, hα₂, sub_eq_add_neg, sub_eq_add_neg, ← neg_smul, ← neg_smul,
      CharTwo.neg_eq, CharTwo.neg_eq]
  let S : V ≃ₗ[K] V := Pe⁻¹ * T
  have hSorth : S ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    mul_mem (inv_mem hPe_orth) hTorth
  have hSfix : ∀ v, (∀ x ∈ siegelY K P.e P'.e, polar Q v x = 0) → S v = v := by
    intro v hv
    have h := hPe v hv
    show Pe⁻¹ (T v) = v
    rw [← h]
    exact LinearEquiv.inv_apply_apply' Pe v
  have hScentral : S ∈ Subgroup.centralizer (axisRadical Q P.e P'.e : Set (V ≃ₗ[K] V)) := by
    rw [axisRadical, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro g ⟨u, w, hu, ha, hb, rfl⟩
    have hu' : S u = u := hSfix u (fun x hx => flag_polar_eq_zero_of_mem_siegelY h hu hx)
    have hw' : S w = w := hSfix w (fun x hx => by
      obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.mp hx
      simp only [polar_add_right, polar_smul_right_eq, polar_comm Q w P.e,
        polar_comm Q w P'.e, ha, hb, mul_zero, add_zero])
    have hcomm := eichler_conj hSorth u w
    rw [hu', hw'] at hcomm
    have h2 := congrArg (· * S) hcomm
    simpa [mul_assoc] using h2.symm
  obtain ⟨c, hc⟩ := (mem_centralizer_axisRadical_iff hQ h hV hSorth).mp hScentral
  have hS_mem : S ∈ axisRadical Q P.e P'.e := by
    rw [hc]
    refine Subgroup.subset_closure ⟨P.e, c • P'.e, mem_P, ?_, ?_, rfl⟩
    · rw [polar_smul_right_eq, h.ee, mul_zero]
    · rw [polar_smul_right_eq, P'.polar_ee, mul_zero]
  have hPe_mem : Pe ∈ axisRadical Q P.e P'.e := by
    refine mul_mem (Subgroup.subset_closure ⟨P.e, w₁, mem_P, ?_, ?_, rfl⟩)
      (Subgroup.subset_closure ⟨P'.e, w₂, mem_P', ?_, ?_, rfl⟩)
    · rw [polar_comm]; exact hw₁mem P.e mem_P
    · rw [polar_comm]; exact hw₁mem P'.e mem_P'
    · rw [polar_comm]; exact hw₂mem P.e mem_P
    · rw [polar_comm]; exact hw₂mem P'.e mem_P'
  have hT_eq : T = Pe * S := by
    show T = Pe * (Pe⁻¹ * T)
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  rw [hT_eq]
  exact mul_mem hPe_mem hS_mem

end CFSG.StandardType.LieKnownR2.POmega.Radical
