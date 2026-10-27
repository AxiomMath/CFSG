module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassDim3Aux

public section

namespace CFSG.StandardType.ZS

open Subgroup QuadraticMap

theorem owD3_odd_card_zmod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : Odd (Nat.card (ZMod p)) := by
  rw [Nat.card_zmod]
  exact hp.eq_two_or_odd'.resolve_left hp2

theorem owD3_refl_form {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (c : ZMod p) (hc : c ≠ 0) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : A = closure (ClassRefl p Q c))
    {r : U ≃ₗ[ZMod p] U} (hrA : r ∈ A) (hr : IsRefl p r) :
    ∃ (a : U) (ha : Q a ≠ 0), Q a = c ∧
      ∀ v, Q a • r v = Q a • v - polarBilin Q v a • a := by
  letI : Field (ZMod p) := @ZMod.instField p ⟨hp⟩
  have h2K : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdiv : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    exact hp2 (le_antisymm hle hp.two_le)
  have hclass : r ∈ ClassRefl p Q c :=
    wit_classRefl_of_mem_closure hp hp2 Q hQ c hc hr (hA ▸ hrA)
  obtain ⟨hr2, hrk⟩ := hr
  obtain ⟨_, hisom, a, haQ, hra⟩ := hclass
  have ha : Q a ≠ 0 := by rw [haQ]; exact hc
  have ha_ne : a ≠ 0 := fun h => ha (by rw [h, QuadraticMap.map_zero])
  obtain ⟨a', ha', hr_eq⟩ := owCr_refl_form Q hQ h2K hr2 hrk hisom
  have hrefl : owCr_orthRefl Q a' ha' a = -a := by rw [← hr_eq]; exact hra
  have hcoe : ((polarBilin Q a a') / Q a') • a' = (2 : ZMod p) • a := by
    have h := hrefl
    rw [owCr_orthRefl_apply] at h
    have h1 : a = -a + ((polarBilin Q a a') / Q a') • a' := (sub_eq_iff_eq_add.mp h)
    have h2'' : a + a = ((polarBilin Q a a') / Q a') • a' := by
      have := congrArg (fun t => t - (-a)) h1
      rwa [add_sub_cancel_left, sub_neg_eq_add] at this
    rw [two_smul]
    exact h2''.symm
  have hBa' : polarBilin Q a a' ≠ 0 := by
    intro h0
    have hzero : (2 : ZMod p) • a = 0 := by rw [← hcoe, h0]; simp
    rcases smul_eq_zero.mp hzero with h2a | haa
    · exact h2K h2a
    · exact ha_ne haa
  have ha'_eq : a' = ((polarBilin Q a a' / Q a')⁻¹ * 2) • a := by
    have h := congrArg (fun w => ((polarBilin Q a a' / Q a')⁻¹) • w) hcoe
    rw [smul_smul, inv_mul_cancel₀ (div_ne_zero hBa' ha'), one_smul] at h
    exact h.trans (by rw [smul_smul])
  have hl : ((polarBilin Q a a' / Q a')⁻¹ * 2) ≠ 0 :=
    mul_ne_zero (inv_ne_zero (div_ne_zero hBa' ha')) h2K
  have ha'' : Q (((polarBilin Q a a' / Q a')⁻¹ * 2) • a) ≠ 0 := by
    rw [← ha'_eq]; exact ha'
  have hcongr : owCr_orthRefl Q a' ha'
      = owCr_orthRefl Q (((polarBilin Q a a' / Q a')⁻¹ * 2) • a) ha'' := by
    congr 1
  have hr_a : r = owCr_orthRefl Q a ha := by
    rw [hr_eq, hcongr]
    exact owCc_orthRefl_smul Q a hl ha ha''
  refine ⟨a, ha, haQ, ?_⟩
  intro v
  rw [hr_a, owCr_orthRefl_apply, smul_sub, smul_smul]
  congr 1
  field_simp [ha]

theorem owD3_exists_orth_norm {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank (ZMod p) U = 3) (c : ZMod p) (hc : c ≠ 0)
    {a : U} (haQ : Q a = c) (μ : ZMod p) (hμ : μ ^ 2 ≠ 4) :
    ∃ v : U, Q v = c ∧ polarBilin Q a v = μ * c := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  letI : Field (ZMod p) := @ZMod.instField p ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdiv : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    exact hp2 (le_antisymm hle hp.two_le)
  have h4 : (4 : ZMod p) ≠ 0 := by
    intro h
    have hdiv : p ∣ 4 := (CharP.cast_eq_zero_iff (ZMod p) p 4).mp h
    have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdiv
    have hpge : 2 ≤ p := hp.two_le
    interval_cases p
    · exact absurd rfl hp2
    · norm_num at hdiv
    · norm_num at hp
  have ha : Q a ≠ 0 := by rw [haQ]; exact hc
  have ha_ne : a ≠ 0 := fun h => ha (by rw [h, QuadraticMap.map_zero])
  have hodd : Odd (Nat.card (ZMod p)) := owD3_odd_card_zmod hp hp2
  let V : Submodule (ZMod p) U := LinearMap.BilinForm.orthogonal (polarBilin Q) (ZMod p ∙ a)
  have hVfin : Module.finrank (ZMod p) V = 2 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hQ (ZMod p ∙ a), finrank_span_singleton ha_ne, hd]
  have hVnd : (polarBilin (Q.comp V.subtype)).Nondegenerate :=
    owCr_restrict_nondegenerate Q hQ h2 a ha
  have h4mu : (4 : ZMod p) - μ ^ 2 ≠ 0 := by
    intro h
    exact hμ (sub_eq_zero.mp h).symm
  let t : ZMod p := c * (4 - μ ^ 2) / 4
  have ht : t ≠ 0 := div_ne_zero (mul_ne_zero hc h4mu) h4
  obtain ⟨w, hwQ⟩ :=
    owD3_binary_represents (K := ZMod p) hodd (Q.comp V.subtype) hVnd hVfin t ht
  have hwB : polarBilin Q a (w : U) = 0 := by
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp w.2) a (Submodule.mem_span_singleton_self a)
    simpa using h
  have hwQ' : Q (w : U) = t := by simpa using hwQ
  refine ⟨(μ / 2) • a + (w : U), ?_, ?_⟩
  · calc Q ((μ / 2) • a + (w : U))
        = Q ((μ / 2) • a) + Q (w : U) + polar Q ((μ / 2) • a) (w : U) :=
            QuadraticMap.map_add Q _ _
      _ = (μ / 2) ^ 2 * Q a + t + (μ / 2) * polar Q a (w : U) := by
            rw [QuadraticMap.map_smul, smul_eq_mul, pow_two, polar_smul_left, hwQ']
            ring
      _ = (μ / 2) ^ 2 * c + t + (μ / 2) * 0 := by
            rw [haQ, show polar Q a (w : U) = 0 by rw [← polarBilin_apply_apply]; exact hwB]
      _ = c := by
            rw [show t = c * (4 - μ ^ 2) / 4 by rfl]
            field_simp [h2, h4, hc]
            ring
  · calc polarBilin Q a ((μ / 2) • a + (w : U))
        = polarBilin Q a ((μ / 2) • a) + polarBilin Q a (w : U) := by rw [map_add]
      _ = (μ / 2) * polarBilin Q a a + polarBilin Q a (w : U) := by
            simp only [polarBilin_apply_apply, polar_smul_right, smul_eq_mul]
      _ = (μ / 2) * (2 * c) + 0 := by
            rw [polarBilin_apply_apply, polar_self, two_smul, haQ, hwB]
            ring
      _ = μ * c := by
            field_simp [h2]
            ring


private theorem owD3_two_ne_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hdiv : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
  exact hp2 (le_antisymm hle hp.two_le)

theorem owD3_wit_cr_mu {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (c : ZMod p) (hc : c ≠ 0) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : A = closure (ClassRefl p Q c))
    (hd : Module.finrank (ZMod p) U = 3)
    (μ : ZMod p) (hμ : μ ^ 2 ≠ 4)
    (hx0 : 2 - μ ^ 2 ≠ 0) (hx1 : (2 - μ ^ 2) ^ 2 ≠ 1)
    (hx2 : (2 - μ ^ 2) ^ 2 ≠ 2) (hx4 : (2 - μ ^ 2) ^ 2 ≠ 4) :
    ∀ r ∈ A, IsRefl p r → WitCR p A r := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  letI : Field (ZMod p) := @ZMod.instField p ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := owD3_two_ne_zero hp hp2
  haveI : Fintype (ZMod p) := ZMod.fintype p
  haveI : Fintype (Fin (Module.finrank (ZMod p) U) →₀ ZMod p) := Finsupp.fintype
  haveI : Finite U := by
    let b := Module.finBasis (ZMod p) U
    exact Finite.of_injective (fun u => b.repr u) (fun u₁ u₂ h => b.repr.injective h)
  intro r hrA hr
  obtain ⟨a, ha, haQ, hrefl⟩ := owD3_refl_form hp hp2 Q hQ c hc hA hrA hr
  have hr_a : r = owCr_orthRefl Q a ha := by
    ext v
    rw [owCr_orthRefl_apply]
    have h := hrefl v
    calc r v = (Q a)⁻¹ • (Q a • r v) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
      _ = (Q a)⁻¹ • (Q a • v - polarBilin Q v a • a) := by rw [h]
      _ = v - (polarBilin Q v a / Q a) • a := by
            rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ ha, one_smul]
            congr 1
            field_simp [ha]
  obtain ⟨v, hvQ, hvB⟩ := owD3_exists_orth_norm hp hp2 Q hQ hd c hc haQ μ hμ
  have hv : Q v ≠ 0 := by rw [hvQ]; exact hc
  let g : U ≃ₗ[ZMod p] U := owCr_orthRefl Q v hv
  have hg_isom : ∀ w, Q (g w) = Q w := owCr_orthRefl_isIsom Q v hv
  have hgv : g v = -v := owCr_orthRefl_self Q v hv
  have hg_refl : IsRefl p g := by
    refine ⟨owCc_orthRefl_mul_self Q v hv, ?_⟩
    change Module.finrank (ZMod p)
      (LinearMap.range (((owCr_orthRefl Q v hv : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - LinearMap.id)) = 1
    rw [owCc_orthRefl_range Q v hv h2]
    exact finrank_span_singleton (fun h => hv (by rw [h, QuadraticMap.map_zero]))
  have hv_ne : v ≠ 0 := fun h => hv (by rw [h, QuadraticMap.map_zero])
  have hgA : g ∈ A := by
    rw [hA]
    exact Subgroup.subset_closure ⟨hg_refl, hg_isom, v, hvQ, hgv⟩
  have hga : g a = a - μ • v := by
    change owCr_orthRefl Q v hv a = a - μ • v
    rw [owCr_orthRefl_apply, hvQ, hvB]
    field_simp [hc]
  have hga_ne : Q (g a) ≠ 0 := by rw [hg_isom a]; exact ha
  have hb : Q (g a) ≠ 0 := hga_ne
  have hgaQ : Q (g a) = c := by rw [hg_isom a, haQ]
  have hBab : polarBilin Q a (g a) = (2 - μ ^ 2) * c := by
    rw [hga, polarBilin_apply_apply, polar_sub_right, polar_smul_right, polar_self,
      ← polarBilin_apply_apply, hvB, haQ]
    ring
  have hx : polarBilin Q a (g a) / c = 2 - μ ^ 2 := by
    rw [hBab]
    field_simp [hc]
  have horder : 4 < orderOf (owCr_orthRefl Q a ha * owCr_orthRefl Q (g a) hb) :=
    owD3_order_criterion h2 Q hc ha hb haQ hgaQ hx hx0 hx1 hx2 hx4
  have hconj : g * owCr_orthRefl Q a ha * g⁻¹ = owCr_orthRefl Q (g a) hb := by
    rw [owCr_orthRefl_conj Q g hg_isom a ha hga_ne]
  refine ⟨g, hgA, ?_⟩
  rw [hr_a, hconj]
  exact horder

end CFSG.StandardType.ZS

end
