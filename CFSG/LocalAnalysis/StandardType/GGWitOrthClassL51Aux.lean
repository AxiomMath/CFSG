module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthL51Aux4
public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassCrAux

public section

namespace CFSG.StandardType.ZS

open Subgroup QuadraticMap

theorem owC5_refl_form_of_root {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U]
    (Q : QuadraticForm K U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (h2 : (2 : K) ≠ 0)
    {r : U ≃ₗ[K] U} (hr2 : r * r = 1)
    (hrk : Module.finrank K (LinearMap.range ((r : U →ₗ[K] U) - LinearMap.id)) = 1)
    (hisom : ∀ v, Q (r v) = Q v) {a : U} (ha : Q a ≠ 0) (hra : r a = -a) :
    r = owCr_orthRefl Q a ha := by
  have ha_ne : a ≠ 0 := fun h => ha (by rw [h, QuadraticMap.map_zero])
  obtain ⟨a', ha', hr_eq⟩ := owCr_refl_form Q hQ h2 hr2 hrk hisom
  have hrefl : owCr_orthRefl Q a' ha' a = -a := by rw [← hr_eq]; exact hra
  have hcoe : ((polarBilin Q a a') / Q a') • a' = (2 : K) • a := by
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
    have hzero : (2 : K) • a = 0 := by rw [← hcoe, h0]; simp
    rcases smul_eq_zero.mp hzero with h2a | haa
    · exact h2 h2a
    · exact ha_ne haa
  have ha'_eq : a' = ((polarBilin Q a a' / Q a')⁻¹ * 2) • a := by
    have h := congrArg (fun w => ((polarBilin Q a a' / Q a')⁻¹) • w) hcoe
    rw [smul_smul, inv_mul_cancel₀ (div_ne_zero hBa' ha'), one_smul] at h
    exact h.trans (by rw [smul_smul])
  have hl : ((polarBilin Q a a' / Q a')⁻¹ * 2) ≠ 0 :=
    mul_ne_zero (inv_ne_zero (div_ne_zero hBa' ha')) h2
  have ha'' : Q (((polarBilin Q a a' / Q a')⁻¹ * 2) • a) ≠ 0 := by
    rw [← ha'_eq]; exact ha'
  have hcongr : owCr_orthRefl Q a' ha'
      = owCr_orthRefl Q (((polarBilin Q a a' / Q a')⁻¹ * 2) • a) ha'' := by
    congr 1
  exact hr_eq.trans (hcongr.trans (owCc_orthRefl_smul Q a hl ha ha''))

theorem owC5_wit_orthClass_l51 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (c : ZMod p) (hc : c ≠ 0) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : A = closure (ClassRefl p Q c)) (hp3 : p = 3)
    (hd : 6 ≤ Module.finrank (ZMod p) U) :
    ∀ r ∈ A, IsRefl p r → WitL51 p A r := by
  subst p
  intro r hrA hr
  have hclass_r : r ∈ ClassRefl 3 Q c :=
    wit_classRefl_of_mem_closure (p := 3) (by norm_num) (by norm_num) Q hQ c hc hr (hA ▸ hrA)
  obtain ⟨_, hisom_r, a, haQ, hra⟩ := hclass_r
  have ha : Q a ≠ 0 := by rw [haQ]; exact hc
  have hr_a : r = owCr_orthRefl Q a ha :=
    owC5_refl_form_of_root Q hQ (owL5_two_ne_zero (K := ZMod 3)) hr.1 hr.2 hisom_r ha hra
  subst r
  intro r₂ hr₂A hr₂ hord
  have hclass_r₂ : r₂ ∈ ClassRefl 3 Q c :=
    wit_classRefl_of_mem_closure (p := 3) (by norm_num) (by norm_num) Q hQ c hc hr₂ (hA ▸ hr₂A)
  obtain ⟨_, hisom_r₂, b, hbQ, hrb⟩ := hclass_r₂
  have hb : Q b ≠ 0 := by rw [hbQ]; exact hc
  have hr₂_b : r₂ = owCr_orthRefl Q b hb :=
    owC5_refl_form_of_root Q hQ (owL5_two_ne_zero (K := ZMod 3)) hr₂.1 hr₂.2 hisom_r₂ hb hrb
  subst r₂
  have hra2 : owCr_orthRefl Q a ha * owCr_orthRefl Q a ha = 1 := hr.1
  have hrb2 : owCr_orthRefl Q b hb * owCr_orthRefl Q b hb = 1 := hr₂.1
  obtain ⟨u, b', hb', hu0, huQ, huB, hb'eq, hrb_eq⟩ :=
    owL5_exists_u (fun x hx => owL5_zmod3_sq x hx) Q ha hb hra2 hrb2 hord
  subst b'
  have hodd : Odd (Nat.card (ZMod 3)) := by rw [Nat.card_zmod]; decide
  obtain ⟨u', hu'0, hu'Q, hu'a, hu'u, hu'span⟩ :=
    owL5_exists_second_isotropic hodd (owL5_two_ne_zero (K := ZMod 3)) Q hQ hd ha huQ huB hu0
  have hbu' : Q (a - u') ≠ 0 := by
    rw [sub_eq_add_neg, owCr_Q_add_eq Q a (-u') (owL5_Q_neg Q hu'Q)
      (by rw [polarBilin_apply_apply, polar_neg_left, ← polarBilin_apply_apply, hu'a]; ring)]
    exact ha
  have hQm : Q ((2 : ZMod 3) • a - u') = c := by
    rw [sub_eq_add_neg, owCr_Q_add_eq Q ((2 : ZMod 3) • a) (-u') (owL5_Q_neg Q hu'Q)
      (by rw [polarBilin_apply_apply, polar_neg_left, polar_smul_right,
        ← polarBilin_apply_apply, hu'a]; ring)]
    rw [QuadraticMap.map_smul, smul_eq_mul]
    rw [show (2 : ZMod 3) * 2 * Q a = Q a by
      rw [show (2 : ZMod 3) * 2 = 1 by decide +kernel, one_mul]]
    exact haQ
  have hbm : Q ((2 : ZMod 3) • a - u') ≠ 0 := by rw [hQm]; exact hc
  have hg_refl : IsRefl 3 (owCr_orthRefl Q ((2 : ZMod 3) • a - u') hbm) := by
    refine ⟨owCc_orthRefl_mul_self Q _ hbm, ?_⟩
    change Module.finrank (ZMod 3)
      (LinearMap.range (((owCr_orthRefl Q ((2 : ZMod 3) • a - u') hbm : U ≃ₗ[ZMod 3] U) :
        U →ₗ[ZMod 3] U) - LinearMap.id)) = 1
    rw [owCc_orthRefl_range Q _ hbm (owL5_two_ne_zero (K := ZMod 3))]
    exact finrank_span_singleton (fun h => hbm (by rw [h, QuadraticMap.map_zero]))
  have hgA : owCr_orthRefl Q ((2 : ZMod 3) • a - u') hbm ∈ A := by
    rw [hA]
    exact Subgroup.subset_closure
      ⟨hg_refl, owCr_orthRefl_isIsom Q _ hbm, (2 : ZMod 3) • a - u', hQm,
        owCr_orthRefl_self Q _ hbm⟩
  refine ⟨owCr_orthRefl Q ((2 : ZMod 3) • a - u') hbm, hgA, ?_, ?_⟩
  · rw [owL5_conj Q ha hu'Q hu'a hbu' hbm]
    intro hcomm
    exact owL5_not_commute Q ha hu'0 hu'Q hu'a hbu' hcomm.1
  · rw [owL5_conj Q ha hu'Q hu'a hbu' hbm, hrb_eq]
    have hnine := owL5_orbit_card_nine_aux (Nat.card_zmod 3)
      (fun y => ZMod.natCast_zmod_surjective y) Q ha huQ hu'Q huB hu'a hu'u
      (owL5_linearIndependent Q ha huQ hu'Q huB hu'a hu'u hu0 hu'span) hb' hbu'
    intro hdvd
    have h948 : 9 ∣ 48 := dvd_trans hnine hdvd
    norm_num at h948

end CFSG.StandardType.ZS

end
