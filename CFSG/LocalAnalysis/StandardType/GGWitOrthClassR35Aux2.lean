module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR35Aux
public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassL51Aux
public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR35Bridge
public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR35Aux4

public section

namespace CFSG.StandardType.ZS

open Subgroup QuadraticMap

attribute [-instance] Nat.fact_prime_three

def owR35_secondH {p : ℕ} (w : Fin 5 → ZMod p) : Prop :=
  ∀ a : Fin 5 → ZMod p, (∑ i, w i * (a i) ^ 2) = 1 →
  ∀ u : Fin 5 → ZMod p, (∑ i, w i * (u i) ^ 2) = 0 →
    (2 * ∑ i, w i * (a i * u i)) = 0 → u ≠ 0 →
    ∃ u' : Fin 5 → ZMod p, u' ≠ 0 ∧ (∑ i, w i * (u' i) ^ 2) = 0 ∧
      (2 * ∑ i, w i * (a i * u' i)) = 0 ∧
      (2 * ∑ i, w i * (u i * u' i)) = 0 ∧ u' ≠ u ∧ u' ≠ -u

theorem owR35_l51_of_second {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (c : ZMod p) (hc : c ≠ 0) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : A = closure (ClassRefl p Q c)) (hp3 : p = 3)
    (hsecond : ∀ a u : U, Q a = c → Q u = 0 → polarBilin Q u a = 0 → u ≠ 0 →
      ∃ u' : U, u' ≠ 0 ∧ Q u' = 0 ∧ polarBilin Q u' a = 0 ∧ polarBilin Q u' u = 0 ∧
        u' ∉ Submodule.span (ZMod p) {u}) :
    ∀ r ∈ A, IsRefl p r → WitL51 p A r := by
  subst p
  letI : Field (ZMod 3) := @ZMod.instField 3 ⟨by norm_num⟩
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
  obtain ⟨u', hu'0, hu'Q, hu'a, hu'u, hu'span⟩ := hsecond a u haQ huQ huB hu0
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

theorem owR35_secondH_abstract {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (e : U ≃ₗ[ZMod p] (Fin 5 → ZMod p)) (w : Fin 5 → ZMod p)
    (he : ∀ v, Q v = ∑ i, w i * (e v i) ^ 2) (hw : ∀ i, w i ≠ 0)
    (hp3 : p = 3) (hsecond : owR35_secondH w) :
    ∀ a u : U, Q a = 1 → Q u = 0 → polarBilin Q u a = 0 → u ≠ 0 →
      ∃ u' : U, u' ≠ 0 ∧ Q u' = 0 ∧ polarBilin Q u' a = 0 ∧ polarBilin Q u' u = 0 ∧
        u' ∉ Submodule.span (ZMod p) {u} := by
  subst p
  letI : Field (ZMod 3) := @ZMod.instField 3 ⟨by norm_num⟩
  have hpol : ∀ x y : U, QuadraticMap.polar Q x y = 2 * ∑ i, w i * (e x i * e y i) := by
    intro x y
    simp only [QuadraticMap.polar, he, map_add, Pi.add_apply]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  intro a u ha hu hpa hu0
  rw [QuadraticMap.polarBilin_apply_apply] at hpa
  have hBeaeu : (2 * ∑ i, w i * (e a i * e u i)) = 0 := by
    rw [hpol u a] at hpa
    rw [show (∑ i, w i * (e a i * e u i)) = ∑ i, w i * (e u i * e a i) by
      refine Finset.sum_congr rfl fun i _ => by ring]
    exact hpa
  obtain ⟨u'', hu''0, hu''Q, hu''a, hu''u, hu''neu, hu''neneg⟩ :=
    hsecond (e a) (by rw [← he a]; exact ha) (e u) (by rw [← he u]; exact hu)
      hBeaeu (fun h => hu0 (e.injective (by rw [h, map_zero])))
  let u' : U := e.symm u''
  have hu'e : e u' = u'' := LinearEquiv.apply_symm_apply e u''
  refine ⟨u', ?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact hu''0 (by rw [← hu'e, h, map_zero])
  · rw [he u', hu'e]; exact hu''Q
  · rw [QuadraticMap.polarBilin_apply_apply, hpol u' a, hu'e]
    rw [show (∑ i, w i * (u'' i * e a i)) = ∑ i, w i * (e a i * u'' i) by
      refine Finset.sum_congr rfl fun i _ => by ring]
    exact hu''a
  · rw [QuadraticMap.polarBilin_apply_apply, hpol u' u, hu'e]
    rw [show (∑ i, w i * (u'' i * e u i)) = ∑ i, w i * (e u i * u'' i) by
      refine Finset.sum_congr rfl fun i _ => by ring]
    exact hu''u
  · intro hmem
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨l, hl⟩ := hmem
    have hcases : ∀ m : ZMod 3, m = 1 ∨ m = -1 ∨ m = 0 := by decide
    rcases hcases l with h1 | h1 | h1
    · apply hu''neu
      rw [← hu'e, ← hl, h1, one_smul]
    · apply hu''neneg
      rw [← hu'e, ← hl, h1, map_smul, neg_smul, one_smul]
    · apply hu''0
      rw [← hu'e, ← hl, h1, zero_smul, map_zero]

private theorem owR35_l51_half {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (e : U ≃ₗ[ZMod p] (Fin 5 → ZMod p)) (w : Fin 5 → ZMod p)
    (he : ∀ v, Q v = ∑ i, w i * (e v i) ^ 2) (hw : ∀ i, w i ≠ 0)
    (hp3 : p = 3) (hsecond : owR35_secondH w) :
    ∀ r ∈ Subgroup.closure (ClassRefl p Q 1), IsRefl p r →
      WitL51 p (Subgroup.closure (ClassRefl p Q 1)) r := by
  subst p
  exact owR35_l51_of_second (p := 3) (by norm_num) (by norm_num) Q hQ (1 : ZMod 3) (by decide) rfl rfl
    (owR35_secondH_abstract (p := 3) (by norm_num) (by norm_num) Q hQ e w he hw rfl hsecond)

theorem owR35_nondeg_smul {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {u : K}
    (hu : u ≠ 0) : (QuadraticMap.polarBilin (u • Q)).Nondegenerate := by
  have hpolar : ∀ x y : V, QuadraticMap.polar (u • Q) x y = u * QuadraticMap.polar Q x y := by
    intro x y
    simp only [QuadraticMap.polar, QuadraticMap.smul_apply, smul_eq_mul]
    ring
  refine ⟨fun x hx => hQ.1 x (fun y => ?_), fun y hy => hQ.2 y (fun x => ?_)⟩
  · have h := hx y
    rw [QuadraticMap.polarBilin_apply_apply, hpolar] at h
    rw [QuadraticMap.polarBilin_apply_apply]
    exact (mul_eq_zero.mp h).resolve_left hu
  · have h := hy x
    rw [QuadraticMap.polarBilin_apply_apply, hpolar] at h
    rw [QuadraticMap.polarBilin_apply_apply]
    exact (mul_eq_zero.mp h).resolve_left hu

theorem owR35_coord {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (e : U ≃ₗ[ZMod p] (Fin 5 → ZMod p)) (w : Fin 5 → ZMod p)
    (he : ∀ v, Q v = ∑ i, w i * (e v i) ^ 2)
    (hw : ∀ i, w i ≠ 0) (c : ZMod p) (hc : c ≠ 0) (hp3 : p = 3) :
    LinWeyl p (Subgroup.closure (ClassRefl p Q c)) ∨
    ∀ r ∈ Subgroup.closure (ClassRefl p Q c), IsRefl p r →
      WitL51 p (Subgroup.closure (ClassRefl p Q c)) r := by
  subst hp3
  letI : Field (ZMod 3) := @ZMod.instField 3 ⟨by norm_num⟩
  have hcinv : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
  have hu : c⁻¹ ≠ 0 := inv_ne_zero hc
  have hcl : ClassRefl 3 Q c = ClassRefl 3 (c⁻¹ • Q) 1 := by
    rw [owR35_classRefl_smul_form Q c c⁻¹ hu, hcinv]
  rw [hcl]
  have hQ1 : (QuadraticMap.polarBilin (c⁻¹ • Q)).Nondegenerate := owR35_nondeg_smul Q hQ hu
  have hw1 : ∀ i, c⁻¹ * w i = 1 ∨ c⁻¹ * w i = 2 := by
    intro i
    have h0 : c⁻¹ * w i ≠ 0 := mul_ne_zero hu (hw i)
    have hcases : ∀ m : ZMod 3, m ≠ 0 → m = 1 ∨ m = 2 := by decide
    exact hcases _ h0
  have he1 : ∀ v, (c⁻¹ • Q) v = ∑ i, (c⁻¹ * w i) * (e v i) ^ 2 := by
    intro v
    rw [QuadraticMap.smul_apply, he v, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨π, hπ⟩ := owR35_perm_exists (fun i => c⁻¹ * w i) hw1
  let e' : U ≃ₗ[ZMod 3] (Fin 5 → ZMod 3) := e.trans (owR35_permIso π)
  have he' : ∀ v, (c⁻¹ • Q) v = ∑ i, owR35_wcan (owR35_kOf (fun i => c⁻¹ * w i)) i * (e' v i) ^ 2 := by
    intro v
    have h := owR35_permIso_form π (fun i => c⁻¹ * w i) (owR35_kOf (fun i => c⁻¹ * w i)) hπ (e v)
    simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul] at h
    rw [he1 v]
    simp only [pow_two]
    exact h.symm
  generalize owR35_kOf (fun i => c⁻¹ * w i) = k at he'
  have hwc : ∀ (k : Fin 6) (i : Fin 5), owR35_wcan k i ≠ 0 := by
    intro k i
    simp only [owR35_wcan]
    split_ifs <;> decide
  fin_cases k
  · exact Or.inr (owR35_l51_half (p := 3) (by norm_num) (by norm_num) (c⁻¹ • Q) hQ1 e' _ he'
      (hwc _) rfl DataR35.secondIso_0)
  · exact Or.inl (owR35_e6_canon_1 (c⁻¹ • Q) e' he')
  · exact Or.inr (owR35_l51_half (p := 3) (by norm_num) (by norm_num) (c⁻¹ • Q) hQ1 e' _ he'
      (hwc _) rfl DataR35.secondIso_2)
  · exact Or.inl (owR35_e6_canon_3 (c⁻¹ • Q) e' he')
  · exact Or.inr (owR35_l51_half (p := 3) (by norm_num) (by norm_num) (c⁻¹ • Q) hQ1 e' _ he'
      (hwc _) rfl DataR35.secondIso_4)
  · exact Or.inl (owR35_e6_canon_5 (c⁻¹ • Q) e' he')

end CFSG.StandardType.ZS

end
