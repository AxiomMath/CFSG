module

import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallRulesAxisA
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUAJPerm
public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUDefs
public import Certificates.Data.SUSmallBase

public section

namespace CFSG.StandardType.HdRo7SU.Small

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7SmAxis_eq_one_or_eq_neg_one (c : ZMod 3) (hc : c * c = 1) :
    c = 1 ∨ c = -1 := by
  have h := (sq_eq_one_iff (a := c)).mp (by rwa [pow_two])
  exact h

private lemma hdRo7SmAxis_case_perm {m : ℕ} {r : SMGL m} {u w : SMV m}
    (hr : SMRefl r u (smDual w)) {σ : Equiv.Perm (Fin m)}
    (hσ : ∀ i, r (Pi.basisFun (ZMod 3) (Fin m) i) = Pi.basisFun (ZMod 3) (Fin m) (σ i)) :
    SMTClass (u, w) := by
  set b : Module.Basis (Fin m) (ZMod 3) (SMV m) := Pi.basisFun (ZMod 3) (Fin m) with hb_def
  have hσb : ∀ i, r (b i) = b (σ i) := hσ
  have hσ2 : ∀ i, σ (σ i) = i := by
    intro i
    have h1 : r (r (b i)) = b i := by
      rw [← LinearEquiv.mul_apply, hdRo7SmAxis_refl_involution hr]
      rfl
    have h2 : r (r (b i)) = b (σ (σ i)) := by
      rw [hσb i, hσb (σ i)]
    exact b.injective (h2.symm.trans h1)
  have hττ : σ * σ = 1 := Equiv.ext (fun i => hσ2 i)
  have hr_eq : r = b.equiv b σ := by
    apply LinearEquiv.toLinearMap_injective
    refine b.ext (fun i => ?_)
    change r (b i) = (b.equiv b σ) (b i)
    rw [hσb i, Module.Basis.equiv_apply]
  have hrank : Module.finrank (ZMod 3) (ggLinMove (b.equiv b σ)) = 1 := by
    rw [← hr_eq]
    exact hdRo7SmAxis_ggLinMove_finrank hr
  obtain ⟨a, b', hab, hswap⟩ := hdRo7SUAJPerm_transposition_of_linRefl b σ hττ hrank
  have hra : r (b a) = b b' := by
    rw [hr_eq, hswap, Module.Basis.equiv_apply, Equiv.swap_apply_left]
  have hrb : r (b b') = b a := by
    rw [hr_eq, hswap, Module.Basis.equiv_apply, Equiv.swap_apply_right]
  have hr_apply : ∀ v t, r v t = v (σ.symm t) := by
    intro v t
    rw [hr_eq]
    change ((Pi.basisFun (ZMod 3) (Fin m)).equiv (Pi.basisFun (ZMod 3) (Fin m)) σ) v t =
      v (σ.symm t)
    rw [hdRo7SmAxis_basisFun_equiv, hdRo7SmAxis_permGL_apply]
  have horth : ∀ x y, smDot (r x) (r y) = smDot x y := by
    intro x y
    simp only [smDot]
    calc ∑ t, r x t * r y t = ∑ t, x (σ.symm t) * y (σ.symm t) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [hr_apply x t, hr_apply y t]
      _ = ∑ t, x t * y t := Equiv.sum_comp σ.symm (fun t => x t * y t)
  have hb_apply : ∀ i, b i = Pi.single i 1 := by intro i; rw [hb_def, Pi.basisFun_apply]
  set d : SMV m := b a - b b' with hd_def
  have hrd : r d = -d := by
    rw [hd_def, map_sub, hra, hrb]
    abel
  have hd_span : d ∈ Submodule.span (ZMod 3) {u} :=
    hdRo7SmAxis_neg_one_mem_span hr hrd
  have hd_ne : d ≠ 0 := by
    intro h
    have := congrFun h a
    simp only [hd_def, hb_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab,
      sub_zero] at this
    exact one_ne_zero this
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hd_span
  have hc_ne : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    exact hd_ne hc.symm
  have hc_sq : c * c = 1 := hdRo7SmAxis_sq_eq_one_of_ne_zero c hc_ne
  have hu : u = c • d := by
    have h := congrArg (fun x => c • x) hc
    rw [← mul_smul, hc_sq, one_smul] at h
    exact h
  have hdd : smDot d d = 2 := by
    simp only [hd_def, hb_apply, hdRo7SmAxis_smDot_sub_left,
      hdRo7SmAxis_smDot_sub_right, hdRo7SmAxis_smDot_single_left,
      hdRo7SmAxis_smDot_single_right, Pi.sub_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne hab, Pi.single_eq_of_ne hab.symm]
    decide
  have hdu : smDot u u = 2 := by
    rw [hu, hdRo7SmAxis_smDot_smul_left, hdRo7SmAxis_smDot_smul_right, hdd]
    rw [← mul_assoc, hc_sq, one_mul]
  have hwu : w = u := by
    apply hdRo7SmAxis_smDual_injective
    apply LinearMap.ext
    intro y
    rw [hdRo7SmAxis_smDual_apply, hdRo7SmAxis_smDual_apply]
    have hru : r u = -u := by
      have h1 : r = Module.reflection hr.1 := LinearEquiv.ext fun v => by
        rw [hr.2 v, Module.reflection_apply]
      rw [h1]
      exact Module.reflection_apply_self hr.1
    have h1 : smDot (r u) (r y) = smDot u y := horth u y
    rw [hru, hr.2 y] at h1
    rw [hdRo7SmAxis_smDot_sub_right, hdRo7SmAxis_smDot_smul_right,
      hdRo7SmAxis_smDot_neg_left] at h1
    rw [hdRo7SmAxis_smDot_neg_left u u, hdu] at h1
    rw [hdRo7SmAxis_smDual_apply] at h1
    have h2 : (2 : ZMod 3) * smDot w y = 2 * smDot u y := by
      linear_combination h1
    have h22 : (2 : ZMod 3) * 2 = 1 := by decide
    have := congrArg (fun x : ZMod 3 => (2 : ZMod 3) * x) h2
    simpa only [← mul_assoc, h22, one_mul] using this
  refine ⟨a, b', c, hab, ?_, ?_, ?_⟩
  · exact hdRo7SmAxis_eq_one_or_eq_neg_one c hc_sq
  · change u = c • (Pi.single a 1 - Pi.single b' 1)
    rw [hu, hd_def, hb_apply, hb_apply]
  · change w = c • (Pi.single a 1 - Pi.single b' 1)
    rw [hwu, hu, hd_def, hb_apply, hb_apply]

private lemma hdRo7SmAxis_three_fixed {m : ℕ} {σ : Equiv.Perm (Fin m)}
    {F : Finset (Fin m)} (hFmem : ∀ i, i ∈ F ↔ σ i = i) (hF : 3 ≤ F.card) :
    ∃ i j k : Fin m, σ i = i ∧ σ j = j ∧ σ k = k ∧ i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  classical
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
  have hF1ge : 2 ≤ (F.erase i).card := by
    have hc := Finset.card_erase_add_one hi
    have h3 : 3 ≤ (F.erase i).card + 1 := by rw [hc]; exact hF
    omega
  have hF1 : 0 < (F.erase i).card := by omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hF1
  have hF2 : 0 < ((F.erase i).erase j).card := by
    have hc := Finset.card_erase_add_one hj
    have h2 : 2 ≤ ((F.erase i).erase j).card + 1 := by rw [hc]; exact hF1ge
    omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hF2
  have hj' := Finset.mem_erase.mp hj
  have hk' := Finset.mem_erase.mp hk
  have hk'' := Finset.mem_erase.mp hk'.2
  refine ⟨i, j, k, (hFmem i).mp hi, (hFmem j).mp hj'.2, (hFmem k).mp hk''.2,
    hj'.1.symm, hk''.1.symm, hk'.1.symm⟩

private lemma hdRo7SmAxis_three_cycles {m : ℕ} {σ : Equiv.Perm (Fin m)}
    (hσ2 : ∀ i, σ (σ i) = i) {M : Finset (Fin m)}
    (hMmem : ∀ i, i ∈ M ↔ σ i ≠ i) (hM : 5 ≤ M.card) :
    ∃ a c e : Fin m,
      σ a ≠ a ∧ σ c ≠ c ∧ σ e ≠ e ∧
      c ≠ a ∧ c ≠ σ a ∧ σ c ≠ a ∧ σ c ≠ σ a ∧
      e ≠ a ∧ e ≠ σ a ∧ σ e ≠ a ∧ σ e ≠ σ a ∧
      e ≠ c ∧ e ≠ σ c ∧ σ e ≠ c ∧ σ e ≠ σ c := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < M.card)
  have hMa : σ a ≠ a := (hMmem a).mp ha
  have hsaM : σ a ∈ M := (hMmem (σ a)).mpr (by rw [hσ2 a]; exact hMa.symm)
  have hsa_erase : σ a ∈ M.erase a := Finset.mem_erase.mpr ⟨hMa, hsaM⟩
  have hM1 : 3 ≤ ((M.erase a).erase (σ a)).card := by
    have h1 := Finset.card_erase_add_one hsa_erase
    have h2 := Finset.card_erase_add_one ha
    have h5 : 5 ≤ (((M.erase a).erase (σ a)).card + 1) + 1 := by rw [h1, h2]; exact hM
    omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < ((M.erase a).erase (σ a)).card)
  have hc1 := Finset.mem_erase.mp hc
  have hc2 := Finset.mem_erase.mp hc1.2
  have hc_sa : c ≠ σ a := hc1.1
  have hc_a : c ≠ a := hc2.1
  have hcM : c ∈ M := hc2.2
  have hMc : σ c ≠ c := (hMmem c).mp hcM
  have hscM : σ c ∈ M := (hMmem (σ c)).mpr (by rw [hσ2 c]; exact hMc.symm)
  have hsc_sa : σ c ≠ σ a := fun h => hc_a (σ.injective h)
  have hsc_a : σ c ≠ a := by
    intro h
    have := congrArg σ h
    rw [hσ2 c] at this
    exact hc_sa this
  have hsc_erase : σ c ∈ (M.erase a).erase (σ a) :=
    Finset.mem_erase.mpr ⟨hsc_sa, Finset.mem_erase.mpr ⟨hsc_a, hscM⟩⟩
  have hsc_erase_c : σ c ∈ ((M.erase a).erase (σ a)).erase c :=
    Finset.mem_erase.mpr ⟨hMc, hsc_erase⟩
  have hM2 : 1 ≤ ((((M.erase a).erase (σ a)).erase c).erase (σ c)).card := by
    have h1 := Finset.card_erase_add_one hsc_erase_c
    have h2 := Finset.card_erase_add_one hc
    have h3 : 3 ≤ (((((M.erase a).erase (σ a)).erase c).erase (σ c)).card + 1) + 1 := by
      rw [h1, h2]; exact hM1
    omega
  obtain ⟨e, he⟩ := Finset.card_pos.mp (by
    omega : 0 < ((((M.erase a).erase (σ a)).erase c).erase (σ c)).card)
  have he1 := Finset.mem_erase.mp he
  have he2 := Finset.mem_erase.mp he1.2
  have he3 := Finset.mem_erase.mp he2.2
  have he4 := Finset.mem_erase.mp he3.2
  have he_sc : e ≠ σ c := he1.1
  have he_c : e ≠ c := he2.1
  have he_sa : e ≠ σ a := he3.1
  have he_a : e ≠ a := he4.1
  have heM : e ∈ M := he4.2
  have hMe : σ e ≠ e := (hMmem e).mp heM
  have hseM : σ e ∈ M := (hMmem (σ e)).mpr (by rw [hσ2 e]; exact hMe.symm)
  have hse_ne_a : σ e ≠ a := by
    intro h
    have := congrArg σ h
    rw [hσ2 e] at this
    exact he_sa this
  have hse_ne_sa : σ e ≠ σ a := fun h => he_a (σ.injective h)
  have hse_ne_c : σ e ≠ c := by
    intro h
    have := congrArg σ h
    rw [hσ2 e] at this
    exact he_sc this
  have hse_ne_sc : σ e ≠ σ c := fun h => he_c (σ.injective h)
  exact ⟨a, c, e, hMa, hMc, hMe, hc_a, hc_sa, hsc_a, hsc_sa,
    he_a, he_sa, hse_ne_a, hse_ne_sa, he_c, he_sc, hse_ne_c, hse_ne_sc⟩

private lemma hdRo7SmAxis_case_neg_false {m : ℕ} (hm : m = 7 ∨ m = 8)
    {r : SMGL m} {u w : SMV m} (hr : SMRefl r u (smDual w))
    (hx : r (smOnes m) = smOnes m)
    {b : Module.Basis (Fin m) (ZMod 3) (SMV m)}
    (hb : b = Pi.basisFun (ZMod 3) (Fin m))
    {σ : Equiv.Perm (Fin m)}
    (hσ : ∀ i, r (b i) = -b (σ i) + (2 / (m : ZMod 3)) • SUOnes 3 b) : False := by
  have hb_apply : ∀ i, b i = Pi.single i 1 := by intro i; rw [hb, Pi.basisFun_apply]
  have hones : SUOnes 3 b = smOnes m := by
    funext j
    rw [SUOnes, smOnes, Finset.sum_apply]
    rw [Finset.sum_eq_single j
      (fun x _ hxj => by simp only [hb_apply, Pi.single_eq_of_ne hxj.symm])
      (fun hj => absurd (Finset.mem_univ j) hj)]
    simp only [hb_apply, Pi.single_eq_same]
  set c : ZMod 3 := 2 / (m : ZMod 3) with hc_def
  have hc_ne : c ≠ 0 := by
    rw [hc_def]
    exact div_ne_zero hdRo7SmAxis_two_ne_zero (by rcases hm with h | h <;> (rw [h]; decide))
  have hσb : ∀ i, r (b i) = -b (σ i) + c • smOnes m := by
    intro i
    rw [hc_def, ← hones]
    exact hσ i
  have hσ2 : ∀ i, σ (σ i) = i := by
    intro i
    have h1 : r (r (b i)) = b i := by
      rw [← LinearEquiv.mul_apply, hdRo7SmAxis_refl_involution hr]; rfl
    have h2 : r (r (b i)) = b (σ (σ i)) := by
      rw [hσb i, map_add, map_neg, map_smul, hσb (σ i), hx]
      module
    exact b.injective (h2.symm.trans h1)
  let F : Finset (Fin m) := Finset.univ.filter (fun i => σ i = i)
  let M : Finset (Fin m) := Finset.univ.filter (fun i => σ i ≠ i)
  have hFmem : ∀ i, i ∈ F ↔ σ i = i := by intro i; simp [F]
  have hMmem : ∀ i, i ∈ M ↔ σ i ≠ i := by intro i; simp [M]
  have hcard : F.card + M.card = m := by
    simp only [F, M]
    simpa using (Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i : Fin m => σ i = i))
  by_cases hF : F.card ≤ 2
  · have hM5 : 5 ≤ M.card := by omega
    obtain ⟨a, c', e, hMa, hMc', hMe, hc'a, hc'sa, hsc'a, hsc'sa,
      hea, hesa, hsea, hsesa, hec', hesc', hsec', hsesc'⟩ :=
      hdRo7SmAxis_three_cycles hσ2 hMmem hM5
    let v1 : SMV m := r (b a) - b a
    let v2 : SMV m := r (b c') - b c'
    have hv1_span : v1 ∈ Submodule.span (ZMod 3) {u} := by
      apply hdRo7SmAxis_neg_one_mem_span hr
      have h1 : r (r (b a)) = b a := by
        rw [← LinearEquiv.mul_apply, hdRo7SmAxis_refl_involution hr]; rfl
      rw [show v1 = r (b a) - b a from rfl, map_sub, h1]
      abel
    have hv2_span : v2 ∈ Submodule.span (ZMod 3) {u} := by
      apply hdRo7SmAxis_neg_one_mem_span hr
      have h1 : r (r (b c')) = b c' := by
        rw [← LinearEquiv.mul_apply, hdRo7SmAxis_refl_involution hr]; rfl
      rw [show v2 = r (b c') - b c' from rfl, map_sub, h1]
      abel
    have hv1a : v1 a = -1 + c := by
      rw [show v1 = r (b a) - b a from rfl, hσb a]
      simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
        hb_apply, Pi.single_eq_same, Pi.single_eq_of_ne hMa.symm, smOnes, Pi.one_apply,
        mul_one, mul_zero, neg_zero, add_zero]
      ring
    have hv2a : v2 a = c := by
      rw [show v2 = r (b c') - b c' from rfl, hσb c']
      simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
        hb_apply, Pi.single_eq_same, Pi.single_eq_of_ne hsc'a.symm, Pi.single_eq_of_ne hc'a.symm,
        smOnes, Pi.one_apply, mul_one, mul_zero, neg_zero, add_zero, zero_add, sub_zero]
    have hv1c : v1 c' = c := by
      rw [show v1 = r (b a) - b a from rfl, hσb a]
      simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
        hb_apply, Pi.single_eq_same, Pi.single_eq_of_ne hc'sa, Pi.single_eq_of_ne hc'a,
        smOnes, Pi.one_apply, mul_one, mul_zero, neg_zero, add_zero, zero_add, sub_zero]
    have hv2c : v2 c' = -1 + c := by
      rw [show v2 = r (b c') - b c' from rfl, hσb c']
      simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
        hb_apply, Pi.single_eq_same, Pi.single_eq_of_ne hMc'.symm, smOnes, Pi.one_apply,
        mul_one, mul_zero, neg_zero, add_zero, zero_add]
      ring
    have hv1e : v1 e = c := by
      rw [show v1 = r (b a) - b a from rfl, hσb a]
      simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
        hb_apply, Pi.single_eq_same, Pi.single_eq_of_ne hesa, Pi.single_eq_of_ne hea,
        smOnes, Pi.one_apply, mul_one, mul_zero, neg_zero, add_zero, zero_add, sub_zero]
    have hv2e : v2 e = c := by
      rw [show v2 = r (b c') - b c' from rfl, hσb c']
      simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
        hb_apply, Pi.single_eq_same, Pi.single_eq_of_ne hesc', Pi.single_eq_of_ne hec',
        smOnes, Pi.one_apply, mul_one, mul_zero, neg_zero, add_zero, zero_add, sub_zero]
    have hind : ∀ p q : ZMod 3, p • v1 + q • v2 = 0 → p = 0 ∧ q = 0 := by
      intro p q hpq
      have ha_eval : (p • v1 + q • v2) a = 0 := by rw [hpq]; rfl
      have hc_eval : (p • v1 + q • v2) c' = 0 := by rw [hpq]; rfl
      have he_eval : (p • v1 + q • v2) e = 0 := by rw [hpq]; rfl
      have ha_eq : p * (-1 + c) + q * c = 0 := by
        simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv1a, hv2a] using ha_eval
      have hc_eq : p * c + q * (-1 + c) = 0 := by
        simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv1c, hv2c] using hc_eval
      have he_eq : p * c + q * c = 0 := by
        simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv1e, hv2e] using he_eval
      have h1 : -p + q = 0 := by linear_combination ha_eq - hc_eq
      have h2 : p + q = 0 := by
        have h3 : (p + q) * c = 0 := by linear_combination he_eq
        exact (mul_eq_zero.mp h3).resolve_right hc_ne
      have hp0 : p = 0 := by
        have h4 : (2 : ZMod 3) * p = 0 := by linear_combination h2 - h1
        have h5 : (2 : ZMod 3) * ((2 : ZMod 3) * p) = 0 := by rw [h4, mul_zero]
        have h22 : (2 : ZMod 3) * 2 = 1 := by decide
        simpa only [← mul_assoc, h22, one_mul] using h5
      have hq0 : q = 0 := by rw [hp0, zero_add] at h2; exact h2
      exact ⟨hp0, hq0⟩
    exact hdRo7SmAxis_span_contra hv1_span hv2_span hind
  · have hF3 : 3 ≤ F.card := by omega
    obtain ⟨i, j, k, hfixi, hfixj, hfixk, hij, hik, hjk⟩ :=
      hdRo7SmAxis_three_fixed hFmem hF3
    let v1 : SMV m := b i - b j
    let v2 : SMV m := b j - b k
    have hv1_span : v1 ∈ Submodule.span (ZMod 3) {u} := by
      apply hdRo7SmAxis_neg_one_mem_span hr
      rw [show v1 = b i - b j from rfl, map_sub, hσb i, hσb j, hfixi, hfixj]
      module
    have hv2_span : v2 ∈ Submodule.span (ZMod 3) {u} := by
      apply hdRo7SmAxis_neg_one_mem_span hr
      rw [show v2 = b j - b k from rfl, map_sub, hσb j, hσb k, hfixj, hfixk]
      module
    have hv1i : v1 i = 1 := by
      simp only [v1, hb_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
        sub_zero]
    have hv2i : v2 i = 0 := by
      simp only [v2, hb_apply, Pi.sub_apply, Pi.single_eq_of_ne hij,
        Pi.single_eq_of_ne hik, sub_zero]
    have hv1k : v1 k = 0 := by
      simp only [v1, hb_apply, Pi.sub_apply, Pi.single_eq_of_ne hik.symm,
        Pi.single_eq_of_ne hjk.symm, sub_zero]
    have hv2k : v2 k = -1 := by
      simp only [v2, hb_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hjk.symm,
        zero_sub]
    have hind : ∀ p q : ZMod 3, p • v1 + q • v2 = 0 → p = 0 ∧ q = 0 := by
      intro p q hpq
      have hi_eval : (p • v1 + q • v2) i = 0 := by rw [hpq]; rfl
      have hk_eval : (p • v1 + q • v2) k = 0 := by rw [hpq]; rfl
      have hi_eq : p = 0 := by
        simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv1i, hv2i, mul_one, mul_zero,
          add_zero] using hi_eval
      have hk_eq : -q = 0 := by
        simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv1k, hv2k, mul_one, mul_zero,
          zero_add, mul_neg, mul_one] using hk_eval
      exact ⟨hi_eq, neg_eq_zero.mp hk_eq⟩
    exact hdRo7SmAxis_span_contra hv1_span hv2_span hind

private lemma hdRo7SmAxis_axis_raw {m : ℕ} (hN : SUNormalizerLeaf) (hm : m = 7 ∨ m = 8)
    {H : Subgroup (SMGL m)} (hP : ∀ g, SMIsPerm g → g ∈ H)
    (hS : ∀ g ∈ H, g (smOnes m) = smOnes m → ∀ s, SMIsPerm s → SMIsPerm (g * s * g⁻¹)) :
    ∀ p ∈ smRefSet H, (∑ i, p.2 i) = 0 → SMTClass p := by
  rintro ⟨u, w⟩ ⟨r, hrH, hr⟩ hsum
  change (∑ i, w i) = 0 at hsum
  have hrx : r (smOnes m) = smOnes m := by
    rw [hr.2 (smOnes m)]
    have h0 : (smDual w) (smOnes m) = 0 := by
      rw [hdRo7SmAxis_smDual_apply]
      simpa only [smDot, smOnes, mul_one] using hsum
    rw [h0, zero_smul, sub_zero]
  set b : Module.Basis (Fin m) (ZMod 3) (SMV m) := Pi.basisFun (ZMod 3) (Fin m) with hb_def
  have hb_apply : ∀ i, b i = Pi.single i 1 := by intro i; rw [hb_def, Pi.basisFun_apply]
  have hones : SUOnes 3 b = smOnes m := by
    funext j
    rw [SUOnes, smOnes, Finset.sum_apply]
    rw [Finset.sum_eq_single j
      (fun x _ hxj => by simp only [hb_apply, Pi.single_eq_of_ne hxj.symm])
      (fun hj => absurd (Finset.mem_univ j) hj)]
    simp only [hb_apply, Pi.single_eq_same]
  have hsuperSmis : ∀ s : SMGL m, SUPerm 3 b s → SMIsPerm s := by
    intro s hs
    obtain ⟨τ, hτ⟩ := hs
    have hs_eq : s = b.equiv b τ := by
      apply LinearEquiv.toLinearMap_injective
      refine b.ext (fun i => ?_)
      change s (b i) = (b.equiv b τ) (b i)
      rw [hτ i, Module.Basis.equiv_apply]
    rw [hs_eq, hb_def, hdRo7SmAxis_basisFun_equiv]
    exact hdRo7SmAxis_smisPerm_permGL τ.symm
  have hsmisSuper : ∀ s : SMGL m, SMIsPerm s → SUPerm 3 b s := by
    intro s hs
    obtain ⟨τ, hτ⟩ := hs
    have hs_eq : s = hdRo7SmAxis_permGL τ.symm := by
      apply LinearEquiv.toLinearMap_injective
      refine LinearMap.ext (fun v => ?_)
      funext t
      change s v t = (hdRo7SmAxis_permGL τ.symm) v t
      rw [hτ v t, hdRo7SmAxis_permGL_apply]
    refine ⟨τ, fun i => ?_⟩
    rw [hs_eq]
    funext t
    rw [hdRo7SmAxis_permGL_apply, hb_apply, hb_apply]
    by_cases h : τ.symm t = i
    · have ht : t = τ i := (Equiv.symm_apply_eq τ).mp h
      rw [h, ht, Pi.single_eq_same, Pi.single_eq_same]
    · have ht : t ≠ τ i := by
        intro hti; exact h ((Equiv.symm_apply_eq τ).mpr hti)
      rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne ht]
  have hStab : ∀ s, SUPerm 3 b s → SUPerm 3 b (r * s * r⁻¹) := by
    intro s hs
    exact hsmisSuper _ (hS r hrH hrx s (hsuperSmis s hs))
  have hfix : r (SUOnes 3 b) = SUOnes 3 b := by rw [hones]; exact hrx
  have hNapp := hN 3 rfl m (by rcases hm with h | h <;> omega) (by
    rintro ⟨k, hk⟩; rcases hm with h | h <;> omega) (SMV m) b r hStab hfix
  rcases hNapp with hsup | ⟨σ, hσ⟩
  · obtain ⟨τ, hτ⟩ := hsup
    exact hdRo7SmAxis_case_perm hr hτ
  · exact absurd (hdRo7SmAxis_case_neg_false hm hr hrx hb_def hσ) not_false

theorem hdRo7SmAxis_axis {m : ℕ} (hN : SUNormalizerLeaf) (hm : m = 7 ∨ m = 8)
    {H : Subgroup (SMGL m)} (hP : ∀ g, SMIsPerm g → g ∈ H)
    (hS : ∀ g ∈ H, g (smOnes m) = smOnes m → ∀ s, SMIsPerm s → SMIsPerm (g * s * g⁻¹)) :
    ∀ p ∈ smRefSet H, (∑ i, p.2 i) = 0 → SMTClass p :=
  hdRo7SmAxis_axis_raw hN hm hP hS

end CFSG.StandardType.HdRo7SU.Small

end
