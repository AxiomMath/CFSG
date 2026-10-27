module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23Z
public import CFSG.Quasithin.Vol2.Ch5Sec2M23Q
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Final
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedAltSevenAlternating

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.QuasithinUnique.L246.C123 (A7 fixU mem_fixU)
open scoped Pointwise

theorem eq_of_two_pow_mul_odd {a b r s : ℕ} (h : 2 ^ a * r = 2 ^ b * s) (hr : ¬ 2 ∣ r)
    (hs : ¬ 2 ∣ s) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exfalso
    obtain ⟨c, rfl⟩ : ∃ c, b = a + (c + 1) := ⟨b - a - 1, by omega⟩
    rw [pow_add, mul_assoc] at h
    have h' := Nat.eq_of_mul_eq_mul_left (by positivity) h
    exact hr ⟨2 ^ c * s, by rw [h', pow_succ]; ring⟩
  · exact hab
  · exfalso
    obtain ⟨c, rfl⟩ : ∃ c, a = b + (c + 1) := ⟨a - b - 1, by omega⟩
    rw [pow_add, mul_assoc] at h
    have h' := Nat.eq_of_mul_eq_mul_left (by positivity) h
    exact hs ⟨2 ^ c * r, by rw [← h', pow_succ]; ring⟩

theorem isConj_of_orderOf_eq_two_A7 {s t : alternatingGroup (Fin 7)} (hs : orderOf s = 2)
    (ht : orderOf t = 2) : IsConj s t :=
  (CFSG.ComponentClassification.UnbalancedAltSeven.isConj_tZero hs).symm.trans
    (CFSG.ComponentClassification.UnbalancedAltSeven.isConj_tZero ht)

theorem eq_one_of_pow_five {σ : Equiv.Perm (Fin 7)} (h5 : σ ^ 5 = 1)
    (hs : ∀ x, σ x ∈ ({3, 4, 5, 6} : Finset (Fin 7)) ↔ x ∈ ({3, 4, 5, 6} : Finset (Fin 7))) :
    σ = 1 := by
  have key : ∀ (p : Fin 7 → Prop) [DecidablePred p] (hp : ∀ x, p (σ x) ↔ p x),
      Fintype.card {x // p x} ≤ 4 → ∀ x, p x → σ x = x := by
    intro p _ hp hcard x hx
    set τ := σ.subtypePerm hp with hτ
    have hτ5 : τ ^ 5 = 1 := by
      rw [hτ, Equiv.Perm.subtypePerm_pow]
      ext y
      simp [h5]
    have h1 : orderOf τ ∣ 5 := orderOf_dvd_of_pow_eq_one hτ5
    have h2 : orderOf τ ∣ (Fintype.card {x // p x}).factorial := by
      rw [← Fintype.card_perm]
      exact orderOf_dvd_card
    have h3 : orderOf τ = 1 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h1 with h | h
      · exact h
      · exfalso
        rw [h] at h2
        have := (Nat.Prime.dvd_factorial (by norm_num : Nat.Prime 5)).mp h2
        omega
    have hτ1 : τ = 1 := orderOf_eq_one_iff.mp h3
    have := congrArg (fun f : Equiv.Perm {x // p x} => (f ⟨x, hx⟩ : {x // p x}).1) hτ1
    simpa [hτ] using this
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ ({3, 4, 5, 6} : Finset (Fin 7))
  · exact key (· ∈ ({3, 4, 5, 6} : Finset (Fin 7))) hs (by decide) x hx
  · exact key (· ∉ ({3, 4, 5, 6} : Finset (Fin 7))) (fun y => not_congr (hs y)) (by decide) x hx

theorem inf_centerOf_ne_bot_of_le {G : Type} [Group G] [Finite G] {T U : Subgroup G}
    (hT : IsPGroup 2 T) (hUT : U ≤ T) (hUn : T ≤ Subgroup.normalizer (U : Set G))
    (hU : U ≠ ⊥) : U ⊓ centerOf T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ U ⊓ centerOf T := ⟨hy.1, y.2, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

theorem mem_zpowers_involution_eq_one_or_eq {G : Type} [Group G] {z y : G}
    (hz : orderOf z = 2) (hy : y ∈ Subgroup.zpowers z) : y = 1 ∨ y = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, hz]
  have h2 : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases h2 with h | h
  · left; rw [h, zpow_zero]
  · right; rw [h, zpow_one]

theorem mem_normalizer_zpowers_of_commute {G : Type} [Group G] {g x : G} (h : g * x = x * g) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  have hc : Commute g x := h
  have hk : ∀ k : ℤ, g * x ^ k * g⁻¹ = x ^ k := fun k => by
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, (hk k).symm⟩
  · rintro ⟨k, hk'⟩
    refine ⟨k, ?_⟩
    have e : y = g⁻¹ * (x ^ k) * g := by
      simp only at hk'
      rw [hk']; group
    rw [e]
    have := hk k
    calc x ^ k = g⁻¹ * (g * x ^ k * g⁻¹) * g := by group
      _ = g⁻¹ * x ^ k * g := by rw [this]

theorem eq_bot_of_mem_normalizer_of_orderOf_seven
    {P : Subgroup A7} (hP : IsPGroup 2 P) {x : A7}
    (hx : orderOf x = 7) (hxP : x ∈ Subgroup.normalizer (P : Set A7)) : P = ⊥ := by
  have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCN : Subgroup.zpowers x ≤ Subgroup.normalizer (P : Set A7) :=
    Subgroup.zpowers_le.mpr hxP
  have hCp : IsPGroup 7 (Subgroup.zpowers x) := by
    have : Nat.card (Subgroup.zpowers x) = 7 ^ 1 := by rw [Nat.card_zpowers, hx]; norm_num
    exact IsPGroup.of_card this
  let _ : MulAction (Subgroup.zpowers x) ↥P := MulAction.compHom ↥P (Subgroup.inclusion hCN)
  have hN21 := CFSG.QuasithinUnique.L246.C123.normalizer_card_of_card_seven
    (Subgroup.zpowers x) (by rw [Nat.card_zpowers, hx])
  have hfix : ∀ p : ↥P, x * (p : A7) * x⁻¹ = p → p = 1 := by
    intro p hp
    have hcomm : (p : A7) * x = x * p := by
      calc (p : A7) * x = x * (p : A7) * x⁻¹ * x := by rw [hp]
        _ = x * p := by group
    have hpN := mem_normalizer_zpowers_of_commute hcomm
    have hd21 : orderOf (p : A7) ∣ 21 := hN21 ▸ Subgroup.orderOf_dvd_natCard _ hpN
    obtain ⟨k, hk⟩ := hP p
    have hd2 : orderOf (p : A7) ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← Subgroup.coe_pow, hk, Subgroup.coe_one]
    have hco : Nat.Coprime (2 ^ k) 21 := Nat.Coprime.pow_left _ (by norm_num)
    have h1 : orderOf (p : A7) = 1 := Nat.eq_one_of_dvd_coprimes hco hd2 hd21
    exact Subtype.ext (orderOf_eq_one_iff.mp h1)
  have hfp : MulAction.fixedPoints (Subgroup.zpowers x) ↥P = {1} := by
    ext p
    rw [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro h
      apply hfix p
      have := h ⟨x, Subgroup.mem_zpowers x⟩
      exact congrArg Subtype.val this
    · rintro rfl c
      apply Subtype.ext
      change (c : A7) * ((1 : ↥P) : A7) * (c : A7)⁻¹ = ((1 : ↥P) : A7)
      simp
  have hmod := hCp.card_modEq_card_fixedPoints ↥P
  have hfc : Nat.card ↑(MulAction.fixedPoints (Subgroup.zpowers x) ↥P) = 1 := by
    rw [hfp, Nat.card_coe_set_eq, Set.ncard_singleton]
  rw [hfc] at hmod
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hdvd : 2 ^ k ∣ 2520 := by
    rw [← hk, ← CFSG.QuasithinUnique.L246.C123.card_A7]
    exact Subgroup.card_subgroup_dvd_card P
  have hk3 : k ≤ 3 := by
    by_contra hk3
    have : 2 ^ 4 ∣ 2520 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at this
  rw [hk] at hmod
  interval_cases k
  · rw [pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq P hk
  · exfalso; norm_num [Nat.ModEq] at hmod
  · exfalso; norm_num [Nat.ModEq] at hmod
  · exfalso
    have hN := CFSG.QuasithinUnique.L246.C123.normalizer_eq_of_card_eight (T := P)
      (by rw [hk]; norm_num)
    have hxP' : x ∈ P := by rw [← hN]; exact hxP
    have := Subgroup.orderOf_dvd_natCard P hxP'
    rw [hx, hk] at this
    norm_num at this

section SL2

variable {F : Type} [Field F]

theorem exists_SL2_col (v : Fin 2 → F) (hv : v ≠ 0) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) F,
      (A : Matrix (Fin 2) (Fin 2) F).mulVec ![1, 0] = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      ext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨⟨!![0, -(v 1)⁻¹; v 1, 0], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two_of]
      simp [h1]
    · ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
  · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two_of]
      simp [h0]
    · ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_SL2_mulVec_eq {v w : Fin 2 → F} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) F, (A : Matrix (Fin 2) (Fin 2) F).mulVec v = w := by
  obtain ⟨B, hB⟩ := exists_SL2_col v hv
  obtain ⟨C, hC⟩ := exists_SL2_col w hw
  refine ⟨C * B⁻¹, ?_⟩
  rw [← hB, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right, hC]

theorem card_fixed_le [Finite F] {A : Matrix (Fin 2) (Fin 2) F} (hA : A ≠ 1) :
    Nat.card {w : Fin 2 → F // A.mulVec w = w} ≤ Nat.card F := by
  obtain ⟨i, j, hij⟩ : ∃ i j, (A - 1) i j ≠ 0 := by
    by_contra h
    push Not at h
    apply hA
    have : A - 1 = 0 := by ext i j; exact h i j
    exact sub_eq_zero.mp this
  have key : ∀ w : Fin 2 → F, A.mulVec w = w →
      (A - 1) i 0 * w 0 + (A - 1) i 1 * w 1 = 0 := by
    intro w hw
    have h1 : (A - 1).mulVec w = 0 := by rw [Matrix.sub_mulVec, Matrix.one_mulVec, hw, sub_self]
    have h2 := congrFun h1 i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h2
  by_cases hq : (A - 1) i 1 = 0
  · have hp : (A - 1) i 0 ≠ 0 := by
      fin_cases j
      · exact hij
      · exact absurd hq hij
    have h0 : ∀ w : {w : Fin 2 → F // A.mulVec w = w}, (w : Fin 2 → F) 0 = 0 := by
      intro w
      have := key w w.2
      rw [hq, zero_mul, add_zero] at this
      exact (mul_eq_zero.mp this).resolve_left hp
    refine Nat.card_le_card_of_injective (fun w => (w : Fin 2 → F) 1) ?_
    intro w w' h
    apply Subtype.ext
    ext k
    fin_cases k
    · simp [h0 w, h0 w']
    · exact h
  · have h1 : ∀ w : {w : Fin 2 → F // A.mulVec w = w},
        (w : Fin 2 → F) 1 = -((A - 1) i 0 * (w : Fin 2 → F) 0) / (A - 1) i 1 := by
      intro w
      have := key w w.2
      field_simp
      linear_combination this
    refine Nat.card_le_card_of_injective (fun w => (w : Fin 2 → F) 0) ?_
    intro w w' h
    apply Subtype.ext
    have h' : (w : Fin 2 → F) 0 = (w' : Fin 2 → F) 0 := h
    ext k
    fin_cases k
    · exact h'
    · show (w : Fin 2 → F) 1 = (w' : Fin 2 → F) 1
      rw [h1 w, h1 w', h']

end SL2

theorem not_isSimpleBenderGroup_of_card {G : Type} [Group G]
    [Finite G] {r : ℕ} (hG : Nat.card G = 2 ^ 7 * r) (hr : ¬ 2 ∣ r) (h5 : 5 ∣ Nat.card G) :
    ¬ CFSG.BenderSuzuki.IsSimpleBenderGroup G := by
  intro hB
  rcases hB with ⟨⟨n, hn, ⟨e⟩⟩⟩ | ⟨⟨n, hn, ⟨e⟩⟩⟩ |
      ⟨⟨n, hn, E, hEfield, hEfinite, J, hJ, hEcard, hfixedCard, ⟨e⟩⟩⟩
  ·
    have hc := CFSG.BenderSuzuki.lemma114_psl2Binary_card_formula n (by omega)
    rw [← Nat.card_congr e.toEquiv] at hc
    have hodd : ¬ 2 ∣ (2 ^ n) ^ 2 - 1 := by
      have h4 : 4 ≤ (2 ^ n) ^ 2 := by
        have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
        nlinarith
      have : Odd ((2 ^ n) ^ 2 - 1) := Nat.Even.sub_odd (by omega)
        (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩) odd_one
      exact fun h2 => (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h2)
    have h7 := eq_of_two_pow_mul_odd (hG.symm.trans hc) hr hodd
    subst h7
    rw [hc] at h5
    norm_num at h5
  ·
    have hc := CFSG.BenderSuzuki.lemma114_suzukiMatrixGroup_card_formula n (by omega)
    rw [← Nat.card_congr e.toEquiv] at hc
    set q := 2 ^ (2 * n + 1) with hq
    have hq2 : 2 ≤ q := Nat.le_self_pow (by omega) 2
    have hodd : ¬ 2 ∣ (q ^ 2 + 1) * (q - 1) := by
      have hqe : Even q := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      have h1 : Odd (q ^ 2 + 1) := (Nat.even_pow.mpr ⟨hqe, by norm_num⟩).add_one
      have h2 : Odd (q - 1) := Nat.Even.sub_odd (by omega) hqe odd_one
      have := Nat.odd_mul.mpr ⟨h1, h2⟩
      exact fun h2 => (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h2)
    have hq2' : q ^ 2 = 2 ^ (2 * (2 * n + 1)) := by rw [hq, ← pow_mul, mul_comm]
    have e2 : Nat.card G = 2 ^ (2 * (2 * n + 1)) * ((q ^ 2 + 1) * (q - 1)) := by
      rw [hc, ← hq2']
      ring
    have := eq_of_two_pow_mul_odd (hG.symm.trans e2) hr hodd
    omega
  ·
    let : Field E := hEfield
    let : Finite E := hEfinite
    set q := 2 ^ n with hq
    rcases CFSG.BenderSuzuki.External.huppert_II_10_12 J q (by simpa [q] using hEcard)
        (by simpa [q] using hfixedCard) hJ with
      ⟨_, _rho, _pinf, _hrho, _hnatural, _hUcard, _hroot, _htwo, hcard, _hthree⟩
    rw [← Nat.card_congr e.toEquiv] at hcard
    set d := Nat.gcd 3 (q + 1) with hd
    set A := (q ^ 3 + 1) * (q ^ 2 - 1) with hA
    have hq2 : 4 ≤ q := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hqe : Even q := Nat.even_pow.mpr ⟨even_two, by omega⟩
    have hAodd : Odd A := by
      have h1 : Odd (q ^ 3 + 1) := (Nat.even_pow.mpr ⟨hqe, by norm_num⟩).add_one
      have h2 : Odd (q ^ 2 - 1) := Nat.Even.sub_odd (by nlinarith)
        (Nat.even_pow.mpr ⟨hqe, by norm_num⟩) odd_one
      exact Nat.odd_mul.mpr ⟨h1, h2⟩
    have hq_factor : (q + 1) * (q - 1) = q ^ 2 - 1 := by
      have hq_le_sq : q ≤ q * q := by nlinarith
      rw [add_mul, one_mul, Nat.mul_sub_left_distrib]
      simp only [mul_one, pow_two]
      omega
    have hdA : d ∣ A := by
      have : d ∣ q ^ 2 - 1 := dvd_trans (Nat.gcd_dvd_right 3 (q + 1)) ⟨q - 1, hq_factor.symm⟩
      exact dvd_mul_of_dvd_right this (q ^ 3 + 1)
    have hcard' : Nat.card G = 2 ^ (3 * n) * (A / d) := by
      rw [hcard]
      calc (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) = q ^ 3 * A / d := by
            congr 1
            simp only [hA]
            ring
        _ = q ^ 3 * (A / d) := Nat.mul_div_assoc _ hdA
        _ = 2 ^ (3 * n) * (A / d) := by rw [hq, ← pow_mul, mul_comm n 3]
    have hodd : ¬ 2 ∣ A / d := by
      intro h2
      obtain ⟨c, hc⟩ := hdA
      have hd0 : 0 < d := Nat.gcd_pos_of_pos_left _ (by norm_num)
      have : A / d = c := by rw [hc, Nat.mul_div_cancel_left _ hd0]
      rw [this] at h2
      have : 2 ∣ A := hc ▸ dvd_mul_of_dvd_right h2 d
      exact (Nat.not_even_iff_odd.mpr hAodd) (even_iff_two_dvd.mpr this)
    have := eq_of_two_pow_mul_odd (hG.symm.trans hcard') hr hodd
    omega

theorem isStronglyEmbedded_of_conj {G : Type} [Group G] [Finite G] {Y : Subgroup G} {z : G}
    (hY : Y ≠ ⊤) (hzY : z ∈ Y) (hz : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution z)
    (hC : Subgroup.centralizer ({z} : Set G) ≤ Y)
    (hconj : ∀ t ∈ Y, CFSG.BenderSuzuki.PFAppendixIII.IsInvolution t → ∃ y ∈ Y, y * t * y⁻¹ = z) :
    CFSG.BenderSuzuki.IsStronglyEmbedded Y := by
  refine ⟨hY, ⟨z, hzY, hz⟩, ?_⟩
  intro g hg x hxY hxg hx
  have hxmap : x ∈ Y.map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa [CFSG.BenderSuzuki.PFchapter1section1.rightConjugate, Subgroup.conjBy] using hxg
  obtain ⟨y, hyY, hyx⟩ := hxmap
  have hgx : g * x * g⁻¹ = y := by
    rw [← hyx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hgxY : g * x * g⁻¹ ∈ Y := hgx ▸ hyY
  have hgxi : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution (g * x * g⁻¹) := by
    refine ⟨fun h => hx.1 ?_, ?_⟩
    · calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · rw [← MulAut.conj_apply, ← map_pow, hx.2, map_one]
  obtain ⟨a, haY, ha⟩ := hconj x hxY hx
  obtain ⟨b, hbY, hb⟩ := hconj (g * x * g⁻¹) hgxY hgxi
  have hc : b * g * a⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have h1 : (b * g * a⁻¹) * z * (b * g * a⁻¹)⁻¹ = z := by
      calc (b * g * a⁻¹) * z * (b * g * a⁻¹)⁻¹ =
            (b * g * a⁻¹) * (a * x * a⁻¹) * (b * g * a⁻¹)⁻¹ := by rw [ha]
        _ = b * (g * x * g⁻¹) * b⁻¹ := by group
        _ = z := hb
    calc z * (b * g * a⁻¹) = (b * g * a⁻¹) * z * (b * g * a⁻¹)⁻¹ * (b * g * a⁻¹) := by
          rw [h1]
      _ = b * g * a⁻¹ * z := by group
  have hcY := hC hc
  apply hg
  have : g = b⁻¹ * (b * g * a⁻¹) * a := by group
  rw [this]
  exact Y.mul_mem (Y.mul_mem (Y.inv_mem hbY) hcY) haY

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_of_isSylowTwoOf {T Y : Subgroup G} (hT : IsSylowTwoOf T Y) {x : G}
    (hxY : x ∈ Y) (hx : orderOf x = 2) : ∃ y ∈ Y, y * x * y⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx'2 : orderOf (⟨x, hxY⟩ : ↥Y) = 2 := by rw [Subgroup.orderOf_mk]; exact hx
  have hP : IsPGroup 2 (Subgroup.zpowers (⟨x, hxY⟩ : ↥Y)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx'2, pow_one])
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  have hTs : CFSG.Quasithin.IsSylowIn 2 T Y := ⟨hT.1, hT.2.1, hT.2.2⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Y S hTs.toSylow
  refine ⟨g, g.2, ?_⟩
  have hmem : g * (⟨x, hxY⟩ : ↥Y) * g⁻¹ ∈ (hTs.toSylow : Subgroup ↥Y) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨⟨x, hxY⟩, hS (Subgroup.mem_zpowers _), by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  rw [CFSG.Quasithin.IsSylowIn.coe_toSylow, Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

omit [Finite G] in
theorem card_left_eq_960_of_isAmalgamOfGroup
    {G1 G2 : Subgroup G}
    (hα : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups G1 G2) (IsLieOverTwo .PSL 3 2)) :
    Nat.card G1 = 960 := by
  rcases isParabolicIsoData_of_isAmalgamOfGroup hα with ⟨φ₁, -, -, -⟩ | ⟨-, φ₂, -, -⟩
  · rw [← Nat.card_congr φ₁.toEquiv, Asc94.card_m22TwoStab]
  · rw [← Nat.card_congr φ₂.toEquiv, M22Witt.card_m22PtHexStab]

theorem isBlock_L_of (h526 : Stmt5_2_6) (hsp : Stmt5_2_8_special)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hn : n = 2) (hlt : oTwoUpper H < M2) (hmax : quasithinIsMaximalLocal T M2) :
    IsBlock2 L L ∧ IsLin2Type L n := by
  obtain ⟨-, -, -, -, -, hcases, -, -⟩ := h526 G T M L V H B D L₂ n hyp
  unfold Cases5_2_6 at hcases
  rcases hcases with c1 | c2 | c3 | c4 | c5 | c6 | c7
  · exact ⟨c1.2.1, c1.2.2.1⟩
  · exact ⟨c2.2.1, c2.2.2.1⟩
  · exact (hsp G T M L V H B D L₂ n hyp M2 hlt hmax (Or.inl c3)).elim
  · exact (hsp G T M L V H B D L₂ n hyp M2 hlt hmax (Or.inr (Or.inl c4))).elim
  · obtain ⟨-, -, -, ⟨a, ha, -⟩, -⟩ := c5
    omega
  · obtain ⟨m, -, h2n, -⟩ := c6
    omega
  · exact absurd c7.1 (by omega)

theorem setting_K_facts (h526 : Stmt5_2_6)
    (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special)
    (hQ : Stmt5_2_8_Q) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) :
    n = 2 ∧ IsLin2Type (oTwoUpper H) 2 ∧ pCoreOf 2 (oTwoUpper H) = pCoreOf 2 M2 ∧
      blockU (oTwoUpper H) = pCoreOf 2 M2 ∧
      Nat.card (((oTwoUpper H).subgroupOf M2).map π) = 60 := by
  have h := hyp.toHyp5_0_1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM2 : oTwoUpper H ≤ M2 := hS.K_lt.le
  have hLin := isLin2Type_oTwoUpper_of h526 h1284 hSz hU4 hsp hyp hM23 hS.K_lt hS.maximal
  have hcardK := card_eq_of_isLin2Type hLin
  have hU2 : IsPGroup 2 (pCoreOf 2 M2) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M2
  have hUN : M2 ≤ Subgroup.normalizer (pCoreOf 2 M2 : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M2)
  obtain ⟨hn2, h60, hQU⟩ :=
    pCoreOf_le_of_card_eq hS.ker_eq hS.range_eq hU2 hKM2 hUN h.two_le hcardK
  subst hn2
  obtain ⟨-, -, -, -, -, -, hKT, hab⟩ := h526 G T M L V H B D L₂ 2 hyp
  have hKS : pCoreOf 2 (oTwoUpper H ⊔ sec52S M H) = pCoreOf 2 (oTwoUpper H) := by
    rcases hab with ⟨-, -, -, h1⟩ | ⟨m, -, h2n, -⟩
    · exact h1
    · omega
  have hTM2 := hS.T_le
  have hTs : IsSylowTwoOf T M2 := isSylowTwoOf_of_isSylowTwo hyp.sylow hTM2
  have hUT : pCoreOf 2 M2 ≤ T := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTs
  have hKTN : oTwoUpper H ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 M2 : Set G) :=
    sup_le (hKM2.trans hUN) (hTM2.trans hUN)
  have hUKT : pCoreOf 2 M2 ≤ pCoreOf 2 (oTwoUpper H ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hUT.trans le_sup_right) hKTN hU2
  rw [hKT, hKS] at hUKT
  have hQeq : pCoreOf 2 (oTwoUpper H) = pCoreOf 2 M2 := le_antisymm hQU hUKT
  obtain ⟨-, hU16, -⟩ := hQ G T M L V H B D L₂ 2 M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  have hUQ : blockU (oTwoUpper H) ≤ pCoreOf 2 (oTwoUpper H) := by
    show ⁅pCoreOf 2 (oTwoUpper H), oTwoUpper H⁆ ≤ pCoreOf 2 (oTwoUpper H)
    rw [Subgroup.commutator_le]
    intro q hq k hk
    have hKN : oTwoUpper H ≤ Subgroup.normalizer (pCoreOf 2 (oTwoUpper H) : Set G) :=
      Subgroup.le_normalizer.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (oTwoUpper H))
    have h1 : k * q⁻¹ * k⁻¹ ∈ pCoreOf 2 (oTwoUpper H) :=
      (Subgroup.mem_normalizer_iff.mp (hKN hk) _).mp ((pCoreOf 2 (oTwoUpper H)).inv_mem hq)
    rw [commutatorElement_def]
    have h2 := (pCoreOf 2 (oTwoUpper H)).mul_mem hq h1
    simpa [mul_assoc] using h2
  have hU16' : 16 ≤ Nat.card ↥(blockU (oTwoUpper H)) := by
    obtain ⟨F, _, _, hF, -, -, -, β, hβ, -, -⟩ := hLin
    have h1 := Nat.card_le_card_of_surjective β hβ
    rw [Nat.card_eq_fintype_card (α := Multiplicative (Fin 2 → F)), Fintype.card_multiplicative,
      Fintype.card_fun, Fintype.card_fin, hF] at h1
    simpa using h1
  refine ⟨rfl, hLin, hQeq, ?_, h60⟩
  apply Subgroup.eq_of_le_of_card_ge (hUQ.trans hQeq.le)
  rw [hU16]
  exact hU16'

theorem setting_L_facts
    (h526 : Stmt5_2_6) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4)
    (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) :
    IsBlock2 L L ∧ IsLin2Type L 2 ∧ Nat.card ↥(pCoreOf 2 L) = 16 ∧ blockU L = pCoreOf 2 L ∧
      Nat.card L = 960 := by
  obtain ⟨hn2, -, -, -, -⟩ := setting_K_facts h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  subst hn2
  obtain ⟨hbl, hLin⟩ := isBlock_L_of h526 hsp hyp rfl hS.K_lt hS.maximal
  have hcardL := card_eq_of_isLin2Type hLin
  have e60 : 2 ^ 2 * ((2 ^ 2) ^ 2 - 1) = 60 := by norm_num
  rw [e60] at hcardL
  have hG1 : Nat.card ↥(L ⊔ (sec52S M H ⊓ L) ⊔ (B ⊓ oTwoUpper H)) = 960 :=
    card_left_eq_960_of_isAmalgamOfGroup hM23.1
  have hLdvd : Nat.card L ∣ 960 := hG1 ▸ Subgroup.card_dvd_of_le (le_sup_left.trans le_sup_left)
  have hUQ : blockU L ≤ pCoreOf 2 L := by
    show ⁅pCoreOf 2 L, L⁆ ≤ pCoreOf 2 L
    rw [Subgroup.commutator_le]
    intro q hq k hk
    have hKN : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
    have h1 : k * q⁻¹ * k⁻¹ ∈ pCoreOf 2 L :=
      (Subgroup.mem_normalizer_iff.mp (hKN hk) _).mp ((pCoreOf 2 L).inv_mem hq)
    rw [commutatorElement_def]
    have h2 := (pCoreOf 2 L).mul_mem hq h1
    simpa [mul_assoc] using h2
  have hU16 : 16 ≤ Nat.card ↥(blockU L) := by
    obtain ⟨F, _, _, hF, -, -, -, β, hβ, -, -⟩ := hLin
    have h1 := Nat.card_le_card_of_surjective β hβ
    rw [Nat.card_eq_fintype_card (α := Multiplicative (Fin 2 → F)), Fintype.card_multiplicative,
      Fintype.card_fun, Fintype.card_fin, hF] at h1
    simpa using h1
  have hO16 : Nat.card ↥(pCoreOf 2 L) = 16 := by
    have h1 := Subgroup.card_le_of_le hUQ
    rw [hcardL] at hLdvd
    have h2 : Nat.card ↥(pCoreOf 2 L) ∣ 16 := by
      have : 60 * Nat.card ↥(pCoreOf 2 L) ∣ 60 * 16 := by
        rw [show (60 : ℕ) * 16 = 960 by norm_num]
        exact hLdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    have h3 := Nat.le_of_dvd (by norm_num) h2
    omega
  refine ⟨hbl, hLin, hO16, Subgroup.eq_of_le_of_card_ge hUQ (by rw [hO16]; exact hU16), ?_⟩
  rw [hcardL, hO16]

theorem normalizer_pCoreOf_eq (hQ : Stmt5_2_8_Q) (h5211 : Stmt5_2_11_four)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) : Subgroup.normalizer (pCoreOf 2 M2 : Set G) = M2 := by
  have hInM := h5211 G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  obtain ⟨-, hU16, -⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  have hU1 : pCoreOf 2 M2 ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hU16
    norm_num at hU16
  refine hInM.1.2 _ ⟨pCoreOf 2 M2, hU1, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M2, rfl⟩ ?_
  exact Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M2)

theorem pCoreOf_centralizer_eq_of_setting
    (hQ : Stmt5_2_8_Q) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) {z : G}
    (hz2 : orderOf z = 2) (hzT : centerOf T = Subgroup.zpowers z) (hzU : z ∈ pCoreOf 2 M2) :
    pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) = pCoreOf 2 M2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hab, -, -⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  have hcomm : ∀ a ∈ pCoreOf 2 M2, ∀ b ∈ pCoreOf 2 M2, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hab.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hTM2 := hS.T_le
  have hzZ : z ∈ centerOf T := hzT ▸ Subgroup.mem_zpowers z
  have hzc : ∀ t ∈ T, t * z = z * t := fun t ht =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzZ).2 t ht
  have memGz : ∀ g : G, g ∈ Subgroup.centralizer ({z} : Set G) ↔ z * g = g * z := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      exact h z rfl
    · intro h w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact h
  have hTGz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    (memGz t).mpr (hzc t ht).symm
  have hzGz : z ∈ Subgroup.centralizer ({z} : Set G) := (memGz z).mpr rfl
  have hzR : Subgroup.zpowers z ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.zpowers_le.mpr hzGz) (fun g hg => mem_normalizer_zpowers_of_commute ?_) ?_
    · exact ((memGz g).mp hg).symm
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one])
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    norm_num at hz2
  have hR1 : pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ := by
    intro hb
    have : z ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := hzR (Subgroup.mem_zpowers z)
    rw [hb, Subgroup.mem_bot] at this
    exact hz1 this
  have hchar : CharTwo (Subgroup.centralizer ({z} : Set G)) :=
    charTwo_of_inH' hyp.qtke hyp.sylow ⟨hTGz, hR1⟩
  set Gz := Subgroup.centralizer ({z} : Set G) with hGz
  set R := pCoreOf 2 Gz with hRdef
  have hRGz : R ≤ Gz := CFSG.LieType.BorelTits.pCoreOf_le 2 Gz
  have hGzR : Gz ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Gz)
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Gz
  have hTs : IsSylowTwoOf T Gz := isSylowTwoOf_of_isSylowTwo hyp.sylow hTGz
  have hRT : R ≤ T := CFSG.Quasithin.IsSylowIn.le_of_normal ⟨hTs.1, hTs.2.1, hTs.2.2⟩ hRGz
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hRGz).mpr hGzR) hR2
  have hRM2 : R ≤ M2 := hRT.trans hTM2
  obtain ⟨π', ρ, hsurj, hker, hinj, hρ, hU16, hU2, hT8, hUT, -⟩ :=
    exists_rho_of_setting hQ hyp hM23 hS
  let _ := commGroupOfComm (pCoreOf 2 M2) hcomm
  have hz'1 : (⟨z, hzU⟩ : ↥(pCoreOf 2 M2)) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hz'fix : (⟨z, hzU⟩ : ↥(pCoreOf 2 M2)) ∈ fixU ρ ((T.subgroupOf M2).map π') := by
    rw [mem_fixU]
    rintro _ ⟨t, ht, rfl⟩
    apply Subtype.ext
    rw [hρ]
    have h1 := hzc t (Subgroup.mem_subgroupOf.mp ht)
    show (t : G) * z * (t : G)⁻¹ = z
    rw [h1, mul_inv_cancel_right]
  obtain ⟨x, hx7, hxz⟩ :=
    CFSG.QuasithinUnique.L246.C123.exists_order_seven_fixing ρ hU16 hinj hT8 hz'1 hz'fix
  obtain ⟨g, rfl⟩ := hsurj x
  have hgz : (g : G) ∈ Gz := by
    have h1 : (g : G) * z * (g : G)⁻¹ = z := by
      have := congrArg Subtype.val hxz
      rw [hρ] at this
      exact this
    rw [memGz]
    calc z * (g : G) = (g : G) * z * (g : G)⁻¹ * g := by rw [h1]
      _ = g * z := by group
  have hPbot : (R.subgroupOf M2).map π' = ⊥ := by
    refine eq_bot_of_mem_normalizer_of_orderOf_seven ?_ hx7 ?_
    · exact (hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRM2).symm).map π'
    · apply CFSG.QuasithinUnique.L246.C123.mem_normalizer_of_conj_le
      rintro _ ⟨r, hr, rfl⟩
      refine ⟨g * r * g⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp [map_mul, map_inv]⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hGzR hgz) _).mp (Subgroup.mem_subgroupOf.mp hr)
  have hRU : R ≤ pCoreOf 2 M2 := by
    intro r hr
    have h1 : π' ⟨r, hRM2 hr⟩ ∈ (R.subgroupOf M2).map π' :=
      ⟨⟨r, hRM2 hr⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
    rw [hPbot, Subgroup.mem_bot] at h1
    have h2 : (⟨r, hRM2 hr⟩ : ↥M2) ∈ π'.ker := h1
    rw [hker, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hUR : pCoreOf 2 M2 ≤ R := by
    intro u hu
    apply hchar
    refine Subgroup.mem_inf.mpr ⟨(memGz u).mpr (hcomm z hzU u hu), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact hcomm r (hRU hr) u hu
  exact le_antisymm hRU hUR

theorem centralizer_le_of_setting
    (hQ : Stmt5_2_8_Q) (h5211 : Stmt5_2_11_four) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) {z : G}
    (hz2 : orderOf z = 2) (hzT : centerOf T = Subgroup.zpowers z) (hzU : z ∈ pCoreOf 2 M2) :
    Subgroup.centralizer ({z} : Set G) ≤ M2 := by
  have hR := pCoreOf_centralizer_eq_of_setting hQ hyp hM23 hS hz2 hzT hzU
  have hN := normalizer_pCoreOf_eq hQ h5211 hyp hM23 hS
  calc Subgroup.centralizer ({z} : Set G) ≤
        Subgroup.normalizer (pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) : Set G) :=
      Subgroup.le_normalizer.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
    _ = M2 := by rw [hR]; exact hN

theorem card_centralizer_le_four (h526 : Stmt5_2_6)
    (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special)
    (hQ : Stmt5_2_8_Q) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) {v : G} (hv : v ∈ M2)
    (hvU : v ∉ pCoreOf 2 M2) (hv2 : v * v = 1) :
    Nat.card {u : ↥(pCoreOf 2 M2) // v * u * v⁻¹ = u} ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLin, hQeq, hUK, h60⟩ := setting_K_facts h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  obtain ⟨hab, -, -⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  obtain ⟨π', ρ, hsurj, hker, hinj, hρ, hU16, hU2, hT8, hUT, hπ'⟩ :=
    exists_rho_of_setting hQ hyp hM23 hS
  have hcomm : ∀ a ∈ pCoreOf 2 M2, ∀ b ∈ pCoreOf 2 M2, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hab.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUN : M2 ≤ Subgroup.normalizer (pCoreOf 2 M2 : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M2)
  have h60' : Nat.card (((oTwoUpper H).subgroupOf M2).map π') = 60 := by
    rw [← h60]
    have e : (((oTwoUpper H).subgroupOf M2).map π').map (alternatingGroup (Fin 7)).subtype =
        ((oTwoUpper H).subgroupOf M2).map π := by
      rw [Subgroup.map_map]
      congr 1
      exact MonoidHom.ext fun g => hπ' g
    rw [← e, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(((oTwoUpper H).subgroupOf M2).map π')) 2 (by rw [h60']; norm_num)
  obtain ⟨k, hkK, hka⟩ := a.2
  have hk2 : orderOf (π' k) = 2 := by rw [hka, Subgroup.orderOf_coe, ha]
  have hv2' : orderOf (π' ⟨v, hv⟩) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, sq]
      have : (⟨v, hv⟩ : ↥M2) * ⟨v, hv⟩ = 1 := Subtype.ext hv2
      rw [this, map_one]
    · intro h1
      apply hvU
      have : (⟨v, hv⟩ : ↥M2) ∈ π'.ker := h1
      rw [hker, Subgroup.mem_subgroupOf] at this
      exact this
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_orderOf_eq_two_A7 hk2 hv2')
  obtain ⟨m, rfl⟩ := hsurj c
  have hu₁ : ((m * k * m⁻¹ : ↥M2) : G)⁻¹ * v ∈ pCoreOf 2 M2 := by
    have : (m * k * m⁻¹)⁻¹ * ⟨v, hv⟩ ∈ π'.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hc, inv_mul_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at this
    simpa using this
  have hwu : ∀ u ∈ pCoreOf 2 M2, v * u * v⁻¹ = u →
      (m : G) * k * (m : G)⁻¹ * u * ((m : G) * k * (m : G)⁻¹)⁻¹ = u := by
    intro u hu hvu
    have hw : ((m * k * m⁻¹ : ↥M2) : G) = (m : G) * k * (m : G)⁻¹ := by simp
    rw [hw] at hu₁
    set w : G := (m : G) * k * (m : G)⁻¹ with hwdef
    have hc1 := hcomm _ hu₁ u hu
    have h1 : (w⁻¹ * v)⁻¹ * u * (w⁻¹ * v) = u := by
      rw [mul_assoc, ← hc1, inv_mul_cancel_left]
    calc w * u * w⁻¹ = v * ((w⁻¹ * v)⁻¹ * u * (w⁻¹ * v)) * v⁻¹ := by group
      _ = v * u * v⁻¹ := by rw [h1]
      _ = u := hvu
  obtain ⟨F, _, _, hF, α, hαs, hαk, β, hβs, hβk, hβ⟩ := hLin
  have hFc : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, hF]; norm_num
  have hβi : Function.Injective β := by
    have hc : Nat.card ↥(blockU (oTwoUpper H)) ≤ Nat.card (Multiplicative (Fin 2 → F)) := by
      rw [hUK, hU16, Nat.card_eq_fintype_card (α := Multiplicative (Fin 2 → F)),
        Fintype.card_multiplicative, Fintype.card_fun, Fintype.card_fin, hF]
      norm_num
    exact (hβs.bijective_of_nat_card_le hc).1
  have hk1 : (α ⟨k, Subgroup.mem_subgroupOf.mp hkK⟩ : Matrix (Fin 2) (Fin 2) F) ≠ 1 := by
    intro h1
    have h2 : α ⟨k, Subgroup.mem_subgroupOf.mp hkK⟩ = 1 := Subtype.ext h1
    have h3 : (⟨k, Subgroup.mem_subgroupOf.mp hkK⟩ : ↥(oTwoUpper H)) ∈
        CFSG.pCore 2 ↥(oTwoUpper H) := by
      rw [← hαk]
      exact h2
    have h4 : (k : G) ∈ pCoreOf 2 (oTwoUpper H) := by
      exact ⟨_, h3, rfl⟩
    rw [hQeq] at h4
    have h5 : k ∈ π'.ker := by rw [hker, Subgroup.mem_subgroupOf]; exact h4
    rw [MonoidHom.mem_ker] at h5
    rw [h5, orderOf_one] at hk2
    norm_num at hk2
  have hUmem : ∀ u : ↥(pCoreOf 2 M2), (m : G)⁻¹ * u * m ∈ blockU (oTwoUpper H) := by
    intro u
    rw [hUK]
    have := (Subgroup.mem_normalizer_iff.mp (hUN (M2.inv_mem m.2)) u).mp u.2
    simpa using this
  let f : {u : ↥(pCoreOf 2 M2) // v * u * v⁻¹ = u} →
      {x : Fin 2 → F //
        (α ⟨k, Subgroup.mem_subgroupOf.mp hkK⟩ : Matrix (Fin 2) (Fin 2) F).mulVec x = x} :=
    fun u => ⟨Multiplicative.toAdd (β ⟨(m : G)⁻¹ * u.1 * m, hUmem u.1⟩), by
      have hfix : (k : G) * ((m : G)⁻¹ * u.1 * m) * (k : G)⁻¹ = (m : G)⁻¹ * u.1 * m := by
        have h1 := hwu u.1 u.1.2 u.2
        have e : (k : G) * ((m : G)⁻¹ * u.1 * m) * (k : G)⁻¹ =
            (m : G)⁻¹ * ((m : G) * k * (m : G)⁻¹ * u.1 * ((m : G) * k * (m : G)⁻¹)⁻¹) * m := by
          group
        rw [e, h1]
      exact (hβ ⟨k, Subgroup.mem_subgroupOf.mp hkK⟩ ⟨(m : G)⁻¹ * u.1 * m, hUmem u.1⟩
        ⟨(m : G)⁻¹ * u.1 * m, hUmem u.1⟩ hfix.symm).symm⟩
  have hf : Function.Injective f := by
    intro u u' h
    have h1 : β ⟨(m : G)⁻¹ * u.1 * m, hUmem u.1⟩ = β ⟨(m : G)⁻¹ * u'.1 * m, hUmem u'.1⟩ :=
      Multiplicative.toAdd.injective (congrArg Subtype.val h)
    have h2 : (m : G)⁻¹ * u.1 * m = (m : G)⁻¹ * u'.1 * m := congrArg Subtype.val (hβi h1)
    have h3 : (u.1 : G) = u'.1 := by
      calc (u.1 : G) = m * ((m : G)⁻¹ * u.1 * m) * (m : G)⁻¹ := by group
        _ = m * ((m : G)⁻¹ * u'.1 * m) * (m : G)⁻¹ := by rw [h2]
        _ = u'.1 := by group
    exact Subtype.ext (Subtype.ext h3)
  calc Nat.card {u : ↥(pCoreOf 2 M2) // v * u * v⁻¹ = u} ≤
        Nat.card {x : Fin 2 → F //
          (α ⟨k, Subgroup.mem_subgroupOf.mp hkK⟩ : Matrix (Fin 2) (Fin 2) F).mulVec x = x} :=
      Nat.card_le_card_of_injective f hf
    _ ≤ Nat.card F := card_fixed_le hk1
    _ = 4 := hFc

theorem exists_conj_of_mul_involution (h526 : Stmt5_2_6)
    (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special)
    (hQ : Stmt5_2_8_Q) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) {v : G} (hv : v ∈ M2)
    (hvU : v ∉ pCoreOf 2 M2) (hv2 : v * v = 1) {u₀ : G} (hu₀ : u₀ ∈ pCoreOf 2 M2)
    (h2 : u₀ * v * (u₀ * v) = 1) : ∃ u ∈ pCoreOf 2 M2, u * v * u⁻¹ = u₀ * v := by
  have hC4 := card_centralizer_le_four h526 h1284 hSz hU4 hsp hQ hyp hM23 hS hv hvU hv2
  obtain ⟨hab, hU16, -⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  have hcomm : ∀ a ∈ pCoreOf 2 M2, ∀ b ∈ pCoreOf 2 M2, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hab.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hexp : ∀ a ∈ pCoreOf 2 M2, a * a = 1 := fun a ha => by
    have := hab.2 a ha
    rwa [sq] at this
  have hinv : ∀ a ∈ pCoreOf 2 M2, a⁻¹ = a := fun a ha => by
    rw [inv_eq_iff_mul_eq_one]
    exact hexp a ha
  have hUN : M2 ≤ Subgroup.normalizer (pCoreOf 2 M2 : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M2)
  have hvn : ∀ a ∈ pCoreOf 2 M2, v * a * v⁻¹ ∈ pCoreOf 2 M2 := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp (hUN hv) a).mp ha
  let f : ↥(pCoreOf 2 M2) →* ↥(pCoreOf 2 M2) :=
    { toFun := fun u => ⟨u * (v * (u : G)⁻¹ * v⁻¹),
        (pCoreOf 2 M2).mul_mem u.2 (hvn _ ((pCoreOf 2 M2).inv_mem u.2))⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have hX := hvn _ ((pCoreOf 2 M2).inv_mem a.2)
        have hY := hvn _ ((pCoreOf 2 M2).inv_mem b.2)
        calc (a : G) * b * (v * ((a : G) * b)⁻¹ * v⁻¹) =
              a * b * ((v * (b : G)⁻¹ * v⁻¹) * (v * (a : G)⁻¹ * v⁻¹)) := by group
          _ = a * b * ((v * (a : G)⁻¹ * v⁻¹) * (v * (b : G)⁻¹ * v⁻¹)) := by
              rw [hcomm _ hY _ hX]
          _ = a * (b * (v * (a : G)⁻¹ * v⁻¹)) * (v * (b : G)⁻¹ * v⁻¹) := by group
          _ = a * ((v * (a : G)⁻¹ * v⁻¹) * b) * (v * (b : G)⁻¹ * v⁻¹) := by
              rw [hcomm _ b.2 _ hX]
          _ = a * (v * (a : G)⁻¹ * v⁻¹) * (b * (v * (b : G)⁻¹ * v⁻¹)) := by group }
  have hf : ∀ u : ↥(pCoreOf 2 M2), ((f u : ↥(pCoreOf 2 M2)) : G) = u * (v * (u : G)⁻¹ * v⁻¹) :=
    fun u => rfl
  have hkerf : ∀ u : ↥(pCoreOf 2 M2), u ∈ f.ker ↔ v * (u : G) * v⁻¹ = u := by
    intro u
    rw [MonoidHom.mem_ker, Subtype.ext_iff, hf, Subgroup.coe_one]
    constructor
    · intro h
      have h1 : v * (u : G)⁻¹ * v⁻¹ = (u : G)⁻¹ := by
        calc v * (u : G)⁻¹ * v⁻¹ = (u : G)⁻¹ * (u * (v * (u : G)⁻¹ * v⁻¹)) := by group
          _ = (u : G)⁻¹ := by rw [h, mul_one]
      calc v * (u : G) * v⁻¹ = (v * (u : G)⁻¹ * v⁻¹)⁻¹ := by group
        _ = u := by rw [h1, inv_inv]
    · intro h
      calc (u : G) * (v * (u : G)⁻¹ * v⁻¹) = u * (v * (u : G) * v⁻¹)⁻¹ := by group
        _ = 1 := by rw [h, mul_inv_cancel]
  have hrange : ∀ u : ↥(pCoreOf 2 M2),
      v * ((f u : ↥(pCoreOf 2 M2)) : G) * v⁻¹ = f u := by
    intro u
    rw [hf]
    have hx := hvn _ u.2
    have e1 : v * ((u : G) * (v * (u : G)⁻¹ * v⁻¹)) * v⁻¹ =
        (v * (u : G) * v⁻¹) * (v * v) * (u : G)⁻¹ * (v * v)⁻¹ := by group
    have e2 : (u : G) * (v * (u : G)⁻¹ * v⁻¹) = u * (v * (u : G) * v⁻¹)⁻¹ := by group
    rw [e1, e2, hv2, mul_one, inv_one, mul_one, hinv _ u.2, hinv _ hx]
    exact hcomm _ hx _ u.2
  have hcardker : Nat.card f.ker ≤ 4 := by
    have : Nat.card f.ker = Nat.card {u : ↥(pCoreOf 2 M2) // v * u * v⁻¹ = u} :=
      Nat.card_congr (Equiv.subtypeEquivRight hkerf)
    rw [this]
    exact hC4
  have hmul : Nat.card f.ker * Nat.card f.range = 16 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, hU16]
  have hrange4 : 4 ≤ Nat.card f.range := by
    by_contra hlt
    push Not at hlt
    have : Nat.card f.ker * Nat.card f.range ≤ 4 * 3 :=
      Nat.mul_le_mul hcardker (by omega)
    omega
  set Cs : Set ↥(pCoreOf 2 M2) := {u | v * (u : G) * v⁻¹ = u} with hCs
  have hsub : (f.range : Set ↥(pCoreOf 2 M2)) ⊆ Cs := by
    rintro _ ⟨u, rfl⟩
    exact hrange u
  have hCcard : Cs.ncard ≤ 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hC4
  have heq : (f.range : Set ↥(pCoreOf 2 M2)) = Cs := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq (f.range : Set ↥(pCoreOf 2 M2))]
    exact hCcard.trans hrange4
  have hvinv : v⁻¹ = v := by
    rw [inv_eq_iff_mul_eq_one]
    exact hv2
  have hu₀C : (⟨u₀, hu₀⟩ : ↥(pCoreOf 2 M2)) ∈ Cs := by
    show v * u₀ * v⁻¹ = u₀
    have h3 : v * u₀ * v = u₀⁻¹ := by
      calc v * u₀ * v = u₀⁻¹ * (u₀ * v * (u₀ * v)) := by group
        _ = u₀⁻¹ := by rw [h2, mul_one]
    rw [hvinv, h3, hinv _ hu₀]
  rw [← heq] at hu₀C
  obtain ⟨u, hu⟩ := hu₀C
  refine ⟨u, u.2, ?_⟩
  have h4 : (u : G) * (v * (u : G)⁻¹ * v⁻¹) = u₀ := by
    rw [← hf, hu]
  calc (u : G) * v * (u : G)⁻¹ = (u : G) * (v * (u : G)⁻¹ * v⁻¹) * v := by group
    _ = u₀ * v := by rw [h4]

theorem exists_conj_of_isLin2Type {L : Subgroup G} (hLin : IsLin2Type L 2)
    (hU16 : Nat.card ↥(blockU L) = 16) (hLN : L ≤ Subgroup.normalizer (blockU L : Set G))
    {x y : G} (hx : x ∈ blockU L) (hy : y ∈ blockU L) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ ℓ ∈ L, ℓ * x * ℓ⁻¹ = y := by
  obtain ⟨F, _, _, hF, α, hαs, -, β, hβs, -, hβ⟩ := hLin
  have hβi : Function.Injective β := by
    have hc : Nat.card ↥(blockU L) ≤ Nat.card (Multiplicative (Fin 2 → F)) := by
      rw [hU16, Nat.card_eq_fintype_card (α := Multiplicative (Fin 2 → F)),
        Fintype.card_multiplicative, Fintype.card_fun, Fintype.card_fin, hF]
      norm_num
    exact (hβs.bijective_of_nat_card_le hc).1
  have hne : ∀ (w : G) (hw : w ∈ blockU L), w ≠ 1 → Multiplicative.toAdd (β ⟨w, hw⟩) ≠ 0 := by
    intro w hw hw1 h
    apply hw1
    have h1 : β ⟨w, hw⟩ = 1 := h
    have h2 : (⟨w, hw⟩ : ↥(blockU L)) = 1 := hβi (by rw [h1, map_one])
    exact congrArg Subtype.val h2
  obtain ⟨A, hA⟩ := exists_SL2_mulVec_eq (hne x hx hx1) (hne y hy hy1)
  obtain ⟨ℓ, hℓ⟩ := hαs A
  refine ⟨ℓ, ℓ.2, ?_⟩
  have hmem : (ℓ : G) * x * (ℓ : G)⁻¹ ∈ blockU L :=
    (Subgroup.mem_normalizer_iff.mp (hLN ℓ.2) x).mp hx
  have h1 := hβ ℓ ⟨x, hx⟩ ⟨_, hmem⟩ rfl
  rw [hℓ, hA] at h1
  have h2 : β ⟨_, hmem⟩ = β ⟨y, hy⟩ := Multiplicative.toAdd.injective h1
  exact congrArg Subtype.val (hβi h2)

theorem mem_blockU_of_setting {T M L V H B D L₂ : Subgroup G} {n : ℕ}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hbL : blockU L = pCoreOf 2 L)
    (hO16 : Nat.card ↥(pCoreOf 2 L) = 16) {z : G} (hz2 : orderOf z = 2)
    (hzT : centerOf T = Subgroup.zpowers z) : z ∈ blockU L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hyp.T_le.trans hyp.normal
  have hTO : T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hLO : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hOT : pCoreOf 2 L ≤ T := by
    have hX : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := sup_le hLO hTO
    have hOX : pCoreOf 2 L ≤ L ⊔ T := (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left
    have hTs : IsSylowTwoOf T (L ⊔ T) := isSylowTwoOf_of_isSylowTwo hyp.sylow le_sup_right
    exact CFSG.Quasithin.IsSylowIn.le_of_normal ⟨hTs.1, hTs.2.1, hTs.2.2⟩ hOX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hOX).mpr hX)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hne : pCoreOf 2 L ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hO16
    norm_num at hO16
  have h := inf_centerOf_ne_bot_of_le hyp.sylow.1 hOT hTO hne
  rw [hzT] at h
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  have hy1' : y ≠ 1 := fun h' => hy1 (Subtype.ext h')
  rcases mem_zpowers_involution_eq_one_or_eq hz2 (Subgroup.mem_inf.mp hy).2 with h1 | h1
  · exact absurd h1 hy1'
  · rw [hbL, ← h1]
    exact (Subgroup.mem_inf.mp hy).1

theorem exists_mem_blockU_not_mem
    (h526 : Stmt5_2_6) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4)
    (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q) (h5211 : Stmt5_2_11_four)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) : ∃ v ∈ blockU L, v ∉ pCoreOf 2 M2 := by
  obtain ⟨-, -, hO16, hbL, hcardL⟩ :=
    setting_L_facts h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  obtain ⟨-, hU16, -⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  obtain ⟨π', ρ, hsurj, hker, hinj, hρ, -, hU2, hT8, hUT, -⟩ :=
    exists_rho_of_setting hQ hyp hM23 hS
  by_contra hcon
  push Not at hcon
  have hO : pCoreOf 2 L = pCoreOf 2 M2 := by
    rw [← hbL]
    exact Subgroup.eq_of_le_of_card_ge (fun v hv => hcon v hv) (by rw [hU16, hbL, hO16])
  have hN := normalizer_pCoreOf_eq hQ h5211 hyp hM23 hS
  have hMM2 : M ≤ M2 := by
    rw [← hN, ← hO]
    exact hyp.normal.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hU1 : pCoreOf 2 M2 ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hU16
    norm_num at hU16
  have hM2loc : IsTwoLocal M2 :=
    ⟨pCoreOf 2 M2, hU1, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M2, hN.symm⟩
  have hM2M : M2 = M := hyp.maxTwoLocal.2 M2 hM2loc hMM2
  have hLM2 : L ≤ M2 := hM2M ▸ hyp.L_le
  have hLn : M2 ≤ Subgroup.normalizer (L : Set G) := hM2M ▸ hyp.normal
  have hLnorm : (L.subgroupOf M2).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM2).mpr hLn
  have hPn : ((L.subgroupOf M2).map π').Normal := hLnorm.map π' hsurj
  have hcardLM2 : Nat.card (L.subgroupOf M2) = 960 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM2).toEquiv, hcardL]
  have := CFSG.QuasithinUnique.L246.C123.isSimple_A7
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L.subgroupOf M2).map π') with hb | ht
  · have hLU : L ≤ pCoreOf 2 M2 := by
      intro l hl
      have h1 : π' ⟨l, hLM2 hl⟩ ∈ (L.subgroupOf M2).map π' :=
        ⟨_, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
      rw [hb, Subgroup.mem_bot] at h1
      have h2 : (⟨l, hLM2 hl⟩ : ↥M2) ∈ π'.ker := h1
      rw [hker, Subgroup.mem_subgroupOf] at h2
      exact h2
    have h3 := Subgroup.card_le_of_le hLU
    rw [hcardL, hU16] at h3
    norm_num at h3
  · have h1 : Nat.card ((L.subgroupOf M2).map π') ≤ Nat.card (L.subgroupOf M2) :=
      Nat.card_le_card_of_surjective _ (π'.subgroupMap_surjective (L.subgroupOf M2))
    rw [ht, Subgroup.card_top, CFSG.QuasithinUnique.L246.C123.card_A7, hcardLM2] at h1
    norm_num at h1

theorem exists_conj_eq_of_involution
    (h526 : Stmt5_2_6) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4)
    (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q) (h5211 : Stmt5_2_11_four)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) {z : G} (hz2 : orderOf z = 2)
    (hzT : centerOf T = Subgroup.zpowers z) (hzU : z ∈ pCoreOf 2 M2) {t : G}
    (ht : t ∈ L ⊔ M2) (ht2 : orderOf t = 2) : ∃ y ∈ L ⊔ M2, y * t * y⁻¹ = z := by
  have hTM2 := hS.T_le
  have hTs : IsSylowTwoOf T (L ⊔ M2) :=
    isSylowTwoOf_of_isSylowTwo hyp.sylow (hTM2.trans le_sup_right)
  obtain ⟨y₁, hy₁, hy₁t⟩ := exists_conj_mem_of_isSylowTwoOf hTs ht ht2
  have ht'2 : orderOf (y₁ * t * y₁⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact ht2
  suffices h : ∃ y ∈ L ⊔ M2, y * (y₁ * t * y₁⁻¹) * y⁻¹ = z by
    obtain ⟨y, hy, hyt⟩ := h
    refine ⟨y * y₁, (L ⊔ M2).mul_mem hy hy₁, ?_⟩
    rw [← hyt]
    group
  set t' := y₁ * t * y₁⁻¹ with ht'
  have ht'M2 : t' ∈ M2 := hTM2 hy₁t
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    norm_num at hz2
  have ht'1 : t' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht'2
    norm_num at ht'2
  by_cases ht'U : t' ∈ pCoreOf 2 M2
  · obtain ⟨g, hg, hgt⟩ :=
      stmt5_2_12_transitive_of hQ hyp hM23 hS t' ht'U z hzU ht'1 hz1
    exact ⟨g, Subgroup.mem_sup_right hg, hgt⟩
  obtain ⟨hbl, hLin, hO16, hbL, hcardL⟩ :=
    setting_L_facts h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hzbL := mem_blockU_of_setting hyp hbL hO16 hz2 hzT
  obtain ⟨v, hvbL, hvU⟩ := exists_mem_blockU_not_mem h526 h1284 hSz hU4 hsp hQ h5211 hyp hM23 hS
  have hv2 : v * v = 1 := by
    have := hbl.1.2.2.1.2 v hvbL
    rwa [sq] at this
  have hv1 : v ≠ 1 := fun h => hvU (h ▸ (pCoreOf 2 M2).one_mem)
  have hLN : L ≤ Subgroup.normalizer (blockU L : Set G) := by
    rw [hbL]
    exact Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  obtain ⟨ℓ, hℓ, hℓv⟩ :=
    exists_conj_of_isLin2Type hLin (by rw [hbL, hO16]) hLN hvbL hzbL hv1 hz1
  have hvT : v ∈ T := by
    have hTs' : IsSylowTwoOf T M := isSylowTwoOf_of_isSylowTwo hyp.sylow hyp.T_le
    have hTL : T ≤ Subgroup.normalizer (L : Set G) := hyp.T_le.trans hyp.normal
    have hX : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      sup_le (Subgroup.le_normalizer.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
        (hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
    have hOX : pCoreOf 2 L ≤ L ⊔ T :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left
    have hTs'' : IsSylowTwoOf T (L ⊔ T) := isSylowTwoOf_of_isSylowTwo hyp.sylow le_sup_right
    have hOT : pCoreOf 2 L ≤ T := CFSG.Quasithin.IsSylowIn.le_of_normal
      ⟨hTs''.1, hTs''.2.1, hTs''.2.2⟩ hOX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hOX).mpr hX)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    exact hOT (hbL ▸ hvbL)
  have hvM2 : v ∈ M2 := hTM2 hvT
  obtain ⟨π', ρ, hsurj, hker, hinj, hρ, hU16, hU2, hT8, hUT, hπ'⟩ :=
    exists_rho_of_setting hQ hyp hM23 hS
  have hinvo : ∀ (s : G) (hs : s ∈ M2), s ∉ pCoreOf 2 M2 → s * s = 1 →
      orderOf (π' ⟨s, hs⟩) = 2 := by
    intro s hs hsU hss
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, sq]
      have : (⟨s, hs⟩ : ↥M2) * ⟨s, hs⟩ = 1 := Subtype.ext hss
      rw [this, map_one]
    · intro h1
      apply hsU
      have : (⟨s, hs⟩ : ↥M2) ∈ π'.ker := h1
      rw [hker, Subgroup.mem_subgroupOf] at this
      exact this
  have ht't' : t' * t' = 1 := by rw [← sq, ← ht'2, pow_orderOf_eq_one]
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_orderOf_eq_two_A7
    (hinvo t' ht'M2 ht'U ht't') (hinvo v hvM2 hvU hv2))
  obtain ⟨m, rfl⟩ := hsurj c
  have hu₀ : (m : G) * t' * (m : G)⁻¹ * v⁻¹ ∈ pCoreOf 2 M2 := by
    have : m * ⟨t', ht'M2⟩ * m⁻¹ * (⟨v, hvM2⟩ : ↥M2)⁻¹ ∈ π'.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hc, mul_inv_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at this
    simpa using this
  have e1 : (m : G) * t' * (m : G)⁻¹ * v⁻¹ * v = (m : G) * t' * (m : G)⁻¹ := by group
  have h2 : (m : G) * t' * (m : G)⁻¹ * v⁻¹ * v * ((m : G) * t' * (m : G)⁻¹ * v⁻¹ * v) = 1 := by
    rw [e1]
    calc (m : G) * t' * (m : G)⁻¹ * ((m : G) * t' * (m : G)⁻¹) =
          (m : G) * (t' * t') * (m : G)⁻¹ := by group
      _ = 1 := by rw [ht't']; group
  obtain ⟨u, hu, huv⟩ :=
    exists_conj_of_mul_involution h526 h1284 hSz hU4 hsp hQ hyp hM23 hS hvM2 hvU hv2 hu₀ h2
  rw [e1] at huv
  have hUM2 : pCoreOf 2 M2 ≤ M2 := CFSG.LieType.BorelTits.pCoreOf_le 2 M2
  refine ⟨ℓ * u⁻¹ * m, (L ⊔ M2).mul_mem ((L ⊔ M2).mul_mem (Subgroup.mem_sup_left hℓ)
    (Subgroup.mem_sup_right (M2.inv_mem (hUM2 hu)))) (Subgroup.mem_sup_right m.2), ?_⟩
  calc ℓ * u⁻¹ * (m : G) * t' * (ℓ * u⁻¹ * m)⁻¹ =
        ℓ * (u⁻¹ * ((m : G) * t' * (m : G)⁻¹) * u) * ℓ⁻¹ := by group
    _ = ℓ * v * ℓ⁻¹ := by rw [← huv]; group
    _ = z := hℓv

theorem exists_conj_eq_of_orderOf_two
    (h526 : Stmt5_2_6) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4)
    (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q) (h5211 : Stmt5_2_11_four)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) {z : G} (hz2 : orderOf z = 2)
    (hzT : centerOf T = Subgroup.zpowers z) (hzU : z ∈ pCoreOf 2 M2) {w : G}
    (hw : orderOf w = 2) : ∃ g : G, g * w * g⁻¹ = z := by
  have hTs : IsSylowTwoOf T ⊤ := isSylowTwoOf_of_isSylowTwo hyp.sylow le_top
  obtain ⟨g₁, -, hg₁⟩ := exists_conj_mem_of_isSylowTwoOf hTs (Subgroup.mem_top w) hw
  have hw' : orderOf (g₁ * w * g₁⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hw
  obtain ⟨g₂, -, hg₂⟩ := exists_conj_eq_of_involution h526 h1284 hSz hU4 hsp hQ h5211 hyp hM23
    hS hz2 hzT hzU (Subgroup.mem_sup_right (hS.T_le hg₁)) hw'
  exact ⟨g₂ * g₁, by rw [← hg₂]; group⟩

theorem stmt5_2_13_of
    (hQ : Stmt5_2_8_Q) (h5211 : Stmt5_2_11_four) (h526 : Stmt5_2_6) (h1284 : Lemma128Four)
    (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special) :
    ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ) (M2 : Subgroup G)
      (π : ↥M2 →* Equiv.Perm (Fin 7)), Hyp5_2_4 G T M L V H B D L₂ n →
      IsOfTypeM23 M L H B D T → IsM23Setting T H M2 π →
        ∀ x y : G, orderOf x = 2 → orderOf y = 2 → ∃ g : G, g * x * g⁻¹ = y := by
  intro G _ _ T M L V H B D L₂ n M2 π hyp hM23 hS x y hx hy
  obtain ⟨z, hz2, hzT, hzU⟩ := stmt5_2_12_center_of hQ hyp hM23 hS
  have key : ∀ w : G, orderOf w = 2 → ∃ g : G, g * w * g⁻¹ = z := fun w hw =>
    exists_conj_eq_of_orderOf_two h526 h1284 hSz hU4 hsp hQ h5211 hyp hM23 hS hz2 hzT hzU hw
  obtain ⟨a, ha⟩ := key x hx
  obtain ⟨b, hb⟩ := key y hy
  refine ⟨b⁻¹ * a, ?_⟩
  calc b⁻¹ * a * x * (b⁻¹ * a)⁻¹ = b⁻¹ * (a * x * a⁻¹) * b := by group
    _ = b⁻¹ * (b * y * b⁻¹) * b := by rw [ha, hb]
    _ = y := by group

theorem sup_eq_top_of_setting
    (h526 : Stmt5_2_6) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4)
    (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q) (h5211 : Stmt5_2_11_four)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) : L ⊔ M2 = ⊤ := by
  by_contra hne
  have h := hyp.toHyp5_0_1
  obtain ⟨z, hz2, hzT, hzU⟩ := stmt5_2_12_center_of hQ hyp hM23 hS
  have hC := centralizer_le_of_setting hQ h5211 hyp hM23 hS hz2 hzT hzU
  have hzi : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution z := by
    refine ⟨fun h1 => ?_, by rw [← hz2]; exact pow_orderOf_eq_one z⟩
    rw [h1, orderOf_one] at hz2
    norm_num at hz2
  have hSE : CFSG.BenderSuzuki.IsStronglyEmbedded (L ⊔ M2) := by
    refine isStronglyEmbedded_of_conj hne (Subgroup.mem_sup_right
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 M2) hzU)) hzi (hC.trans le_sup_right) ?_
    intro t ht hti
    exact exists_conj_eq_of_involution h526 h1284 hSz hU4 hsp hQ h5211 hyp hM23 hS hz2 hzT hzU ht
      (orderOf_eq_prime hti.2 hti.1)
  have hB := CFSG.BenderSuzuki.theorem_SE_simple (L ⊔ M2) hSE h.simple
  have hcardT : Nat.card T = 128 := card_eq_128_of_setting hQ hyp hM23 hS
  have hG : Nat.card G = 2 ^ 7 * T.index := by
    rw [← Subgroup.card_mul_index T, hcardT]
    norm_num
  obtain ⟨-, hU16, -⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  have hcardM2 : Nat.card M2 = 2520 * 16 := by
    obtain ⟨-, ⟨α, hα, hαker⟩, -⟩ := hS.excA7
    have h1 := card_eq_card_modO2_mul M2
    have h2 : Nat.card (↥M2 ⧸ CFSG.pCore 2 ↥M2) = 2520 := by
      rw [← card_alternatingGroup_seven]
      exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hαker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα)).toEquiv
    rw [h1, h2, hU16]
  have h5 : 5 ∣ Nat.card G := by
    have := Subgroup.card_subgroup_dvd_card M2
    rw [hcardM2] at this
    exact Dvd.dvd.trans (by norm_num) this
  exact not_isSimpleBenderGroup_of_card hG hyp.sylow.2 h5 hB

theorem le_sup_m23I (h526 : Stmt5_2_6) (h1284 : Lemma128Four)
    (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) : M2 ≤ oTwoUpper H ⊔ m23I M2 π := by
  obtain ⟨-, -, -, -, h60⟩ := setting_K_facts h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  obtain ⟨π', ρ, hsurj, hker, hinj, hρ, hU16, hU2, hT8, hUT, hπ'⟩ :=
    exists_rho_of_setting hQ hyp hM23 hS
  have h60' : Nat.card (((oTwoUpper H).subgroupOf M2).map π') = 60 := by
    rw [← h60]
    have e : (((oTwoUpper H).subgroupOf M2).map π').map (alternatingGroup (Fin 7)).subtype =
        ((oTwoUpper H).subgroupOf M2).map π := by
      rw [Subgroup.map_map]
      congr 1
      exact MonoidHom.ext fun g => hπ' g
    rw [← e, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  set s : Set (Fin 7) := {3, 4, 5, 6} with hs
  set St := MulAction.stabilizer (alternatingGroup (Fin 7)) s with hSt
  set J := (((oTwoUpper H) ⊔ m23I M2 π).subgroupOf M2).map π' with hJ
  have hUI : pCoreOf 2 M2 ≤ m23I M2 π := by
    intro u hu
    refine mem_setStabIn.mpr ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 M2 hu, ?_⟩
    have h1 : (⟨u, CFSG.LieType.BorelTits.pCoreOf_le 2 M2 hu⟩ : ↥M2) ∈ π.ker := by
      rw [hS.ker_eq, Subgroup.mem_subgroupOf]
      exact hu
    rw [MonoidHom.mem_ker] at h1
    rw [h1, one_smul]
  have hStJ : St ≤ J := by
    intro a ha
    obtain ⟨g, rfl⟩ := hsurj a
    refine ⟨g, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_right (mem_setStabIn.mpr ⟨g.2, ?_⟩)), rfl⟩
    rw [← hπ' g]
    exact ha
  have hKJ : ((oTwoUpper H).subgroupOf M2).map π' ≤ J :=
    Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx))
  have hJne : J ≠ St := by
    intro hJS
    have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(((oTwoUpper H).subgroupOf M2).map π')) 5 (by rw [h60']; norm_num)
    have haSt : (a : alternatingGroup (Fin 7)) ∈ St := hJS ▸ hKJ a.2
    have ha5 : orderOf (a : alternatingGroup (Fin 7)) = 5 := by rw [Subgroup.orderOf_coe, ha]
    have hσ : ((a : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) • s = s := haSt
    have hconv : ∀ y : Fin 7, y ∈ ({3, 4, 5, 6} : Finset (Fin 7)) ↔ y ∈ s := by
      intro y
      simp [hs]
    have hmem : ∀ x, ((a : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) x ∈
        ({3, 4, 5, 6} : Finset (Fin 7)) ↔ x ∈ ({3, 4, 5, 6} : Finset (Fin 7)) := by
      intro x
      rw [hconv, hconv]
      constructor
      · intro h1
        rw [← hσ] at h1
        exact Set.smul_mem_smul_set_iff.mp h1
      · intro h1
        have := Set.smul_mem_smul_set
          (a := ((a : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))) h1
        rwa [hσ] at this
    have h5' : ((a : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) ^ 5 = 1 := by
      rw [← Subgroup.coe_pow, ← ha5, pow_orderOf_eq_one, Subgroup.coe_one]
    have h1 := eq_one_of_pow_five h5' hmem
    have h2 : (a : alternatingGroup (Fin 7)) = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at ha5
    norm_num at ha5
  have hsF : s = ((({3, 4, 5, 6} : Finset (Fin 7))) : Set (Fin 7)) := by
    rw [hs]
    ext x
    simp
  have hcoatom := alternatingGroup.isCoatom_stabilizer (α := Fin 7) (s := s)
    ⟨3, by simp [hs]⟩ ⟨0, by simp [hs]⟩
    (by rw [hsF, Set.ncard_coe_finset, Nat.card_eq_fintype_card, Fintype.card_fin]; decide)
  have hJtop : J = ⊤ := hcoatom.2 J (lt_of_le_of_ne hStJ (Ne.symm hJne))
  intro m hm
  have hmJ : π' ⟨m, hm⟩ ∈ J := by
    rw [hJtop]
    exact Subgroup.mem_top _
  obtain ⟨x, hx, hxm⟩ := hmJ
  have hd : x⁻¹ * ⟨m, hm⟩ ∈ π'.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxm, inv_mul_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at hd
  have hdI : ((x⁻¹ * ⟨m, hm⟩ : ↥M2) : G) ∈ m23I M2 π := hUI hd
  have e : m = (x : G) * ((x⁻¹ * ⟨m, hm⟩ : ↥M2) : G) := by simp
  rw [e]
  exact (oTwoUpper H ⊔ m23I M2 π).mul_mem (Subgroup.mem_subgroupOf.mp hx)
    (Subgroup.mem_sup_right hdI)

theorem stmt5_2_21_of
    (hQ : Stmt5_2_8_Q) (h5211 : Stmt5_2_11_four) (h526 : Stmt5_2_6) (h1284 : Lemma128Four)
    (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special) : Stmt5_2_21 := by
  intro G _ _ T M L V H B D L₂ n M2 π hyp hM23 hS
  have htop := sup_eq_top_of_setting h526 h1284 hSz hU4 hsp hQ h5211 hyp hM23 hS
  have hM2I := le_sup_m23I h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hLGx : L ≤ m23Gx T M L H B D :=
    le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
  have hKGx : oTwoUpper H ≤ m23Gx T M L H B D :=
    le_sup_of_le_left (le_sup_of_le_right le_sup_right)
  refine ⟨?_, ?_⟩
  · rw [eq_top_iff, ← htop]
    exact sup_le_sup_right hyp.L_le M2
  · rw [eq_top_iff, ← htop]
    exact sup_le (hLGx.trans le_sup_left) (hM2I.trans (sup_le_sup_right hKGx _))

end CFSG.Quasithin.H13
