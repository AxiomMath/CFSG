module

public import CFSG.Quasithin.Background.GoldschmidtM12SylowCore
public import CFSG.Quasithin.Background.GoldschmidtAutM12L3Even
public import CFSG.Quasithin.Background.GoldschmidtAutM12L3U3
public import CFSG.Quasithin.Background.GoldschmidtAutM12U3Four

public section

namespace CFSG.Quasithin.F6

open Matrix CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag AutM12Recog

namespace M12Sylow

theorem excl64_of_rank_le_four {K : Type} [Group K] [Finite K]
    (hK : ∃ m : ℕ, Odd m ∧ Nat.card K = 2 ^ 6 * m)
    (hr : ∀ (Q : Sylow 2 K) (E : Subgroup K), E ≤ Q → IsElemAbelian 2 E → Nat.card E ≤ 4) :
    Excl64 K := by
  intro T _ _ hT Q n N hQN hcard hA
  obtain ⟨m, hm, hK⟩ := hK
  have h1 := card_sylow_eq hm hK Q
  have h3 := card_mul_two_pow hT (Q : Subgroup K) n N hQN hcard
  rw [h1] at h3
  have hn : 2 ^ n = 1 := by
    have : 2 ^ 6 * 2 ^ n = 2 ^ 6 * 1 := by rw [h3, mul_one]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  have hNc : Nat.card N = Nat.card T := by rw [hcard, hn, mul_one]
  have hNtop : N = ⊤ := Subgroup.eq_top_of_card_eq N hNc
  obtain ⟨E, hE, hE8⟩ := hT.hasE8
  let f : ↥(Q : Subgroup K) →* T := N.subtype.comp hQN.some.toMonoidHom
  have hf : Function.Injective f := N.subtype_injective.comp hQN.some.injective
  have hrange : f.range = N := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (hQN.some y).2
    · intro hx
      exact ⟨hQN.some.symm ⟨x, hx⟩, by simp [f]⟩
  obtain ⟨E', hE'Q, hE'a, hE'c⟩ := exists_elemAbelian_of_embed (Q : Subgroup K) f hf
    (show E ≤ f.range by rw [hrange, hNtop]; exact le_top) hE
  have := hr Q E' hE'Q hE'a
  omega

theorem excl64_psl_three_four {S : Type} [Group S] [Finite S]
    (h : StatedClassicalModel S .PSL 3 2 2) : Excl64 S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK4]; norm_num)
  have hchar : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hK
  let e' : S ≃* projectiveSL 3 K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  have : Finite (projectiveSL 3 K) := Finite.of_equiv S e'.toEquiv
  refine Excl64.of_equiv ?_ e'
  refine excl64_of_hasE16 fun Q => ?_
  obtain ⟨B, -, hB, -, hc, -⟩ := Tab.hasTwoE16_of_surjective (proj 3 K) (proj_surjective 3 K)
    (fun z hz => CFSG.Quasithin.SteinbergCD.pow_three_eq_one_of_mem_scalars
      (proj_eq_one_iff.mp hz)) (hasTwoE16_specialLinear_three hK4) Q
  exact ⟨B, hB, hc⟩

theorem excl64_psl_three_two {S : Type} [Group S] [Finite S]
    (h : StatedClassicalModel S .PSL 3 2 1) : Excl64 S := by
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
  obtain ⟨-, hf, hn, -, -⟩ := h.1
  obtain ⟨r, hr, hmr⟩ := (CFSG.Timmesfeld.Orders.profile_ordA (n := 2) (by omega) hf).two
  have hout := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (τ := .PSL) (Or.inl rfl) (n := 3) (ℓ := 2) (f := 1) (by norm_num) Nat.prime_two le_rfl h).1
  have hout2 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ≤ 2 := by
    have h2 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ∣ 2 := by
      simpa [CFSG.RankThree.OuterOrder.determinantParameter] using hout
    exact Nat.le_of_dvd (by norm_num) h2
  refine excl64_of_outer_le (a := 3) (c := 2) ⟨r, hr, ?_⟩ (by norm_num) (by norm_num) hout2
  have hcard' : Nat.card S = Open.ordA 2 (2 ^ 1) := hcard
  rw [hcard', hmr]

theorem excl64_psu_three_four {S : Type} [Group S] [Finite S]
    (h : StatedClassicalModel S .PSU 3 2 2) : Excl64 S := by
  obtain ⟨φ⟩ := CFSG.RankThree.PartTwo.KFacts.KS21.U34.nonempty_equiv_Y h
  have : Finite CFSG.RankThree.PartTwo.KFacts.KS21.U34.Y := Finite.of_equiv S φ.toEquiv
  have hY : Excl64 CFSG.RankThree.PartTwo.KFacts.KS21.U34.Y :=
    excl64_of_rank_le_four
      ⟨975, by decide, by rw [CFSG.RankThree.PartTwo.KFacts.KS21.U34.card_Y]; norm_num⟩
      U34Rank.rank_le_four
  exact Excl64.of_equiv hY φ

theorem l3_arith {i j a n : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (ha : (2 ^ i) ^ 2 * 2 ^ j = 2 ^ a)
    (han : a + n = 6) (hn : n ≤ 1) (h16 : ¬ 16 ≤ 2 ^ i * 2 ^ j) : i = 2 ∧ j = 1 ∧ n = 1 := by
  have h1 : i * 2 + j = a := by
    have : 2 ^ (i * 2 + j) = 2 ^ a := by rw [← ha, pow_add, pow_mul]
    exact Nat.pow_right_injective le_rfl this
  have h2 : i + j < 4 := by
    by_contra hge
    apply h16
    rw [← pow_add]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (i + j) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem u3_arith {i j a n : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (ha : 2 ^ i * (2 ^ j) ^ 2 = 2 ^ a)
    (han : a + n = 6) (hn : n ≤ 1) (h16 : ¬ 16 ≤ 2 ^ i * 2 ^ j) : i = 1 ∧ j = 2 ∧ n = 1 := by
  have h1 : i + j * 2 = a := by
    have : 2 ^ (i + j * 2) = 2 ^ a := by rw [← ha, pow_add, pow_mul]
    exact Nat.pow_right_injective le_rfl this
  have h2 : i + j < 4 := by
    by_contra hge
    apply h16
    rw [← pow_add]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (i + j) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem mod_eight_of_factorization_two {m : ℕ} (hm : m ≠ 0) (h : m.factorization 2 = 2) :
    m % 8 = 4 := by
  obtain ⟨k, u, hu, hmu⟩ := Nat.exists_eq_two_pow_mul_odd hm
  have h1 : ordProj[2] m = 2 ^ k := ordProj_two_eq hu hmu
  rw [h] at h1
  have hk : k = 2 := (Nat.pow_right_injective le_rfl h1).symm
  obtain ⟨t, ht⟩ := hu
  subst hk
  omega

theorem psl_three_odd_data64 {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : StatedClassicalModel S .PSL 3 p 1) {T : Type} [Group T] [Finite T]
    (hT : TProps64 T) (Q : Sylow 2 S) (n : ℕ) (N : Subgroup T)
    (hQN : Nonempty (↥(Q : Subgroup S) ≃* ↥N)) (hcard : Nat.card T = Nat.card N * 2 ^ n)
    (hA : Nat.card S * 2 ^ n ∣ Nat.card (MulAut S)) : p % 8 = 5 ∧ n = 1 := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hS := h
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  have hKodd : Odd (Nat.card K) := by rw [hK, pow_one]; exact hodd
  let e' : S ≃* projectiveSL 3 K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  have hP : ordProj[2] (Nat.card S) = ordProj[2] (p - 1) ^ 2 * ordProj[2] (p + 1) := by
    rw [Nat.card_congr e'.toEquiv,
      CFSG.Quasithin.SteinbergCD.ordProj_two_card_projectiveSL_three hKodd, hK, pow_one]
  have hout := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (τ := .PSL) (Or.inl rfl) (n := 3) (ℓ := p) (f := 1) (by norm_num) hp le_rfl hS).1
  have hn2 : 2 ^ n ≤ 2 := by
    have h2 := (dvd_card_outer_of_dvd_card_mulAut hA).trans hout
    have hd : CFSG.RankThree.OuterOrder.determinantParameter .PSL 3 (p ^ 1) ∣ 3 :=
      Nat.gcd_dvd_left _ _
    have h3 : 2 ^ n ∣ 2 * CFSG.RankThree.OuterOrder.determinantParameter .PSL 3 (p ^ 1) := by
      simpa using h2
    exact two_pow_le_two_of_dvd hd h3
  have hn1 : n ≤ 1 := by
    by_contra hlt
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hS0 : Nat.card S ≠ 0 := Nat.card_pos.ne'
  obtain ⟨a, m, hm, hcardS⟩ := Nat.exists_eq_two_pow_mul_odd hS0
  have hPa : ordProj[2] (Nat.card S) = 2 ^ a := ordProj_two_eq hm hcardS
  have h3 := card_mul_two_pow hT (Q : Subgroup S) n N hQN hcard
  rw [card_sylow_eq hm hcardS Q, ← pow_add] at h3
  have han : a + n = 6 := Nat.pow_right_injective le_rfl h3
  have hi1 : 1 ≤ (p - 1).factorization 2 :=
    one_le_factorization_two (by omega) (by obtain ⟨k, hk⟩ := hodd; exact ⟨k, by omega⟩)
  have hj1 : 1 ≤ (p + 1).factorization 2 :=
    one_le_factorization_two (by omega) (by obtain ⟨k, hk⟩ := hodd; exact ⟨k + 1, by omega⟩)
  by_cases h16 : 16 ≤ ordProj[2] (p - 1) * ordProj[2] (p + 1)
  · exfalso
    have h16' : 16 ≤ ordProj[2] (Nat.card K ^ 2 - 1) := by
      rw [hK, pow_one, ordProj_two_sq_sub_one hp.one_lt]
      exact h16
    obtain ⟨x, j, hj, hx⟩ := exists_orderOf_two_pow_projectiveSL hKodd h16'
    exact excl64_of_orderOf_sixteen (g := e'.symm x) hj (by rw [MulEquiv.orderOf_eq, hx]) T hT Q
      n N hQN hcard hA
  · have key := l3_arith hi1 hj1 (hP.symm.trans hPa) han hn1 h16
    refine ⟨?_, key.2.2⟩
    have := mod_eight_of_factorization_two (m := p - 1) (by omega) key.1
    omega

section UnitaryThree

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.Steinberg CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.SteinbergCD

variable {p : ℕ} {K : Type} [Field K]

theorem exists_orderOf_two_pow_unitaryPSU' (h : UnitaryFieldData p 1 K) (hp2 : p ≠ 2)
    (h16 : 16 ≤ ordProj[2] (p - 1) * ordProj[2] (p + 1)) :
    ∃ x : unitaryPSU h 3, ∃ j : ℕ, 4 ≤ j ∧ orderOf x = 2 ^ j := by
  have hdet : (1 : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by rw [det_one]; exact one_ne_zero
  obtain ⟨⟨P, hP⟩, -, -, -, h3, h1⟩ := odd_unitary_three_exact_coordinate_and_Sylow_models h hp2
    (bar_one_apply h) hdet (⊥ : Subgroup (SUgram h.bar (1 : Matrix (Fin 3) (Fin 3) K))) bot_le
  have hodd : Odd p := h.prime.odd_of_ne_two hp2
  have key : ∃ g : SUgram h.bar (1 : Matrix (Fin 3) (Fin 3) K), ∃ k : ℕ, 4 ≤ k ∧
      orderOf g = 2 ^ k := by
    have hmod : p % 4 = 1 ∨ p % 4 = 3 := by
      rcases hodd with ⟨m, hm⟩
      omega
    rcases hmod with hq | hq
    ·
      obtain ⟨⟨z, hz⟩, ⟨M, hM⟩, hmodel⟩ := h1 (by rw [pow_one]; exact hq)
      obtain ⟨u, τ, -, -, hou, -⟩ := hmodel M hM z hz
      have hs : ordProj[2] (p + 1) = 2 := ordProj_two_eq_two (by omega)
      rw [hs] at h16
      have hr : 8 ≤ ordProj[2] (p - 1) := by omega
      rw [pow_one] at hou
      refine ⟨u, (p - 1).factorization 2 + 1, ?_, ?_⟩
      · have : 2 ^ 3 ≤ 2 ^ (p - 1).factorization 2 := by simpa using hr
        have := (Nat.pow_le_pow_iff_right (by norm_num)).mp this
        omega
      · rw [hou, pow_succ, mul_comm]
    ·
      obtain ⟨⟨l, hl, hlo⟩, hmodel⟩ := h3 (by rw [pow_one]; exact hq)
      obtain ⟨u, v, τ, -, -, -, hvu, huv, hou, hov, hτ2, -, -, hinj, -, hpg, -, -, -, -⟩ :=
        hmodel P hP l hl hlo
      have hr : ordProj[2] (p - 1) = 2 := ordProj_two_eq_two (by omega)
      rw [hr] at h16
      have hs8 : 8 ≤ ordProj[2] (p + 1) := by omega
      rw [pow_one] at hou
      have hττ : τ⁻¹ = τ := inv_eq_of_mul_eq_one_left (by rw [← sq, hτ2])
      rw [hττ] at hvu
      have hg2 : (u * τ) * (u * τ) = u * v := by
        rw [hvu]
        group
      have hg8 : (u * τ) ^ 8 = u ^ 4 * v ^ 4 := by
        have : (u * τ) ^ 8 = ((u * τ) * (u * τ)) ^ 4 := by
          rw [← sq, ← pow_mul]
        rw [this, hg2, huv.mul_pow]
      have hne : (u * τ) ^ 8 ≠ 1 := by
        rw [hg8]
        intro h41
        have h4s : 4 < ordProj[2] (p ^ 1 + 1) := by rw [pow_one]; omega
        have := @hinj (⟨4, h4s⟩, ⟨4, h4s⟩, ⟨0, by norm_num⟩) (0, 0, 0) (by
          simp [h41])
        have h4 := congrArg (fun x : Fin (ordProj[2] (p ^ 1 + 1)) ×
          Fin (ordProj[2] (p ^ 1 + 1)) × Fin 2 => (x.1 : ℕ)) this
        simp at h4
      have hmem : u * τ ∈ Subgroup.closure {u, v, τ} :=
        Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
      obtain ⟨k, hk, hk'⟩ := exists_orderOf_two_pow hpg hmem hne
      exact ⟨u * τ, k, hk, hk'⟩
  obtain ⟨g, k, hk, hg⟩ := key
  let e₀ := MulEquiv.subgroupCongr (SUgram_one_eq_unitarySU h)
  have hg' : orderOf (e₀ g) = 2 ^ k := by rw [MulEquiv.orderOf_eq, hg]
  obtain ⟨j, hj, hord⟩ := exists_orderOf_two_pow_mk (Z := unitaryScalars h 3)
    (fun z hz => pow_three_eq_one_of_mem_unitaryScalars h hz) hk hg'
  exact ⟨QuotientGroup.mk (e₀ g), j, hj, hord⟩

end UnitaryThree

theorem psu_three_odd_data64 {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : StatedClassicalModel S .PSU 3 p 1) {T : Type} [Group T] [Finite T]
    (hT : TProps64 T) (Q : Sylow 2 S) (n : ℕ) (N : Subgroup T)
    (hQN : Nonempty (↥(Q : Subgroup S) ≃* ↥N)) (hcard : Nat.card T = Nat.card N * 2 ^ n)
    (hA : Nat.card S * 2 ^ n ∣ Nat.card (MulAut S)) : p % 8 = 3 ∧ n = 1 := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hS := h
  obtain ⟨⟨-, -, hadm⟩, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p 1 K :=
    ⟨hp, le_rfl, by rw [hK, ← pow_mul, mul_comm]⟩
  let e' : S ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU 3 :=
    e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by omega)).symm
  have hP : ordProj[2] (Nat.card S) = ordProj[2] (p - 1) * ordProj[2] (p + 1) ^ 2 := by
    rw [Nat.card_congr e'.toEquiv,
      CFSG.Quasithin.SteinbergCD.ordProj_two_card_unitaryPSU_three hU hp2, pow_one]
  have hout := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (τ := .PSU) (Or.inr rfl) (n := 3) (ℓ := p) (f := 1) (by norm_num) hp le_rfl hS).1
  have hn2 : 2 ^ n ≤ 2 := by
    have h2 := (dvd_card_outer_of_dvd_card_mulAut hA).trans hout
    have hd : CFSG.RankThree.OuterOrder.determinantParameter .PSU 3 (p ^ 1) ∣ 3 :=
      Nat.gcd_dvd_left _ _
    have h3 : 2 ^ n ∣ 2 * CFSG.RankThree.OuterOrder.determinantParameter .PSU 3 (p ^ 1) := by
      simpa using h2
    exact two_pow_le_two_of_dvd hd h3
  have hn1 : n ≤ 1 := by
    by_contra hlt
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hS0 : Nat.card S ≠ 0 := Nat.card_pos.ne'
  obtain ⟨a, m, hm, hcardS⟩ := Nat.exists_eq_two_pow_mul_odd hS0
  have hPa : ordProj[2] (Nat.card S) = 2 ^ a := ordProj_two_eq hm hcardS
  have h3 := card_mul_two_pow hT (Q : Subgroup S) n N hQN hcard
  rw [card_sylow_eq hm hcardS Q, ← pow_add] at h3
  have han : a + n = 6 := Nat.pow_right_injective le_rfl h3
  have hi1 : 1 ≤ (p - 1).factorization 2 :=
    one_le_factorization_two (by omega) (by obtain ⟨k, hk⟩ := hodd; exact ⟨k, by omega⟩)
  have hj1 : 1 ≤ (p + 1).factorization 2 :=
    one_le_factorization_two (by omega) (by obtain ⟨k, hk⟩ := hodd; exact ⟨k + 1, by omega⟩)
  by_cases h16 : 16 ≤ ordProj[2] (p - 1) * ordProj[2] (p + 1)
  · exfalso
    obtain ⟨x, j, hj, hx⟩ := exists_orderOf_two_pow_unitaryPSU' hU hp2 h16
    exact excl64_of_orderOf_sixteen (g := e'.symm x) hj (by rw [MulEquiv.orderOf_eq, hx]) T hT Q
      n N hQN hcard hA
  · have key := u3_arith hi1 hj1 (hP.symm.trans hPa) han hn1 h16
    refine ⟨?_, key.2.2⟩
    have := mod_eight_of_factorization_two (m := p + 1) (by omega) key.2.1
    omega

end M12Sylow

end CFSG.Quasithin.F6
