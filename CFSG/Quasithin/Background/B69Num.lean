module

public import CFSG.Quasithin.Background.E2Two
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinNonIso
import CFSG.Adapters.StatedSmallProjOrders

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.ClassicalOrders

namespace B69

theorem cubic_no (q g : ℕ) (hg : 0 < g) (hg2 : g ≤ 2) (N : ℕ) (hN : N = 20160 ∨ N = 9999360)
    (h : N * g + q = q ^ 3) : False := by
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with rfl | h0
    · rcases hN with rfl | rfl <;> simp at h <;> omega
    · exact h0
  have hsq : q ^ 3 = q * (q * q) := by ring
  interval_cases g <;> rcases hN with rfl | rfl
  · rcases Nat.lt_or_ge q 28 with h1 | h1
    · nlinarith [Nat.mul_le_mul h1.le h1.le]
    · nlinarith [Nat.mul_le_mul h1 h1]
  · rcases Nat.lt_or_ge q 216 with h1 | h1
    · nlinarith [Nat.mul_le_mul h1.le h1.le]
    · nlinarith [Nat.mul_le_mul h1 h1]
  · rcases Nat.lt_or_ge q 35 with h1 | h1
    · nlinarith [Nat.mul_le_mul h1.le h1.le]
    · nlinarith [Nat.mul_le_mul h1 h1]
  · rcases Nat.lt_or_ge q 272 with h1 | h1
    · nlinarith [Nat.mul_le_mul h1.le h1.le]
    · nlinarith [Nat.mul_le_mul h1 h1]

theorem big_three {q g X : ℕ} (hq : 16 ≤ q) (hg : g ≤ 3) (s : ℕ) (hs : s = 1 ∨ s = 2)
    (h : X * g = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ∨ X * g = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) :
    9999360 < X := by
  have h1 : 16 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : 16 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
  have h3 : 16 ^ 3 - 1 ≤ q ^ 3 - 1 := Nat.sub_le_sub_right h1 1
  have h3' : 16 ^ 3 - 1 ≤ q ^ 3 + 1 := by omega
  have h4 : 16 ^ 3 * ((16 ^ 2 - 1) * (16 ^ 3 - 1)) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3')
  have h5 : 16 ^ 3 * ((16 ^ 2 - 1) * (16 ^ 3 - 1)) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  by_contra hX
  push Not at hX
  have h6 : X * g ≤ 9999360 * 3 := Nat.mul_le_mul hX hg
  have _ := hs
  rcases h with h | h <;> norm_num at h4 h5 h6 <;> omega

theorem big_four {q X : ℕ} (hq : 8 ≤ q) (h : X = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) :
    9999360 < X := by
  have h1 : 8 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
  have h2 : 8 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
  have h3 : 8 ^ 4 - 1 ≤ q ^ 4 - 1 := Nat.sub_le_sub_right h1 1
  have h4 : 8 ^ 4 * ((8 ^ 2 - 1) * (8 ^ 4 - 1)) ≤ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  rw [h]
  norm_num at h4
  omega

theorem no_cube_dvd {p N : ℕ} (hp : 5 ≤ p) (hodd : p % 2 = 1) (hN : N = 20160 ∨ N = 9999360)
    (h : p ^ 3 ∣ N) : False := by
  have hle : p ^ 3 ≤ N := Nat.le_of_dvd (by rcases hN with rfl | rfl <;> norm_num) h
  have hp215 : p ≤ 215 := by
    by_contra hlt
    push Not at hlt
    have : 216 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hlt 3
    rcases hN with rfl | rfl <;> omega
  have key : ∀ q ∈ Finset.Icc 5 215, q % 2 = 1 → ¬ q ^ 3 ∣ 20160 ∧ ¬ q ^ 3 ∣ 9999360 := by
    decide +kernel
  have := key p (Finset.mem_Icc.2 ⟨hp, hp215⟩) hodd
  rcases hN with rfl | rfl
  · exact this.1 h
  · exact this.2 h

theorem card_psl_mul_gcd {X : Type} [Group X] {n p e : ℕ} (hn : 2 ≤ n) (h : IsPSL n p e X) :
    Nat.card X * Nat.gcd n (p ^ e - 1) =
      (p ^ e) ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, ((p ^ e) ^ j - 1) := by
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := h
  have e'' : X ≃* StatedProj (StatedSL n K) := e'
  rw [Nat.card_congr e''.toEquiv, card_statedProj_statedSL (by omega), hK]
  apply Nat.div_mul_cancel
  have h1 : Nat.gcd n (p ^ e - 1) ∣ p ^ e - 1 := Nat.gcd_dvd_right _ _
  have h2 : p ^ e - 1 ∣ (p ^ e) ^ 2 - 1 := by simpa using Nat.sub_dvd_pow_sub_pow (p ^ e) 1 2
  have h3 : (p ^ e) ^ 2 - 1 ∣ ∏ j ∈ Finset.Icc 2 n, ((p ^ e) ^ j - 1) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_Icc.2 ⟨le_rfl, hn⟩)
  exact (h1.trans (h2.trans h3)).mul_left _

theorem card_psl_two_mul {X : Type} [Group X] {p e : ℕ} (h : IsPSL 2 p e X) :
    Nat.card X * Nat.gcd 2 (p ^ e - 1) + p ^ e = (p ^ e) ^ 3 := by
  have h1 := card_psl_mul_gcd (by norm_num) h
  have hq : 1 ≤ p ^ e := Nat.one_le_pow _ _ h.1.1.pos
  simp only [Finset.Icc_self, Finset.prod_singleton] at h1
  norm_num at h1
  rw [h1]
  obtain ⟨u, hu⟩ : ∃ u, (p ^ e) ^ 2 = u + 1 := ⟨(p ^ e) ^ 2 - 1, by
    have := Nat.one_le_pow 2 (p ^ e) (by omega); omega⟩
  rw [hu, show (p ^ e) ^ 3 = p ^ e * (p ^ e) ^ 2 by ring, hu]
  simp [Nat.mul_add]

theorem card_psl_three_mul {X : Type} [Group X] {p e : ℕ} (h : IsPSL 3 p e X) :
    Nat.card X * Nat.gcd 3 (p ^ e - 1) =
      (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1)) := by
  have h1 := card_psl_mul_gcd (by norm_num) h
  have : Finset.Icc 2 3 = {2, 3} := by decide
  simpa [this] using h1

theorem card_psu_three_mul {X : Type} [Group X] {p e : ℕ} (h : IsPSU 3 p e X) :
    Nat.card X * Nat.gcd 3 (p ^ e + 1) =
      (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) :=
  CFSG.Open.StatedAPI.card_mul_gcd_of_statedClassicalModel_psu_three h

theorem card_psp_four {X : Type} [Group X] {e : ℕ} (h : IsPSp4 2 e X) :
    Nat.card X = (2 ^ e) ^ 4 * (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 4 - 1)) := by
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := h
  have e'' : X ≃* StatedProj (StatedSp 2 K) := e'
  have := CFSG.QuasithinUnique.Fin257.charP_two_of_card hK
  rw [Nat.card_congr e''.toEquiv, card_statedProj_statedSp_of_charTwo, hK]
  have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hIcc, Finset.prod_pair (by norm_num)]
  norm_num

@[expose] def BadOrder (N : ℕ) : Prop := N = 20160 ∨ N = 9999360

theorem not_psl_two {X : Type} [Group X] {p e : ℕ} (h : IsPSL 2 p e X)
    (hN : BadOrder (Nat.card X)) : False := by
  have h1 := card_psl_two_mul h
  have hg1 : 0 < Nat.gcd 2 (p ^ e - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hg2 : Nat.gcd 2 (p ^ e - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
  exact cubic_no (p ^ e) _ hg1 hg2 _ hN h1

theorem not_isSz
    {X : Type} [Group X] {n : ℕ} (h : IsSz n X) (hN : BadOrder (Nat.card X)) :
    False := by
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := h
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
  have hc : Nat.card X = CFSG.Open.ordSuzuki (2 ^ n) := by
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hF', hfa, CFSG.Open.ordSuzuki]
    exact Nat.mul_right_comm _ _ _
  have hodd : Odd n := ⟨a, by omega⟩
  have h3 : ¬ 3 ∣ CFSG.Open.ordSuzuki (2 ^ n) :=
    CFSG.QuasithinUnique.Fin257.not_three_dvd_suzuki hodd
  rw [← hc] at h3
  rcases hN with h | h <;> rw [h] at h3 <;> omega

theorem not_psu_three_two {X : Type} [Group X] {n : ℕ} (h : IsPSU 3 2 n X)
    (hN : BadOrder (Nat.card X)) : False := by
  have h1 := card_psu_three_mul h
  have hn2 : 2 ≤ n := by
    obtain ⟨-, hf, -, h32⟩ := h.1
    by_contra hlt
    have : n = 1 := by omega
    subst this
    exact h32 (by norm_num)
  have hg : Nat.gcd 3 (2 ^ n + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  rcases Nat.lt_or_ge n 4 with hn4 | hn4
  · interval_cases n
    · norm_num at h1
      rcases hN with h | h <;> omega
    · norm_num at h1
      rcases hN with h | h <;> omega
  · have hq : 16 ≤ 2 ^ n := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn4
    have := big_three hq hg 1 (Or.inl rfl) (Or.inl h1)
    rcases hN with h | h <;> omega

theorem psl_three_two_cases {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n) (h : IsPSL 3 2 n X) :
    Nat.card X ≠ 9999360 ∧ (Nat.card X = 20160 → n = 2) := by
  have h1 := card_psl_three_mul h
  have hg : Nat.gcd 3 (2 ^ n - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  rcases Nat.lt_or_ge n 4 with hn4 | hn4
  · interval_cases n
    · norm_num at h1
      omega
    · norm_num at h1
      omega
    · norm_num at h1
      omega
  · have hq : 16 ≤ 2 ^ n := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn4
    have := big_three hq hg 1 (Or.inl rfl) (Or.inr h1)
    omega

theorem not_isSp4Prime {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n) (h : E2.IsSp4Prime n X)
    (hN : BadOrder (Nat.card X)) : False := by
  unfold E2.IsSp4Prime at h
  split_ifs at h with h1
  · obtain ⟨e⟩ := h
    have hc : Nat.card X = 360 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    rcases hN with h | h <;> omega
  · have hc := card_psp_four h
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · have hn2 : n = 2 := by omega
      subst hn2
      norm_num at hc
      rcases hN with h | h <;> omega
    · have hq : 8 ≤ 2 ^ n := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
      have := big_four hq hc
      rcases hN with h | h <;> omega

theorem coprime_pow_gcd {p g : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hg : g ∣ 3) :
    Nat.Coprime (p ^ 3) g := by
  have h1 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  exact (h1.coprime_dvd_right hg).pow_left 3

theorem not_psl_three_odd {X : Type} [Group X] {p : ℕ} (hp2 : p ≠ 2) (h : IsPSL 3 p 1 X)
    (hN : BadOrder (Nat.card X)) : False := by
  have hpp : p.Prime := h.1.1
  have h1 := card_psl_three_mul h
  rw [pow_one] at h1
  rcases Nat.lt_or_ge p 5 with hp5 | hp5
  · have hp3 : p = 3 := by
      have := hpp.two_le
      interval_cases p
      · exact absurd rfl hp2
      · rfl
      · exact absurd hpp (by norm_num)
    subst hp3
    norm_num at h1
    rcases hN with h | h <;> omega
  · have hcop := coprime_pow_gcd hpp hp5 (Nat.gcd_dvd_left 3 (p - 1))
    have hd : p ^ 3 ∣ Nat.card X * Nat.gcd 3 (p - 1) := by
      rw [h1]; exact Dvd.intro _ rfl
    exact no_cube_dvd hp5 (by have := hpp.eq_two_or_odd; omega) hN (hcop.dvd_of_dvd_mul_right hd)

theorem not_psu_three_odd {X : Type} [Group X] {p : ℕ} (hp2 : p ≠ 2) (h : IsPSU 3 p 1 X)
    (hN : BadOrder (Nat.card X)) : False := by
  have hpp : p.Prime := h.1.1
  have h1 := card_psu_three_mul h
  rw [pow_one] at h1
  rcases Nat.lt_or_ge p 5 with hp5 | hp5
  · have hp3 : p = 3 := by
      have := hpp.two_le
      interval_cases p
      · exact absurd rfl hp2
      · rfl
      · exact absurd hpp (by norm_num)
    subst hp3
    norm_num at h1
    rcases hN with h | h <;> omega
  · have hcop := coprime_pow_gcd hpp hp5 (Nat.gcd_dvd_left 3 (p + 1))
    have hd : p ^ 3 ∣ Nat.card X * Nat.gcd 3 (p + 1) := by
      rw [h1]; exact Dvd.intro _ rfl
    exact no_cube_dvd hp5 (by have := hpp.eq_two_or_odd; omega) hN (hcop.dvd_of_dvd_mul_right hd)

@[expose] def E22Fam (F : Type) [Group F] : Prop :=
  (∃ p e : ℕ, IsPSL 2 p e F) ∨ (∃ n : ℕ, IsSz n F) ∨ (∃ n : ℕ, IsPSU 3 2 n F) ∨
  (∃ n : ℕ, 1 ≤ n ∧ IsPSL 3 2 n F) ∨ (∃ n : ℕ, 1 ≤ n ∧ E2.IsSp4Prime n F) ∨
  (∃ p : ℕ, p ≠ 2 ∧ IsPSU 3 p 1 F) ∨ (∃ p : ℕ, p ≠ 2 ∧ IsPSL 3 p 1 F)

namespace E22Fam

variable {F : Type} [Group F]

theorem card_ne
    (h : E22Fam F) (hN : Nat.card F = 9999360) : False := by
  have hb : BadOrder (Nat.card F) := Or.inr hN
  rcases h with ⟨p, e, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨p, hp, h⟩ | ⟨p, hp, h⟩
  · exact not_psl_two h hb
  · exact not_isSz h hb
  · exact not_psu_three_two h hb
  · exact (psl_three_two_cases hn h).1 hN
  · exact not_isSp4Prime hn h hb
  · exact not_psu_three_odd hp h hb
  · exact not_psl_three_odd hp h hb

theorem exists_psl_three_four
    (h : E22Fam F) (hN : Nat.card F = 20160) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      Nonempty (F ≃* StatedProj (StatedSL 3 K)) := by
  have hb : BadOrder (Nat.card F) := Or.inl hN
  rcases h with ⟨p, e, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨p, hp, h⟩ | ⟨p, hp, h⟩
  · exact (not_psl_two h hb).elim
  · exact (not_isSz h hb).elim
  · exact (not_psu_three_two h hb).elim
  · have h2 := (psl_three_two_cases hn h).2 hN
    subst h2
    obtain ⟨-, K, hK, hfin, hKc, ⟨e⟩⟩ := h
    exact ⟨K, hK, hfin, by rw [hKc]; norm_num, ⟨e⟩⟩
  · exact (not_isSp4Prime hn h hb).elim
  · exact (not_psu_three_odd hp h hb).elim
  · exact (not_psl_three_odd hp h hb).elim

end E22Fam

theorem e22Cases_fam {Γ : Type} [Group Γ] {H T M K : Subgroup Γ} (h : E2.E22Cases H T M K) :
    E22Fam ↥(E2.star M H K) := by
  unfold E2.E22Cases at h
  dsimp only at h
  rcases h with ⟨-, t, -, -, -, h1⟩ | ⟨-, -, h2⟩
  · rcases h1 with ⟨n, -, h1 | h1, -⟩ | ⟨p, -, -, h1, -⟩
    · exact Or.inl ⟨2, n, h1⟩
    · exact Or.inr (Or.inl ⟨n, h1⟩)
    · exact Or.inl ⟨p, 1, h1⟩
  · rcases h2 with ⟨n, ⟨-, h2 | h2 | h2⟩, -⟩ | ⟨n, hn, h2 | h2, -⟩ | ⟨p, e, -, -, -, -, h2, -⟩ |
        ⟨p, -, hp2, h2 | h2, -⟩
    · exact Or.inl ⟨2, n, h2⟩
    · exact Or.inr (Or.inl ⟨n, h2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨n, h2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, h2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, h2⟩))))
    · exact Or.inl ⟨p, e, h2⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp2, h2.2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp2, h2.2.1⟩)))))

end B69

end CFSG.Quasithin
