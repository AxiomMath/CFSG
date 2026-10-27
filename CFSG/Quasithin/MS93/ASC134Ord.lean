module

public import CFSG.Quasithin.EmptyFaithful.R3c2Hat
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Quasithin.MS93.ASBlocksHat

public section

namespace CFSG.Quasithin.MS93

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

theorem sl3Order_cases {n : ℕ} (hn : 1 ≤ n) :
    (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) = 168 ∨
      60480 ≤ (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) := by
  rcases Nat.eq_or_lt_of_le hn with rfl | h2
  · left
    norm_num
  · right
    have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
    have h3 : 64 ≤ (2 ^ n) ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq 3
    have h2' : 16 ≤ (2 ^ n) ^ 2 := by
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2
    calc 60480 = 64 * 15 * 63 := by norm_num
      _ ≤ (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) := by
        refine Nat.mul_le_mul (Nat.mul_le_mul h3 (by omega)) (by omega)

theorem sl3Order_ne_sp4Order {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k) :
    (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) ≠
      (2 ^ k) ^ 4 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1)) := by
  intro h
  have hA : Odd (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
    (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)).mul
      (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))
  have hB : Odd (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1)) :=
    (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)).mul
      (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))
  have h' : 2 ^ (3 * n) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) =
      2 ^ (4 * k) * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1)) := by
    rw [mul_comm 3 n, mul_comm 4 k, pow_mul, pow_mul, ← mul_assoc, h]
  have h34 := Timmesfeld.Orders.eq_of_two_pow_mul_odd hA hB h'
  have hodd : ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) =
      ((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1) := by
    rw [h34] at h'
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h'
  obtain ⟨m, rfl, rfl⟩ : ∃ m, n = 4 * m ∧ k = 3 * m := ⟨n / 4, by omega, by omega⟩
  have hm : 1 ≤ m := by omega
  have e1 : (2 ^ (4 * m)) ^ 3 = 2 ^ (12 * m) := by rw [← pow_mul]; ring_nf
  have e2 : (2 ^ (3 * m)) ^ 4 = 2 ^ (12 * m) := by rw [← pow_mul]; ring_nf
  have e3 : (2 ^ (4 * m)) ^ 2 = 2 ^ (8 * m) := by rw [← pow_mul]; ring_nf
  have e4 : (2 ^ (3 * m)) ^ 2 = 2 ^ (6 * m) := by rw [← pow_mul]; ring_nf
  rw [e1, e2, e3, e4] at hodd
  have hpos : 0 < 2 ^ (12 * m) - 1 := by
    have : 2 ≤ 2 ^ (12 * m) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (12 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h86 : 2 ^ (8 * m) - 1 = 2 ^ (6 * m) - 1 := Nat.eq_of_mul_eq_mul_right hpos hodd
  have h1 : 1 ≤ 2 ^ (6 * m) := Nat.one_le_two_pow
  have h1' : 1 ≤ 2 ^ (8 * m) := Nat.one_le_two_pow
  have hpow : 2 ^ (8 * m) = 2 ^ (6 * m) := by omega
  have := Nat.pow_right_injective (le_refl 2) hpow
  omega

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_quot_of_isModO2Surj {L : Subgroup G} {Γ : Type} [Group Γ] {α : ↥L →* Γ}
    (h : IsModO2Surj L α) : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card Γ := by
  rw [← h.2]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α h.1).toEquiv

theorem card_statedSL3_eq {F : Type} [Field F] [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n) :
    Nat.card ↥(StatedSL 3 F) = (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) := by
  rw [SectionRank.OddCover.card_statedSL_three, Nat.card_eq_fintype_card, hF]

theorem one_le_of_card_eq_two_pow {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := Fintype.one_lt_card (α := F)
    rw [hF] at this
    norm_num at this
  · exact hn

theorem card_statedSL3_ne {F : Type} [Field F] [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    {m : ℕ} (hm : m = 360 ∨ m = 1080 ∨ m = 6048) : Nat.card ↥(StatedSL 3 F) ≠ m := by
  rw [card_statedSL3_eq hF]
  rcases sl3Order_cases (one_le_of_card_eq_two_pow hF) with h | h <;> omega

theorem not_case2_of_sl3 {M T L : Subgroup G} (h : PUHyp M T L) (h2 : MS93Case2 M L)
    {F : Type} [Field F] [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    {α : ↥L →* ↥(StatedSL 3 F)} (hα : IsModO2Surj L α) : False := by
  obtain ⟨-, β, hβ, hβk, -⟩ := isAltBlockType_of_case2 h h2
  have e1 := card_quot_of_isModO2Surj hα
  have e2 := card_quot_of_isModO2Surj (α := β) ⟨hβ, hβk⟩
  have h360 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  rw [e1, h360] at e2
  exact card_statedSL3_ne hF (Or.inl rfl) e2

theorem not_case3_of_sl3 {M T L : Subgroup G} (h : PUHyp M T L) (h3 : MS93Case3 M T L)
    {F : Type} [Field F] [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    {α : ↥L →* ↥(StatedSL 3 F)} (hα : IsModO2Surj L α) : False := by
  obtain ⟨hVX, k, F', _, _, β, hk, hF', hβ, hn, -⟩ := h3
  have hmod := isModO2Surj_of_natural h hVX inf_le_right hβ hn
  have e := (card_quot_of_isModO2Surj hα).symm.trans (card_quot_of_isModO2Surj hmod)
  rw [card_statedSL3_eq hF, LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
    Nat.card_eq_fintype_card, hF'] at e
  rw [show Finset.Icc 1 2 = {1, 2} from rfl, Finset.prod_pair (by norm_num)] at e
  exact sl3Order_ne_sp4Order (one_le_of_card_eq_two_pow hF) hk (by simpa using e)

theorem not_case6_of_sl3 {M T L : Subgroup G} (h : PUHyp M T L) (h6 : MS93Case6 M L)
    {F : Type} [Field F] [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    {α : ↥L →* ↥(StatedSL 3 F)} (hα : IsModO2Surj L α) : False := by
  obtain ⟨-, hhat, -⟩ := isHatA6Block_of_case6 h h6
  have e1 := card_quot_of_isModO2Surj hα
  rw [R3c2.card_of_isHat_alt6 hhat] at e1
  exact card_statedSL3_ne hF (Or.inr (Or.inl rfl)) e1.symm

theorem not_case10_of_sl3
    {M T L : Subgroup G} (h : PUHyp M T L)
    (h10 : MS93Case10 M L) {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) {α : ↥L →* ↥(StatedSL 3 F)} (hα : IsModO2Surj L α) : False := by
  obtain ⟨-, hpsu, -⟩ := isG2Block_of_case10 h h10
  have e1 := card_quot_of_isModO2Surj hα
  rw [SBc11.card_of_isPSU_three_three hpsu] at e1
  exact card_statedSL3_ne hF (Or.inr (Or.inr rfl)) e1.symm

end CFSG.Quasithin.MS93
