module

public import CFSG.Quasithin.H13.A5S136r
public import CFSG.Quasithin.EmptyFaithful.S153LKsDef
public import CFSG.RankThree.PartOne.D4RC.RxOrder

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.S153L

theorem sl2_ne_u38 (n : ℕ) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 5515776 ∧ 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 16547328 := by
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n <;> norm_num
  · have h1 : 2 ^ 9 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h2 : (2 ^ 9) ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h1 2
    have h3 : 2 ^ 9 * ((2 ^ 9) ^ 2 - 1) ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
      Nat.mul_le_mul h1 (Nat.sub_le_sub_right h2 1)
    norm_num at h3
    omega

theorem sz_ne_u38 {a : ℕ} (ha : 1 ≤ a) :
    (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) ≠ 5515776 ∧
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) ≠ 16547328 := by
  rcases Nat.lt_or_ge a 2 with h | h
  · obtain rfl : a = 1 := by omega
    norm_num
  · have h1 : 2 ^ 5 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (2 ^ 5) ^ 2 ≤ (2 ^ (2 * a + 1)) ^ 2 := Nat.pow_le_pow_left h1 2
    have h3 : (2 ^ 5) ^ 2 * (2 ^ 5 - 1) * ((2 ^ 5) ^ 2 + 1) ≤
        (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h2 (Nat.sub_le_sub_right h1 1)) (Nat.add_le_add_right h2 1)
    norm_num at h3
    omega

theorem su3_eq_u38 {a : ℕ}
    (h : (2 ^ a) ^ 3 * ((2 ^ a) ^ 2 - 1) * ((2 ^ a) ^ 3 + 1) = 5515776 ∨
      (2 ^ a) ^ 3 * ((2 ^ a) ^ 2 - 1) * ((2 ^ a) ^ 3 + 1) = 16547328) :
    a = 3 := by
  rcases Nat.lt_or_ge a 4 with ha | ha
  · interval_cases a <;> first | rfl | (exfalso; norm_num at h)
  · exfalso
    have h1 : 2 ^ 4 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    have h2 : (2 ^ 4) ^ 2 ≤ (2 ^ a) ^ 2 := Nat.pow_le_pow_left h1 2
    have h3 : (2 ^ 4) ^ 3 ≤ (2 ^ a) ^ 3 := Nat.pow_le_pow_left h1 3
    have h4 : (2 ^ 4) ^ 3 * ((2 ^ 4) ^ 2 - 1) * ((2 ^ 4) ^ 3 + 1) ≤
        (2 ^ a) ^ 3 * ((2 ^ a) ^ 2 - 1) * ((2 ^ a) ^ 3 + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h3 (Nat.sub_le_sub_right h2 1)) (Nat.add_le_add_right h3 1)
    norm_num at h4
    omega

theorem sl3_ne_u38 (n : ℕ) :
    (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) ≠ 5515776 ∧
      (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) ≠ 16547328 := by
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> norm_num
  · have h1 : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h2 : (2 ^ 4) ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h1 2
    have h3 : (2 ^ 4) ^ 3 ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left h1 3
    have h4 : (2 ^ 4) ^ 3 * (((2 ^ 4) ^ 2 - 1) * ((2 ^ 4) ^ 3 - 1)) ≤
        (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
      Nat.mul_le_mul h3 (Nat.mul_le_mul (Nat.sub_le_sub_right h2 1) (Nat.sub_le_sub_right h3 1))
    norm_num at h4
    omega

theorem sp4_ne_u38 (n : ℕ) :
    (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) ≠ 5515776 ∧
      (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) ≠ 16547328 := by
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> norm_num
  · have h1 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h2 : (2 ^ 3) ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h1 2
    have h3 : (2 ^ 3) ^ 4 ≤ (2 ^ n) ^ 4 := Nat.pow_le_pow_left h1 4
    have h4 : (2 ^ 3) ^ 4 * (((2 ^ 3) ^ 2 - 1) * ((2 ^ 3) ^ 4 - 1)) ≤
        (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) :=
      Nat.mul_le_mul h3 (Nat.mul_le_mul (Nat.sub_le_sub_right h2 1) (Nat.sub_le_sub_right h3 1))
    norm_num at h4
    omega

section Modules

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}

theorem card_eq_of_nat {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {U Z : Subgroup W}
    (h : (FFModel.nat Γ).Realizes L U Z) : Nat.card ↥L = Nat.card ↥Γ := by
  obtain ⟨π, hπ⟩ := h
  have hinj := realizesVia_injective_of_faithful (FFModel.nat_faithful _) hπ
  exact (Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ.1⟩)).symm

theorem natural_su3_of_types {V : Subgroup W}
    (h : TypesFourShapeNatWSec L V) (hc : Nat.card ↥L = 5515776 ∨ Nat.card ↥L = 16547328) :
    BinaryNaturalSU3 L V (V ⊓ fixV L) 3 ∧ Nat.card ↥L = 16547328 := by
  rcases h with ⟨n, -, K, _, _, hKc, hR⟩ | ⟨f, a, ha, hf, K, _, _, hKc, hR⟩ |
      ⟨a, K, _, _, hKc, hR⟩ | ⟨n, -, K, _, _, hKc, hR⟩ | ⟨n, -, K, _, _, hKc, hR⟩
  ·
    exfalso
    rw [card_eq_of_nat hR, A5.card_statedSL_two, hKc] at hc
    have := sl2_ne_u38 n
    omega
  ·
    exfalso
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hf]; exact hKc
    rw [card_eq_of_nat hR, CFSG.LieType.Ree.suzuki_order hK'] at hc
    have := sz_ne_u38 ha
    omega
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have ha1 : 1 ≤ a := by
      by_contra h0
      have h0 : a = 0 := by omega
      subst h0
      have := Finite.one_lt_card (α := K)
      rw [hKc] at this
      norm_num at this
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (k := 2 * a) (by omega) (by rw [hKc, ← pow_mul, mul_comm])
    have hcL := card_eq_of_nat hR
    rw [CFSG.RankThree.PartOne.D4RC.rcl_card_statedSU_three hKc] at hcL
    rw [hcL] at hc
    have ha3 := su3_eq_u38 hc
    subst ha3
    exact ⟨⟨K, inferInstance, inferInstance, hKc, hR⟩, by rw [hcL]; norm_num⟩
  ·
    exfalso
    rw [card_eq_of_nat hR, A5.card_statedSL_three, hKc] at hc
    have := sl3_ne_u38 n
    omega
  ·
    exfalso
    rw [card_eq_of_nat hR, A5.card_statedSp_two, hKc] at hc
    have := sp4_ne_u38 n
    omega

theorem false_of_d310Two_card_su3 {U C : Subgroup W}
    (hc : Nat.card ↥L = 5515776 ∨ Nat.card ↥L = 16547328)
    (h : (∃ n, BinaryNaturalSL L U C 3 n) ∨ (∃ n, BinaryNaturalSp4 L U C n) ∨
      AlternatingNatural L U C 6 ∨ BinaryNaturalSL L U C 4 1 ∨ BinaryNaturalSL L U C 5 1 ∨
      A7Four L U C) : False := by
  rcases h with ⟨n, K, _, _, hKc, hR⟩ | ⟨n, K, _, _, hKc, hR⟩ | ⟨π, hπ⟩ |
      ⟨K, _, _, hKc, hR⟩ | ⟨K, _, _, hKc, hR⟩ | ⟨α, π, hπ⟩
  ·
    rw [card_eq_of_nat hR, A5.card_statedSL_three, hKc] at hc
    have := sl3_ne_u38 n
    omega
  ·
    rw [card_eq_of_nat hR, A5.card_statedSp_two, hKc] at hc
    have := sp4_ne_u38 n
    omega
  ·
    have h1 := A5.card_le_of_surjective (Γ := ↥(alternatingGroup (Fin 6))) π hπ.1
    rw [Ch1Four.card_alt6 ⟨MulEquiv.refl _⟩] at h1
    omega
  ·
    have h2 : Nat.card ↥(StatedSL 4 K) = 20160 := by
      rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 4 K).toEquiv,
        CFSG.OrderReductions.LinearOrders.card_specialLinear K 4 (by norm_num), hKc]
      decide
    rw [card_eq_of_nat hR, h2] at hc
    omega
  ·
    rw [card_eq_of_nat hR, A5.card_statedSL_five_two (by rw [hKc]; norm_num)] at hc
    omega
  ·
    have h1 := A5.card_le_of_surjective (Γ := ↥(alternatingGroup (Fin 7))) π hπ.1
    rw [Ch1Four.card_alt7 ⟨MulEquiv.refl _⟩] at h1
    omega

end Modules

end CFSG.Quasithin.H13.A6.A6S20
