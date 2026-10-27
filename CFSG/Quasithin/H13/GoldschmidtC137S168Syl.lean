module

public import CFSG.Quasithin.H13.GoldschmidtC137SQBurn
public import CFSG.Quasithin.H13.GoldschmidtC137SQU33Sec

public section

namespace CFSG.Quasithin.H13.U3.GC137.SQ.S168

variable {S : Type} [Group S] [Finite S] [IsSimpleGroup S]

omit [IsSimpleGroup S] in
theorem card_sylow (hcard : Nat.card S = 168) (P : Sylow 7 S) : Nat.card P = 7 :=
  card_sylow_seven_of_dvd (by rw [hcard]; norm_num) (by rw [hcard]; norm_num) P

theorem card_sylow_eight (hcard : Nat.card S = 168) (P : Sylow 7 S) :
    Nat.card (Sylow 7 S) = 8 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hP := card_sylow hcard P
  have hindex : (P : Subgroup S).index = 24 := by
    have := (P : Subgroup S).card_mul_index
    rw [hP, hcard] at this
    omega
  have hdvd : Nat.card (Sylow 7 S) ∣ 24 := hindex ▸ P.card_dvd_index
  have hmod : Nat.card (Sylow 7 S) % 7 = 1 := card_sylow_modEq_one (p := 7) (G := S)
  have key : ∀ m ∈ Nat.divisors 24, m % 7 = 1 → m = 1 ∨ m = 8 := by decide +kernel
  rcases key _ (Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩) hmod with h1 | h8
  · exfalso
    have hsub : Subsingleton (Sylow 7 S) := (Nat.card_eq_one_iff_unique.mp h1).1
    have hnormal := Sylow.normal_of_subsingleton P
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup S) with hb | ht
    · rw [hb, Subgroup.card_bot] at hP
      omega
    · rw [ht, Subgroup.card_top, hcard] at hP
      omega
  · exact h8

theorem card_normalizer (hcard : Nat.card S = 168) (P : Sylow 7 S) :
    Nat.card (Subgroup.normalizer (P : Set S)) = 21 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hidx : (Subgroup.normalizer (P : Set S)).index = Nat.card (Sylow 7 S) :=
    (Sylow.card_eq_index_normalizer P).symm
  have hmul := (Subgroup.normalizer (P : Set S)).card_mul_index
  rw [hidx, card_sylow_eight hcard P, hcard] at hmul
  omega

theorem not_comm_normalizer (hcard : Nat.card S = 168) (P : Sylow 7 S) :
    ∃ a ∈ Subgroup.normalizer (P : Set S), ∃ b ∈ Subgroup.normalizer (P : Set S),
      a * b ≠ b * a := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  by_contra hcon
  have h : ∀ a ∈ Subgroup.normalizer (P : Set S), ∀ b ∈ Subgroup.normalizer (P : Set S),
      a * b = b * a := by
    intro a ha b hb
    by_contra hab
    exact hcon ⟨a, ha, b, hb, hab⟩
  refine false_of_normalizer_le_centralizer P (by rw [card_sylow hcard P]; norm_num)
    (by rw [card_sylow hcard P, hcard]; norm_num) ?_
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro h' hh'
  exact h h' (Subgroup.le_normalizer hh') g hg

theorem exists_frobenius (hcard : Nat.card S = 168) (P : Sylow 7 S) :
    ∃ x y : S, x ∈ (P : Subgroup S) ∧ y ∈ Subgroup.normalizer (P : Set S) ∧ orderOf x = 7 ∧
      orderOf y = 3 ∧ y * x * y⁻¹ = x ^ 2 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set N : Subgroup S := Subgroup.normalizer (P : Set S) with hN
  have hPN : (P : Subgroup S) ≤ N := Subgroup.le_normalizer
  obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(P : Subgroup S)) 7
    (by rw [card_sylow hcard P])
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 3
    (by rw [hN, card_normalizer hcard P]; norm_num)
  set x : S := x'.1 with hxdef
  set y : S := y'.1 with hydef
  have hxP : x ∈ (P : Subgroup S) := x'.2
  have hyN : y ∈ N := y'.2
  have hxo : orderOf x = 7 := by
    rw [hxdef, Subgroup.orderOf_coe]
    exact hx'
  have hyo : orderOf y = 3 := by
    rw [hydef, Subgroup.orderOf_coe]
    exact hy'
  have hx7 : x ^ 7 = 1 := hxo ▸ pow_orderOf_eq_one x
  have hy3 : y ^ 3 = 1 := hyo ▸ pow_orderOf_eq_one y
  have hPz : Subgroup.zpowers x = (P : Subgroup S) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxP)
      (by rw [Nat.card_zpowers, hxo, card_sylow hcard P])
  have hconj : y * x * y⁻¹ ∈ Subgroup.zpowers x := by
    rw [hPz]
    exact (Subgroup.mem_normalizer_iff.1 hyN x).1 hxP
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hconj
  obtain ⟨m, hm, hm7⟩ : ∃ m : ℕ, y * x * y⁻¹ = x ^ m ∧ m < 7 := by
    refine ⟨(k % 7).toNat, ?_, by omega⟩
    have hnn : (0 : ℤ) ≤ k % 7 := Int.emod_nonneg k (by norm_num)
    rw [← hk, ← zpow_mod_orderOf, hxo, ← zpow_natCast, Int.toNat_of_nonneg hnn]
    rfl
  have hpow : ∀ n : ℕ, y ^ n * x * (y ^ n)⁻¹ = x ^ (m ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc y ^ (n + 1) * x * (y ^ (n + 1))⁻¹ = y * (y ^ n * x * (y ^ n)⁻¹) * y⁻¹ := by group
        _ = y * x ^ (m ^ n) * y⁻¹ := by rw [ih]
        _ = (y * x * y⁻¹) ^ (m ^ n) := conj_pow.symm
        _ = x ^ (m ^ (n + 1)) := by rw [hm, ← pow_mul, pow_succ, mul_comm]
  have hmod : m ^ 3 % 7 = 1 := by
    have h3 := hpow 3
    rw [hy3, one_mul, inv_one, mul_one] at h3
    have h1 : x ^ 1 = x ^ (m ^ 3) := by rw [pow_one]; exact h3
    have := (pow_eq_pow_iff_modEq).1 h1
    rw [hxo] at this
    exact this.symm
  have hm124 : m = 1 ∨ m = 2 ∨ m = 4 := by
    have key : ∀ m < 7, m ^ 3 % 7 = 1 → m = 1 ∨ m = 2 ∨ m = 4 := by decide
    exact key m hm7 hmod
  have hm1 : m ≠ 1 := by
    intro h1
    have hcomm : y * x = x * y := by
      have := hm
      rw [h1, pow_one] at this
      exact mul_inv_eq_iff_eq_mul.1 this
    set s : Set S := {x, y} with hs
    set K : Subgroup S := Subgroup.closure s with hK
    have hxK : x ∈ K := Subgroup.subset_closure (by simp [hs])
    have hyK : y ∈ K := Subgroup.subset_closure (by simp [hs])
    have hKN : K ≤ N := by
      rw [hK, Subgroup.closure_le]
      intro z hz
      rcases hz with rfl | rfl
      · exact hPN hxP
      · exact hyN
    have h21 : Nat.card K = 21 := by
      have h7K : 7 ∣ Nat.card K := hxo ▸ Subgroup.orderOf_dvd_natCard K hxK
      have h3K : 3 ∣ Nat.card K := hyo ▸ Subgroup.orderOf_dvd_natCard K hyK
      have hdvd : Nat.card K ∣ 21 := by
        have := Subgroup.card_dvd_of_le hKN
        rwa [hN, card_normalizer hcard P] at this
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      have hpos : 0 < Nat.card K := Nat.card_pos
      omega
    have hKeq : K = N :=
      Subgroup.eq_of_le_of_card_ge hKN (by rw [h21, hN, card_normalizer hcard P])
    have hsc : s ⊆ Subgroup.centralizer s := by
      intro z hz
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro w hw
      rcases hz with rfl | rfl <;> rcases hw with rfl | rfl <;>
        first | rfl | exact hcomm.symm | exact hcomm
    have hKc : K ≤ Subgroup.centralizer s := (Subgroup.closure_le _).2 hsc
    obtain ⟨a, ha, b, hb, hab⟩ := not_comm_normalizer hcard P
    rw [← hN, ← hKeq] at ha hb
    apply hab
    have hb' : b ∈ Subgroup.centralizer s := hKc hb
    have ha' := Subgroup.closure_le_centralizer_centralizer s ha
    exact (Subgroup.mem_centralizer_iff.1 ha' b hb').symm
  rcases hm124 with h1 | h2 | h4
  · exact absurd h1 hm1
  · exact ⟨x, y, hxP, hyN, hxo, hyo, by rw [hm, h2]⟩
  · refine ⟨x, y⁻¹, hxP, inv_mem hyN, hxo, by rw [orderOf_inv]; exact hyo, ?_⟩
    have hx8 : x ^ 8 = x := by rw [pow_eq_pow_mod 8 hx7]; norm_num
    have : y * (y⁻¹ * x * y⁻¹⁻¹) * y⁻¹ = y * x ^ 2 * y⁻¹ := by
      calc y * (y⁻¹ * x * y⁻¹⁻¹) * y⁻¹ = x := by group
        _ = x ^ 8 := hx8.symm
        _ = (x ^ 4) ^ 2 := by rw [← pow_mul]
        _ = (y * x * y⁻¹) ^ 2 := by rw [hm, h4]
        _ = y * x ^ 2 * y⁻¹ := conj_pow
    exact mul_left_cancel (mul_right_cancel this)

end CFSG.Quasithin.H13.U3.GC137.SQ.S168
