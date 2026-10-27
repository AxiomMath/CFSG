module

public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Timmesfeld.Orders.ClassicalOmega

public section

namespace CFSG.Timmesfeld

open CFSG.Assembly.LowTwoRank CFSG.Open CFSG.Timmesfeld.ClassicalOrders

namespace ClassicalOrders

theorem charP_two_of_card_eq {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])

theorem odd_two_pow_pow_sub_one {f n : ℕ} (hf : 1 ≤ f) (hn : 1 ≤ n) : Odd ((2 ^ f) ^ n - 1) := by
  have h : 2 ∣ (2 ^ f) ^ n := dvd_pow (dvd_pow_self 2 (by omega)) (by omega)
  have h1 : 1 ≤ (2 ^ f) ^ n := Nat.one_le_pow _ _ (by positivity)
  rw [Nat.odd_iff]
  omega

theorem odd_two_pow_pow_add_one {f n : ℕ} (hf : 1 ≤ f) (hn : 1 ≤ n) : Odd ((2 ^ f) ^ n + 1) := by
  have h : 2 ∣ (2 ^ f) ^ n := dvd_pow (dvd_pow_self 2 (by omega)) (by omega)
  rw [Nat.odd_iff]
  omega

theorem gcd_four_eq_one {x : ℕ} (hx : Odd x) : Nat.gcd 4 x = 1 :=
  Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hx)

theorem cast_prod_pow_sub_one {q : ℕ} (hq : 1 ≤ q) (s : Finset ℕ) (g : ℕ → ℕ) :
    ((∏ i ∈ s, (q ^ g i - 1) : ℕ) : ℤ) = ∏ i ∈ s, ((q : ℤ) ^ g i - 1) := by
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
  push_cast
  rfl

end ClassicalOrders

theorem card_statedClassicalModel_two {G : Type} [Group G] {t : StatedLieTag} {n f : ℕ}
    (h : StatedClassicalModel G t n 2 f) :
    (t = .PSL → Nat.card G = ordA (n - 1) (2 ^ f)) ∧
    (t = .PSU → Nat.card G = ordTwistedA (n - 1) (2 ^ f)) ∧
    (t = .PSp → Nat.card G = ordBC n (2 ^ f)) ∧
    (t = .POmegaPlus → Nat.card G = ordD n (2 ^ f)) ∧
    (t = .POmegaMinus → Nat.card G = ordTwistedD n (2 ^ f)) := by
  refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_, fun ht => ?_, fun ht => ?_⟩ <;> subst ht
  · obtain ⟨⟨-, hf, hn, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
    rw [Nat.card_congr e.toEquiv, card_statedProj_statedSL (by omega), hK, ordA,
      Nat.sub_add_cancel (by omega : 1 ≤ n), mul_comm (n - 1) n]
  · obtain ⟨⟨-, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
    rw [Nat.card_congr e.toEquiv, card_statedProj_statedSU Nat.prime_two hf hK (by omega),
      ordTwistedA, Nat.sub_add_cancel (by omega : 1 ≤ n), mul_comm (n - 1) n]
  · obtain ⟨⟨-, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
    have := charP_two_of_card_eq hK
    have hgcd : Nat.gcd 2 (2 ^ f - 1) = 1 :=
      Nat.coprime_two_left.mpr (by simpa using odd_two_pow_pow_sub_one hf (n := 1) le_rfl)
    rw [Nat.card_congr e.toEquiv, card_statedProj_statedSp_of_charTwo, hK, ordBC, hgcd,
      Nat.div_one, sq]
  · obtain ⟨⟨-, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := h
    have := charP_two_of_card_eq hK
    have hz := card_statedProj_statedOmega_quadPlus (K := K) hn
    rw [Nat.card_congr e.toEquiv, ordD, gcd_four_eq_one (odd_two_pow_pow_sub_one hf (by omega)),
      Nat.div_one]
    apply Nat.cast_injective (R := ℤ)
    rw [hz, hK]
    have hq : 1 ≤ (2 ^ f) ^ n := Nat.one_le_pow _ _ (by positivity)
    push_cast [hq, cast_prod_pow_sub_one (Nat.one_le_pow f 2 (by norm_num))]
    rfl
  · obtain ⟨⟨-, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h
    have := charP_two_of_card_eq hK
    have hz := card_statedProj_statedOmega_quadMinus (K := K) hn hirr
    rw [Nat.card_congr e.toEquiv, ordTwistedD,
      gcd_four_eq_one (odd_two_pow_pow_add_one hf (by omega)), Nat.div_one]
    apply Nat.cast_injective (R := ℤ)
    rw [hz, hK]
    push_cast [cast_prod_pow_sub_one (Nat.one_le_pow f 2 (by norm_num))]
    rfl

end CFSG.Timmesfeld
