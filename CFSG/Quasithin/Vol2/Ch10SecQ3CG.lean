module

public import CFSG.Quasithin.Vol2.Ch10SecAShape
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem card_eq_card_mul_card {X T B : Subgroup G} (hT : IsSylowTwoOf T X)
    (hB : Lin2.IsHallTwoPrimeOf B X) : Nat.card X = Nat.card T * Nat.card B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTX, hT2, hTi⟩ := hT
  obtain ⟨hBX, hBo, k, hk⟩ := hB
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hT2
  have h1 : Nat.card T * T.relIndex X = Nat.card X := by
    have h := Subgroup.relIndex_mul_card (H := T) (K := X)
    rw [inf_eq_left.mpr hTX] at h
    rw [mul_comm]
    exact h
  have h2 : Nat.card B * B.relIndex X = Nat.card X := by
    have h := Subgroup.relIndex_mul_card (H := B) (K := X)
    rw [inf_eq_left.mpr hBX] at h
    rw [mul_comm]
    exact h
  have hTo : Odd (T.relIndex X) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hTi)
  rw [hk] at h2
  rw [hj] at h1
  obtain ⟨-, h3⟩ := SecA.two_pow_mul_odd_inj hTo hBo (h1.trans (h2.symm.trans (mul_comm _ _)))
  rw [hj, ← h3, h1]

theorem le_sup_of_hall {X T B : Subgroup G} (hT : IsSylowTwoOf T X)
    (hB : Lin2.IsHallTwoPrimeOf B X) : X ≤ T ⊔ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : T ⊔ B ≤ X := sup_le hT.1 hB.1
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hT.2.1
  have hcop : Nat.Coprime (Nat.card T) (Nat.card B) := by
    rw [hj]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hB.2.1)
  have hdvd : Nat.card X ∣ Nat.card ↥(T ⊔ B) := by
    rw [card_eq_card_mul_card hT hB]
    exact hcop.mul_dvd_of_dvd_of_dvd (Subgroup.card_dvd_of_le le_sup_left)
      (Subgroup.card_dvd_of_le le_sup_right)
  have heq : T ⊔ B = X := Subgroup.eq_of_le_of_card_ge hle
    (Nat.le_of_dvd Nat.card_pos hdvd)
  exact heq.ge

theorem mem_of_odd_of_index {Y : Type*} [Group Y] [Finite Y] {N : Subgroup Y} [N.Normal]
    {i : ℕ} (hi : N.index = 2 ^ i) {y : Y} (hy : Odd (orderOf y)) : y ∈ N := by
  have h1 : y ^ (2 ^ i) ∈ N := hi ▸ N.pow_index_mem y
  have hcop : Nat.Coprime (2 ^ i) (orderOf y) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hy)
  have hb := Nat.gcd_eq_gcd_ab (2 ^ i) (orderOf y)
  rw [hcop.gcd_eq_one, Nat.cast_one] at hb
  have h2 : y = (y ^ (2 ^ i)) ^ (Nat.gcdA (2 ^ i) (orderOf y)) *
      (y ^ orderOf y) ^ (Nat.gcdB (2 ^ i) (orderOf y)) := by
    rw [← zpow_natCast, ← zpow_natCast y (orderOf y), ← zpow_mul, ← zpow_mul, ← zpow_add,
      ← hb, zpow_one]
  rw [h2, pow_orderOf_eq_one, one_zpow, mul_one]
  exact N.zpow_mem h1 _

omit [Finite G] in
theorem eq_one_of_mem_of_odd {Q : Subgroup G} (hQ : IsPGroup 2 Q) {x : G} (hx : x ∈ Q)
    (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
  have h1 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 := orderOf_dvd_of_pow_eq_one h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  rcases j with _ | j
  · exact orderOf_eq_one_iff.mp (by simpa using hj)
  · rw [hj, pow_succ] at hodd
    exact absurd hodd (Nat.not_odd_iff_even.mpr (even_two.mul_left _))

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
