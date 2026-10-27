module

import CFSG.RankThree.PartOne.S10.EmbeddingTransport
public import CFSG.RankThree.PartTwo.Sec21.Item22Res4ProofFamilies

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

namespace Item228Census2Proof

theorem le_perfectResidual_centralizer {S : Type} [Group S] [Finite S] {y : S}
    {N Kb : Subgroup S} {m : ℕ} (hcomm : ∀ k ∈ N, y * k = k * y) (hKbN : Kb ≤ N)
    (eK : Kb ≃* projSL 2 (GaloisField 2 m)) (hm : 0 < m) (he : Even m) :
    Kb ≤ inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set S)) := by
  have hKp : Group.IsPerfect Kb :=
    isPerfect_of_mulEquiv_projSL (by obtain ⟨r, hr⟩ := he; omega) eK
  refine CFSG.RankThree.PartOne.EmbeddingTransport.le_inSubgroup_perfectResidual_of_isPerfect
    (fun k hk => ?_) hKp
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hcomm k (hKbN hk)).symm

theorem noL2Normal228_of_perfectResidual {S : Type} [Group S] [Finite S]
    (hZ : Subgroup.center S = ⊥)
    (h : ∀ y : S, orderOf y = 3 →
      ¬ 5 ∣ Nat.card (inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set S)))) :
    NoL2Normal228 S := by
  intro y N Kb m hyZ hy3 hcomm _ hKbN ⟨eK⟩ hm he _
  have hy3' : y ^ 3 = 1 := by rwa [hZ, Subgroup.mem_bot] at hy3
  have hy1 : y ≠ 1 := fun h1 => hyZ (h1 ▸ Subgroup.one_mem _)
  have hle := le_perfectResidual_centralizer hcomm hKbN eK hm he
  have h5 : 5 ∣ Nat.card Kb := by
    rw [Nat.card_congr eK.toEquiv]
    exact Item22Res4Proof.five_dvd_card_projSL_two hm he
  exact h y (orderOf_eq_prime hy3' hy1) (h5.trans (Subgroup.card_dvd_of_le hle))

theorem noL2Normal228_of_simple_perfectResidual {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (h : ∀ y : S, orderOf y = 3 →
      ¬ 5 ∣ Nat.card (inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set S)))) :
    NoL2Normal228 S := by
  intro y N Kb m hyZ
  have hZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hb | ht
    · exact hb
    · exact (hyZ (ht ▸ Subgroup.mem_top y)).elim
  exact noL2Normal228_of_perfectResidual hZ h y N Kb m hyZ

theorem two_pow_sq_mod_five {f : ℕ} (hf : Odd f) : (2 ^ f) ^ 2 % 5 = 4 := by
  obtain ⟨k, rfl⟩ := hf
  rw [← pow_mul, show (2 * k + 1) * 2 = 4 * k + 2 by ring, pow_add, pow_mul]
  norm_num [Nat.mul_mod, Nat.pow_mod]

theorem not_five_dvd_two_pow (f : ℕ) : ¬ 5 ∣ 2 ^ f := fun h =>
  absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).mp
    (Nat.prime_five.dvd_of_dvd_pow h)) (by norm_num)

theorem not_five_dvd_two_pow_pow (f k : ℕ) : ¬ 5 ∣ (2 ^ f) ^ k := by
  rw [← pow_mul]
  exact not_five_dvd_two_pow _

end Item228Census2Proof

end CFSG.RankThree.PartTwo.Sec21
