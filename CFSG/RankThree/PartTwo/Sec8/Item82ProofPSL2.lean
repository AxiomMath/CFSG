module

public import CFSG.RankThree.PartTwo.Sec8.Item82ProofDefs
import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofSeitzL2

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item82Proof

open CFSG CFSG.Open

theorem card_le_three_of_card_eq_twelve {X : Type*} [Group X] [Finite X] (hX : Nat.card X = 12)
    {E : Subgroup X} (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpg : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  have hdvd : 3 ^ k ∣ 12 := hk ▸ hX ▸ Subgroup.card_subgroup_dvd_card E
  rw [hk]
  rcases k with _ | _ | k
  · norm_num
  · norm_num
  · exfalso
    have h9 : 3 ^ 2 ∣ 12 := (pow_dvd_pow 3 (by omega : 2 ≤ k + 2)).trans hdvd
    norm_num at h9

theorem kF82TwoNoE9PSL2 : KF82TwoNoE9PSL2 := by
  intro K _ _ p e hp hK hpe E hE
  have : Fact p.Prime := ⟨hp⟩
  have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
  by_cases hp3 : p = 3
  · subst hp3
    have he1 : e = 1 := hpe.resolve_left (not_not.mpr rfl)
    subst he1
    have hK3 : Nat.card K = 3 := by simpa using hK
    have hodd : GorensteinWalter.IsOddPrimePower (Nat.card K) :=
      ⟨3, 1, Nat.prime_three, by decide, le_rfl, by simpa using hK3⟩
    have hcard : Nat.card (GorensteinWalter.PSL2 K) = 12 := by
      rw [GorensteinWalter.psl2_card_formula K hodd, hK3]
      norm_num
    exact card_le_three_of_card_eq_twelve hcard hE
  · have he : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · subst h0
        rw [pow_zero] at hK
        omega
      · exact h0
    exact Sec4.Item434RowsProof.SeitzL2.card_le_three_of_pow_three hp3 hK he hE.2

end CFSG.RankThree.PartTwo.Sec8.Item82Proof
