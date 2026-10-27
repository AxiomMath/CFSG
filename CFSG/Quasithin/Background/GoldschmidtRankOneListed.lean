module

public import CFSG.Quasithin.Background.GoldschmidtRankOneSmall
public import CFSG.Quasithin.H13.NQCatLieOverRank1

public section

namespace CFSG.Quasithin

open CFSG.Open

universe u

@[expose] def RankOneUnitaryFacts : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (F : Type) [Field F] [Finite F], Nat.card F = (2 ^ n) ^ 2 →
    IsRankOneSylow (StatedSU 3 (2 ^ n) F) ∧ IsRankOneSylow (StatedProj (StatedSU 3 (2 ^ n) F))

theorem rankOneListedFacts_of_unitary (hU : RankOneUnitaryFacts) :
    RankOneListedFacts.{u} := by
  intro K _ h
  rcases h with ⟨n, hn, ⟨e⟩⟩ | ⟨a, ⟨e⟩⟩ | ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩ |
    ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rcases Nat.lt_or_ge n 2 with h1 | h2
    · obtain rfl : n = 1 := by omega
      obtain ⟨e'⟩ := isL2Quot_one_iff_perm3.1 ⟨e⟩
      exact isRankOneSylow_perm_three.of_mulEquiv e'.symm
    · have : NeZero n := ⟨by omega⟩
      have : Finite K := Finite.of_equiv _ e.symm.toEquiv
      exact CFSG.Quasithin.H13.NQCat.isRankOneSylow_of_benderType (.linear n h2 e)
  · rcases Nat.eq_zero_or_pos a with h0 | h1
    · subst h0
      exact isRankOneSylow_sz_zero.of_mulEquiv e.symm
    · have : Finite K := Finite.of_equiv _ e.symm.toEquiv
      exact CFSG.Quasithin.H13.NQCat.isRankOneSylow_of_benderType
        (.suzuki a h1 e)
  · exact (hU n hn F hF).1.of_mulEquiv e.symm
  · exact (hU n hn F hF).2.of_mulEquiv e.symm
  · exact isRankOneSylow_dihedral_five.of_mulEquiv e.symm

end CFSG.Quasithin
