module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylow
import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalRank

public section

namespace CFSG.RankThree.LocalRank

open CFSG.Assembly CFSG.Assembly.RankThreeEven

theorem above_two_local_rank_invariant_prime_complement_odd {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {A X : Subgroup G} (hA : IsPGroup p A)
    (hrank : localRank p G < pRank p A) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hX : ¬p ∣ Nat.card X) : Odd (Nat.card X) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro heven
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_in_prime_complement_subgroup
      p hp A X hA hX hAX 2 Nat.prime_two
  have hlocal : IsTwoLocal
      (Subgroup.normalizer (((S : Subgroup X).map X.subtype : Subgroup G) : Set G)) :=
    ⟨_, fun hbot => S.ne_bot_of_dvd_card heven
      ((Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hbot),
      S.isPGroup'.map X.subtype, rfl⟩
  have hle : pRank p A ≤ localRank p G :=
    (CFSG.RankThreeEvenClassification.Helpers.pRank_mono p hp hS).trans
      (CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank p hp _ hlocal)
  omega

end CFSG.RankThree.LocalRank
