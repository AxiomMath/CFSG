module

public import CFSG.Quasithin.Background.GoldschmidtRankOneListed
public import CFSG.Quasithin.Background.GoldschmidtRankOneSUTwo

public section

namespace CFSG.Quasithin

open CFSG.Open

universe u

theorem rankOneUnitaryFacts : RankOneUnitaryFacts := by
  intro n hn F _ _ hF
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    exact ⟨isRankOneSylow_statedSU_one hF, (isRankOneSylowCyclic_statedProj_one hF).1⟩
  · exact ⟨isRankOneSylow_statedSU h2 hF, (isRankOneSylowCyclic_statedProj h2 hF).1⟩

theorem rankOneListedFacts : RankOneListedFacts.{u} :=
  rankOneListedFacts_of_unitary rankOneUnitaryFacts

theorem prop_F19_of_hyp111 {G : Type u} [Group G] [Finite G]
    {L1 L2 S : Subgroup G} (h : Hyp111 L1 L2 S) :
    (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S ∧
    IsWeakBNPair (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S) ∧
    coreIn (bigB L1 L2 S) (L1 ⊔ L2 ⊔ S) = ⊥ ∧
    ∃ c : (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)).Completion
        ↥(L1 ⊔ L2 ⊔ S), c.IsFaithful :=
  prop_F19_of_listed rankOneListedFacts h

end CFSG.Quasithin
