module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofCensus
public import CFSG.RankThree.PartTwo.Sec4.Item47CoreClosed

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem outer_cases_of_alt47W
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G} (hx3 : x ^ 3 = 1)
    (hout : InducesOuterTheta x L) (h : Alt47W L x) :
    KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField ∨
      IsSLThreePiAny (L ⧸ aschbacherSolvableCore 3 L) := by
  rcases h with ⟨-, -, -, -, -, -, hk⟩ | ⟨p, e, hp, -, he, -, hSL', -⟩ | ⟨-, hk⟩ |
      ⟨n, hn, hSL', -⟩ | ⟨n, -, hD4⟩
  · exact Or.inl hk
  · right; right
    rcases hSL' with h1 | h1
    · exact Or.inl ⟨_, h1⟩
    · exact Or.inr ⟨p, e, hp, he, h1⟩
  · exact Or.inl hk
  · right; right
    rcases hSL' with h1 | h1
    · exact Or.inl ⟨_, h1⟩
    · exact Or.inr ⟨2, n, ⟨Nat.prime_two⟩, hn, h1⟩
  · right; left
    obtain ⟨⟨hp, hf, -⟩, hm⟩ := hD4
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 hp hf hm
    exact .triality n hf K hK σ hσ (KFacts.inducesKindTriality_graphField hf hK hσ L hx3 hout e)

theorem item4_23_of_W
    (h45 : Item4_5) (h46 : Item4_6) (hSL : K423SLThree) (hCov : K423Cover)
    (hIn : K423InnerCensus) : Item4_23 :=
  Item423Proof.item4_23_of_outer h45 h46 hSL hCov hIn fun G _ _ hS4 h3 L hL x hx3 hout =>
    outer_cases_of_alt47W (hx3 ▸ pow_orderOf_eq_one x) hout
      (rank3II_4_7W_of h46 G hS4 h3 L hL x hx3 hout)

theorem item4_23_of_res2W
    (h45 : Item4_5) (h46 : Item4_6) (hSL : K423SLThree) (hCov : K423Cover)
    (h3 : K423Inner46Three) (hθ : K423SporThetaCent) (hJ3 : K423SporJ3) (hJ4 : K423SporJ4)
    (hMcL : K423SporMcL) (h6 : K423Inner46SixRest) (hθ7 : K423ThetaCentSeven)
    (hSp : K423SevenSp62) (h8 : K423Inner46EightRest) : Item4_23 :=
  item4_23_of_W h45 h46 hSL hCov (k423InnerCensus_of_res2 h3 hθ hJ3 hJ4 hMcL h6 hθ7 hSp h8)

end CFSG.RankThree.PartTwo.Sec4
