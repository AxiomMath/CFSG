module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

theorem kThinL2Odd_holds :
    ∀ (X : Type) [Group X] [Finite X] (p : ℕ), 5 < p → IsL2Odd X p →
      ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r (⊤ : Subgroup X) ≤ 1 := by
  intro X _ _ p hp5 hX r hr hr2
  have hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 p 1 :=
    hX.statedClassicalModel_of_ne_zero (by norm_num)
  have hp : p.Prime := hX.admissible.1
  have hp3 : 3 < p := by omega
  exact CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_prime hp hp3 hm hr hr2

end CFSG.LocalAnalysis.UniquenessCase.UC22
