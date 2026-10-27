module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerOdd
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Open CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem centralizer_le_of_involution_of_two_le_pRank (D : Data G) (h61 : UC6.R6_1 D)
    {p : ℕ} (hp : p.Prime) (hpsig : p ∈ D.sig) {v : G} (hv2 : v ^ 2 = 1) (hv1 : v ≠ 1)
    (hrank : 2 ≤ CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer ({v} : Set G))) :
    Subgroup.centralizer ({v} : Set G) ≤ D.M := by
  obtain ⟨A, hA, hAel, hAcard⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hp (k := 2) hrank
  have hAM : A ≤ D.M := hA.trans inf_le_left
  have hAv : A ≤ Subgroup.centralizer ({v} : Set G) := hA.trans inf_le_right
  haveI : Fact p.Prime := ⟨hp⟩
  have hAc : ¬ IsCyclic A :=
    RankThreeTheoremC.not_isCyclic_of_elemAbelian hAel hAcard le_rfl
  exact centralizer_le_of_noncyclic D h61 hpsig hAM hAel.isPGroup hAc hv1
    ⟨1, by simpa using hv2⟩ hAv

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
