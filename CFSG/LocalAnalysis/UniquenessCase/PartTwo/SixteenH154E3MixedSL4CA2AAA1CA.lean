module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenA
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_cV_T_le_cClos (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L) :
    V ⊓ Subgroup.centralizer (D.T : Set G) ≤ E3.cClos V 1 D.T := by
  intro v hv
  obtain ⟨hvV, hvcT⟩ := Subgroup.mem_inf.1 hv
  have hvT : v ∈ D.T := s15_13A_le_T h.hyp151.hyp125 hvV
  rw [E3.cClos]
  exact Subgroup.mem_inf.2 ⟨hvT,
    Subgroup.centralizer_le (E3.wClos_le (V := V) 1 D.T) hvcT⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
