module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Smith81.OrthSegre
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 QuadraticMap Module

namespace CFSG.RankThree.GF2n.Smith81

section PlusType

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isPlusType_of_not_noTSP {qU : QuadraticForm K (ι → K)} (h4 : Fintype.card ι = 4)
    (h : ¬ NoTotallySingularPlane qU) : CFSG.GroupTheory.WeirSylow.IsPlusType qU := by
  unfold NoTotallySingularPlane at h
  push Not at h
  obtain ⟨s, t, hs, ht, hst, hind⟩ := h
  have hli : LinearIndependent K ![s, t] := by
    rw [LinearIndependent.pair_iff]
    exact hind
  refine ⟨Submodule.span K (Set.range ![s, t]), ?_, ?_⟩
  · rw [finrank_span_eq_card hli, Fintype.card_fin, Module.finrank_fintype_fun_eq_card, h4]
  · intro x hx
    rw [Matrix.range_cons_cons_empty] at hx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    rw [QuadraticMap.map_add qU, QuadraticMap.map_smul, QuadraticMap.map_smul, hs, ht,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hst]
    simp

end PlusType

end CFSG.RankThree.GF2n.Smith81
