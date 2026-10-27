module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.MPrime
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem generalizedFitting_MbarPrime_eq_CN_of_fitting
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0))) :
    generalizedFitting (MbarPrime M Q Z Z0) =
      ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))).subgroupOf
        (MbarPrime M Q Z Z0) := by
  have hKH : bar M Q (NormH0 M Z Z0) ≤ bar M Q (H0 M Z) := MbarPrimeLe M Q Z Z0
  let e : ↥(MbarPrime M Q Z Z0) ≃* ↥(bar M Q (NormH0 M Z Z0)) :=
    Subgroup.subgroupOfEquivOfLe hKH
  have hmapF : (generalizedFitting (MbarPrime M Q Z Z0)).map e.toMonoidHom =
      generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) :=
    CFSG.WholeGroup.generalizedFitting_map_mulEquiv e
  have hmapS : (((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))).subgroupOf
        (MbarPrime M Q Z Z0)).map e.toMonoidHom =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨⟨y.1, hKH y.2⟩, y.2⟩, hy, rfl⟩
  exact Subgroup.map_injective e.injective (hmapF.trans (hF.trans hmapS.symm))

theorem pCore_two_MbarPrime_eq_CN_subgroupOf_of_fitting
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (h712 : Stroth712Statement)
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0))) :
    pCore 2 (MbarPrime M Q Z Z0) =
      ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))).subgroupOf
        (MbarPrime M Q Z Z0) := by
  rw [← generalizedFitting_MbarPrime hc hs hZ0 h712]
  exact generalizedFitting_MbarPrime_eq_CN_of_fitting hc hs hZ0 hF

end CFSG.RankThree.GF2n.Stroth80
