module

import CFSG.Quasithin.H13.GoldschmidtC137SQRkHat
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

theorem s16k_pRank_hat_a6_le_two {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsHat ↥L ↥(alternatingGroup (Fin 6))) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p L ≤ 2 := by
  have hrank : CFSG.Quasithin.H13.U3.GC137.SQ.RankLeTwo ↥L :=
    CFSG.Quasithin.H13.U3.GC137.SQ.rankLeTwo_of_hatA6 hL.1.1 hL.2.1 hL.2.2.some
  refine CFSG.SectionRank.pRank_le hp.one_lt fun E hEL hE => ?_
  have hE' : CFSG.Open.IsElemAbelian p (E.subgroupOf L) := hE.subgroupOf L
  have h := hrank p hp hp2 (E.subgroupOf L) hE'
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv] at h
  exact h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
