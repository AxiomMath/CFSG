module

public import CFSG.Quasithin.Vol2.Ch10SecA312AI
public import CFSG.Quasithin.Vol2.Ch10SecA312AK
public import CFSG.Quasithin.Vol2.Ch10SecA312AL
public import CFSG.Quasithin.Vol2.Ch10SecA312LD
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.Dihedral.Glauberman.DicksonMaxTraceField
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.SteinbergBRSemidirectSL2
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique

theorem a312ZCentLie_holds
    : A312ZCentLie := by
  intro X _ _ T B hcase hc
  have hq : CFSG.IsQuasisimple X := hc.1
  have hq' : CFSG.IsQuasisimple ↥(⊤ : Subgroup X) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq
  rcases hcase with ⟨⟨n, hn⟩, hR, P, ⟨hP, hPtop, -⟩, hBP⟩ | ⟨f, -, hF4, -, -, -⟩
  · rcases hR with ⟨f, ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, -, h⟩⟩ | hT
    · exact (false_of_zcentFor (ZCentFor.of_top (zcentFor_of_isPSL3 hq' hf h)) hc).elim
    · exact (false_of_zcentFor (ZCentFor.of_top (zcentFor_of_isSL3 hq' hf h)) hc).elim
    · have hne : perfectCore P ≠ ⊥ := hBP ▸ ne_bot_of_mem_cComp hc.2.2.2.2.1
      rw [hBP]
      exact a312Sp4_of_isPSp4 hq hf (IsPSp4.of_mulEquiv Subgroup.topEquiv h) hP hPtop hne
    · exact (false_of_zcentFor (ZCentFor.of_top (zcentFor_of_isG2 hq' h)) hc).elim
    · exact (false_of_zcentFor (ZCentFor.of_top (zcentFor_of_is3D4 hq' h)) hc).elim
    · exact (false_of_zcentFor (ZCentFor.of_top (zcentFor_of_is2F4 hq' h)) hc).elim
    · exact (A312LF.false_of_isTits hT hP hPtop (hBP ▸ hn)).elim
  · exact (false_of_zcentFor (ZCentFor.of_top (zcentFor_of_is2F4 hq' hF4)) hc).elim

theorem a312ZCentFacts_of
    (hl45 : A312ZCentL45) (hm22 : A312ZCentM22) (hm23 : A312ZCentM23) (hm24 : A312ZCentM24)
    (hj4 : A312ZCentJ4) (hhs : A312ZCentHS) (hru : A312ZCentRu) : A312ZCentFacts :=
  ⟨a312ZCentLie_holds, hl45, hm22, hm23, hm24, hj4, hhs, hru⟩

end CFSG.Quasithin.Vol2.Ch10.A312A
