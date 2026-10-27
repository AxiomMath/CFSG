module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Halves
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1RowsIVA6
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1K2

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
open CFSG.StandardType.RCKSmall (RCKSmallTag RCKSmallLabel RCKSmallEmpty)
open CFSG.StandardType.RCKA6 (RCKLemmaP)

theorem ggSixRootCommKnownOpen_of_leaves
    (hK1I : RCKRowK1NS .I RCKPosRootSub) (hK1II : RCKRowK1 .II RCKPosRootElt)
    (hK1III : RCKRowK1 .III RCKPosShort) (hK1IIp : RCKRowK1 .IIp (RCKPosCent 96))
    (hR : RCKRootPosKnownFlag) (hR2 : RCKRootPosKnownII) (hNbr : RCKK2NbrRootSub)
    (hFlag : RCKK2FlagRootSub) (hCol : RCKK2NbrCollinear) (hK2III : RCKRowK2 .III RCKPosShort)
    (hK2IIp : RCKRowK2 .IIp (RCKPosCent 96)) (hS : RCKSmallEmpty) (hP : RCKLemmaP) :
    GGSixRootCommKnownOpen := by
  intro i h1 h2
  cases i with
  | I =>
    exact ggSixRootCommKnownRow_of_halves_ns .I RCKPosRootSub hK1I (rckRowK2_I_of hR hNbr hFlag) hS
  | II => exact ggSixRootCommKnownRow_of_halves .II RCKPosRootElt hK1II (rckRowK2_II_of hR2 hCol)
  | III => exact ggSixRootCommKnownRow_of_halves .III RCKPosShort hK1III hK2III
  | IIp => exact ggSixRootCommKnownRow_of_halves .IIp (RCKPosCent 96) hK1IIp hK2IIp
  | IV => exact ggSixRootCommKnownRow_IV_of_smallEmpty hS
  | A6 => exact ggSixRootCommKnownRow_A6_of_lemmaP hP
  | L32 => exact absurd rfl h1
  | U33 => exact absurd rfl h2

theorem ggSixRootCommKnownOpen_of_leavesConj
    (h : GGSixRootCommKnownLeaves) (hS : RCKSmallEmpty) (hP : RCKLemmaP) : GGSixRootCommKnownOpen := by
  obtain ⟨hK1I, hK1II, hK1III, hK1IIp, hR, hR2, hNbr, hFlag, hCol, hK2III, hK2IIp⟩ := h
  exact ggSixRootCommKnownOpen_of_leaves hK1I hK1II hK1III hK1IIp hR hR2 hNbr hFlag hCol hK2III hK2IIp hS hP

end CFSG.StandardType.RCKC1
