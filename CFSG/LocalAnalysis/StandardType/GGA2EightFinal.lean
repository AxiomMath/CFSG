module

public import CFSG.LocalAnalysis.StandardType.GGA2EightDefs
public import CFSG.LocalAnalysis.StandardType.GGA2EightSlices
public import CFSG.LocalAnalysis.StandardType.GGA2EightRA
public import CFSG.LocalAnalysis.StandardType.GGTPNClassicalCover
public import CFSG.LocalAnalysis.StandardType.GGTPNExcCover
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrowC6
public import CFSG.LocalAnalysis.StandardType.GGTPNA8SevenR
public import CFSG.LocalAnalysis.StandardType.GGTPNE6TwoSeven
public import CFSG.LocalAnalysis.StandardType.GGE6TwoSevenComp
public import CFSG.LocalAnalysis.StandardType.GGTPNI1Holds
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGK0ExcB3

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTablePKnownR_a2Eight
    (hEx : GGA2EightExcPair) (hNon : GGA2EightNonExc)
    (hA8 : GGTablePKnownR GGRegimeA8Seven)
    (hE67 : GGTablePKnownR GGRegimeE6TwoSevenOut) : GGTablePKnownR GGRegimeA2Eight := by
  have hCl := ggA2EightClGen_holds
  have hRA := ggA2EightRA_holds
  intro p hp hp2 X _ _ A Ab σ J n hd labJ labX hΛJ hΛX hr hhJ hhX
  have hr' : p = 7 ∧ labJ = ⟨.A, 2, 3⟩ := hr
  obtain ⟨hp7, hlabJ⟩ := hr'
  have hm : GGTPNMarked p (fun _ _ => True) A := hd.1.2.2.2.2.2.2.2
  by_cases hcl : GGTPNClTag labX.tag
  · rcases ggTPN_classicalCover hp hp2 hm hΛX hhX hcl with hg | hra | ⟨hp7', hX8⟩ | ⟨hp5, hX5⟩
    · exact hCl p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX ⟨hr, hg⟩ hhJ hhX
    · exact hRA p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX ⟨hr, hra⟩ hhJ hhX
    · exact hA8 p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX ⟨hp7', hX8⟩ hhJ hhX
    · exact absurd (hp7.symm.trans hp5) (by decide)
  · by_cases hexc : GGTPNExcTag labX.tag
    · rcases ggTPN_excCover hp hp2 hm hΛX hhX hexc with hpair | ⟨hp7', hX⟩
      · exact hEx p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX ⟨hr, hpair⟩ hhJ hhX
      · refine hE67 p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX
          (ggRegimeE6TwoSevenOut_of_two_le hp7' hX ?_) hhJ hhX
        rw [hlabJ]
        decide
    · exact hNon p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX ⟨hr, hcl, hexc⟩ hhJ hhX

theorem ggNbrTablePNbrInputOn_a2Eight
    (hT : GGTPNTransferBNoCorners) (hE67 : GGE6TwoSevenComp)
    (hK : GGTablePKnownR GGRegimeA2Eight) : GGNbrTablePNbrInputOn GGRegimeA2Eight := by
  intro G _ _ p B Bs x L D J y K hc hL hKi hn labJ labK hΛJ hΛK hr hhJ hhK
  have hr' : p = 7 ∧ labJ = ⟨.A, 2, 3⟩ := hr
  obtain ⟨hp7, hlabJ⟩ := hr'
  obtain ⟨hJK, hN, hx, hBasic⟩ := hT G p B Bs x L D J y K hc hL hKi hn
  have hβ := hc.1.2.2.2.2.2.1
  have hhJ' : GGHasLabel labJ (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)) :=
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK).symm hhJ
  have hcorners : GGTPNCorners p (J.subgroupOf K) := by
    refine ⟨fun hp7' hE6 => ?_, fun h3 _ _ => absurd (h3.symm.trans hp7) (by decide)⟩
    have h7 := ggRegimeE6TwoSevenOut_of_two_le (p := p) (n := Nat.card Bs) (labJ := labJ)
      (labX := ⟨.E6, 0, 1⟩) hp7' rfl (by rw [hlabJ]; decide)
    exact ggTPNHalfJ_e6TwoSeven hE67 hBasic labJ hΛJ hhJ' h7.2.2.1 h7.2.2.2 hp7' hE6
  have hD : GGTPNDatumB p (Nat.card Bs) (fun _ _ => True) (ggAutsOf K Bs hN)
      (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) :=
    ⟨hBasic, hcorners⟩
  obtain ⟨labJ', labX', hΛJ', hΛX', hrow, hJ', hX'⟩ :=
    hK p hβ.1 hβ.2.1 ↥K (ggAutsOf K Bs hN) (ggAutsOf K B (hc.2.1.1.trans hN))
      (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) (Nat.card Bs) hD labJ labK hΛJ hΛK
      hr hhJ' hhK
  exact ⟨labJ', labX', hΛJ', hΛX', hrow,
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) hJ', hX'⟩

theorem ggNbrTablePNbrInputOn_a2Eight_of_leaves
    (hT : GGTPNTransferBNoCorners) (hB3 : GGK0ExcB3) :
    GGNbrTablePNbrInputOn GGRegimeA2Eight :=
  ggNbrTablePNbrInputOn_a2Eight hT E6TwoSeven.ggE6TwoSevenComp_holds
    (ggTablePKnownR_a2Eight (ggA2EightExcPair_holds hB3)
      ggA2EightNonExc_holds ggTablePKnownR_a8Seven
      (ggTablePKnownR_e6TwoSevenOut E6TwoSeven.ggE6TwoSevenComp_holds))

end CFSG.StandardType

end
