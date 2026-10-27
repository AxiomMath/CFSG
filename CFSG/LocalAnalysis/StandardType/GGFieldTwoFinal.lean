module

public import CFSG.LocalAnalysis.StandardType.GGFieldTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldTwoSlices
public import CFSG.LocalAnalysis.StandardType.GGFieldTwoLabel
public import CFSG.LocalAnalysis.StandardType.GGTPNNonExcR
public import CFSG.LocalAnalysis.StandardType.GGTPNExcTwoSlices
public import CFSG.LocalAnalysis.StandardType.GGExcTwoCompListsRE
public import CFSG.LocalAnalysis.StandardType.GGF4TwoThree
public import CFSG.LocalAnalysis.StandardType.GGK0CompREMult
public import CFSG.LocalAnalysis.StandardType.GGB36JExc
public import CFSG.LocalAnalysis.StandardType.GGE6TwoCenter
public import CFSG.LocalAnalysis.StandardType.GGE6TwoLocalRank
public import CFSG.LocalAnalysis.StandardType.GGE6TwoSevenComp
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRAC5
public import CFSG.LocalAnalysis.StandardType.GGTPNA8SevenR
public import CFSG.LocalAnalysis.StandardType.GGTPNE6TwoSeven
public import CFSG.LocalAnalysis.StandardType.GGTPNClassicalCover
public import CFSG.LocalAnalysis.StandardType.GGTPNExcCover
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrowC6
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGK0ExcB3

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTablePKnownR_fieldTwo
    (hRA : GGTablePKnownR GGRegimeFieldTwoRA)
    (hEx2 : GGTablePKnownR GGRegimeFieldTwoExcTwo) (hNon : GGNonExcR GGRegimeFieldTwo)
    (hA8 : GGTablePKnownR GGRegimeA8Seven) (hE67 : GGTablePKnownR GGRegimeE6TwoSevenOut) :
    GGTablePKnownR GGRegimeFieldTwo := by
  have hCl := ggFieldTwoClGen_holds
  intro p hp hp2 X _ _ A Ab σ J n hd labJ labX hΛJ hΛX hr hhJ hhX
  have hJ2 : 2 ≤ labJ.n := hr.1
  have hX1 : labX.n = 1 := hr.2.1
  have hm : GGTPNMarked p (fun _ _ => True) A := hd.1.2.2.2.2.2.2.2
  by_cases hcl : GGTPNClTag labX.tag
  · rcases ggTPN_classicalCover hp hp2 hm hΛX hhX hcl with hg | hra | ⟨hp7, hX8⟩ | ⟨hp5, hX5⟩
    · exact hCl p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX ⟨hr, hg⟩ hhJ hhX
    · exact hRA p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX ⟨hr, hra⟩ hhJ hhX
    · exact hA8 p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX ⟨hp7, hX8⟩ hhJ hhX
    · rw [hX5] at hX1
      simp at hX1
  · by_cases hexc : GGTPNExcTag labX.tag
    · rcases ggTPN_excCover hp hp2 hm hΛX hhX hexc with hpair | ⟨hp7, hX⟩
      · refine hEx2 p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX ⟨hr, hX1, ?_⟩ hhJ hhX
        have h := hpair.2.2.2
        rcases h with h | h | h | h | h <;> simp [h]
      · exact hE67 p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX
          (ggRegimeE6TwoSevenOut_of_two_le hp7 hX hJ2) hhJ hhX
    · exact hNon p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX ⟨hr, hcl, hexc⟩ hhJ hhX

theorem ggNbrTablePNbrInputOn_fieldTwo
    (hT : GGTPNTransferBNoCorners) (hE67 : GGE6TwoSevenComp) (hT9 : GGFieldTwoCorner)
    (hK : GGTablePKnownR GGRegimeFieldTwo) : GGNbrTablePNbrInputOn GGRegimeFieldTwo := by
  intro G _ _ p B Bs x L D J y K hc hL hKi hn labJ labK hΛJ hΛK hr hhJ hhK
  have hr' := hr
  obtain ⟨hJ2, hK1, -⟩ := hr'
  obtain ⟨hJK, hN, hx, hBasic⟩ := hT G p B Bs x L D J y K hc hL hKi hn
  have hβ := hc.1.2.2.2.2.2.1
  have hhJ' : GGHasLabel labJ (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)) :=
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK).symm hhJ
  have hcorners : GGTPNCorners p (J.subgroupOf K) := by
    refine ⟨fun hp7 hE6 => ?_, fun hp3 n' hl => ?_⟩
    · have h7 := ggRegimeE6TwoSevenOut_of_two_le (p := p) (n := Nat.card Bs) (labJ := labJ)
        (labX := ⟨.E6, 0, 1⟩) hp7 rfl hJ2
      exact ggTPNHalfJ_e6TwoSeven hE67 hBasic labJ hΛJ hhJ' h7.2.2.1 h7.2.2.2 hp7 hE6
    · have hn' : n' = 1 := ggFieldTwo_twA5_n_eq_one hΛK hK1 hhK hl
      subst hn'
      exact hT9 G p B Bs x L D J y K hc hL hKi hn hJK hp3 hl ⟨labJ, hΛJ, hJ2, hhJ'⟩
  have hD : GGTPNDatumB p (Nat.card Bs) (fun _ _ => True) (ggAutsOf K Bs hN)
      (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) :=
    ⟨hBasic, hcorners⟩
  obtain ⟨labJ', labX', hΛJ', hΛX', hrow, hJ', hX'⟩ :=
    hK p hβ.1 hβ.2.1 ↥K (ggAutsOf K Bs hN) (ggAutsOf K B (hc.2.1.1.trans hN))
      (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) (Nat.card Bs) hD labJ labK hΛJ hΛK
      hr hhJ' hhK
  exact ⟨labJ', labX', hΛJ', hΛX', hrow,
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) hJ', hX'⟩

theorem ggNbrTablePNbrInputOn_fieldTwo_of_leaves
    (hT : GGTPNTransferBNoCorners) (hB3 : GGK0ExcB3) (hT9 : GGFieldTwoCorner) :
    GGNbrTablePNbrInputOn GGRegimeFieldTwo := by
  have hRE : GGK0CompRE :=
    ggK0CompRE_of_mult (ggK0CompREMult_of_excB (ltqJx_excB_of_excBS (ggK0ExcBS_of_B3 hB3)))
  have h7 : GGE6TwoSevenComp := E6TwoSeven.ggE6TwoSevenComp_holds
  exact ggNbrTablePNbrInputOn_fieldTwo hT h7 hT9
    (ggTablePKnownR_fieldTwo
      (ggTablePKnownR_fieldTwoRA ggLabelRigidInput_holds)
      (ggTablePKnownR_fieldTwoExcTwo h7 (ggE6TwoThreeComp_of_K0RE hRE)
        (ggTwE6TwoThreeComp_of_K0RE hRE) (ggE7TwoThreeComp_of_K0RE hRE)
        (ggE8TwoThreeComp_of_K0RE hRE) ggF4TwoThreeComp_holds ggE6TwoCenterBot_holds
        ggE6TwoLocalRankThree_holds)
      (ggNonExcR_holds GGRegimeFieldTwo) ggTablePKnownR_a8Seven
      (ggTablePKnownR_e6TwoSevenOut h7))

end CFSG.StandardType

end
