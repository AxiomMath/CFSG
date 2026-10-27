module

public import CFSG.LocalAnalysis.StandardType.GGTypeADefs
public import CFSG.LocalAnalysis.StandardType.GGExcRegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNClassicalCover
public import CFSG.LocalAnalysis.StandardType.GGTPNExcCover
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrowC6
public import CFSG.LocalAnalysis.StandardType.GGTPNI1
public import CFSG.LocalAnalysis.StandardType.GGTPNE6TwoSeven
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableClDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNClGen
public import CFSG.LocalAnalysis.StandardType.GGTPNNonExc
public import CFSG.LocalAnalysis.StandardType.GGTypeAClRA
public import CFSG.LocalAnalysis.StandardType.GGExcGen
public import CFSG.LocalAnalysis.StandardType.GGTypeAExcRE
public import CFSG.LocalAnalysis.StandardType.GGTPNA8SevenR
public import CFSG.LocalAnalysis.StandardType.GGE6TwoSevenComp
public import CFSG.LocalAnalysis.StandardType.GGTPNI1Holds
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGK0ExcB3

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTablePKnownRK_typeAClassical
    (hGen : GGClGenRK fun p n labJ labX => GGRegimeTypeA p n labJ labX ∧ p.Prime ∧ p ≠ 2)
    (hRA : GGTypeAClRARK) (hA8 : GGTablePKnownR GGRegimeA8Seven) :
    GGTablePKnownRK fun p n labJ labX => GGRegimeTypeA p n labJ labX ∧ GGTPNClTag labX.tag := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨hreg, hcl⟩ := hr
  have hm : GGTPNMarked p (fun _ _ => True) A := hd.1.2.2.2.2.2.2.2
  rcases ggTPN_classicalCover hp hp2 hm hΛX hhX hcl with hg | hra | ⟨hp7, hX8⟩ | ⟨hp5, hX5⟩
  · exact hGen p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨⟨hreg, hp, hp2⟩, hg⟩ hhJ hhX
  · exact hRA p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨hreg, hra⟩ hhJ hhX
  · exact hA8 p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX ⟨hp7, hX8⟩ hhJ hhX
  · have hg : GGKacGenericCl labX p := by
      subst hp5; subst hX5; unfold GGKacGenericCl; norm_num
    exact hGen p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨⟨hreg, hp, hp2⟩, hg⟩ hhJ hhX

theorem ggTablePKnownRK_typeAExc
    (hGenE : GGExcGenRK GGRegimeTypeA) (hRE : GGTypeAExcRERK)
    (hE67 : GGTablePKnownR GGRegimeE6TwoSevenOut) :
    GGTablePKnownRK fun p n labJ labX => GGRegimeTypeA p n labJ labX ∧ GGTPNExcTag labX.tag := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨hreg, hexc⟩ := hr
  have hm : GGTPNMarked p (fun _ _ => True) A := hd.1.2.2.2.2.2.2.2
  rcases ggTPN_excCover hp hp2 hm hΛX hhX hexc with hpair | ⟨hp7, hX⟩
  · by_cases hg : GGKacGeneric labX p
    · exact hGenE p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨hreg, hg⟩ hhJ hhX
    · exact hRE p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX
        ⟨hreg, ggKacRE_of_excPair_of_not_generic hpair hg⟩ hhJ hhX
  · exact hE67 p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX
      (ggRegimeE6TwoSevenOut_of_two_le hp7 hX hreg.2.2.1) hhJ hhX

theorem ggTablePKnownRK_typeA
    (hNon : GGNonExcRK GGRegimeTypeA)
    (hGen : GGClGenRK fun p n labJ labX => GGRegimeTypeA p n labJ labX ∧ p.Prime ∧ p ≠ 2)
    (hRA : GGTypeAClRARK) (hA8 : GGTablePKnownR GGRegimeA8Seven)
    (hGenE : GGExcGenRK GGRegimeTypeA) (hRE : GGTypeAExcRERK)
    (hE67 : GGTablePKnownR GGRegimeE6TwoSevenOut) : GGTablePKnownRK GGRegimeTypeA := by
  refine GGTablePKnownRK.mono
    (GGTablePKnownRK.union (ggTablePKnownRK_typeAClassical hGen hRA hA8)
      (GGTablePKnownRK.union (ggTablePKnownRK_typeAExc hGenE hRE hE67) hNon)) ?_
  intro p n labJ labX hJ
  by_cases hcl : GGTPNClTag labX.tag
  · exact Or.inl ⟨hJ, hcl⟩
  · by_cases hexc : GGTPNExcTag labX.tag
    · exact Or.inr (Or.inl ⟨hJ, hexc⟩)
    · exact Or.inr (Or.inr ⟨hJ, hcl, hexc⟩)

theorem ggNbrTablePNbrInputOnL_typeA
    (hrig : GGLabelRigidInput) (hT : GGTPNTransferBNoCorners) (hI1 : GGI1OfPairL)
    (hE67 : GGE6TwoSevenComp) (hK : GGTablePKnownRK GGRegimeTypeA) :
    GGNbrTablePNbrInputOnL GGRegimeTypeAL := by
  intro G _ _ p B Bs x L D J y K hc hL hKi hn labL labJ labK hΛL hΛJ hΛK hr hhL hhJ hhK
  have hpair : GGPairTypeA p labL labJ := hr
  have hreg : GGRegimeTypeA p (Nat.card Bs) labJ labK := hpair.regime _ labK
  have hβ := hc.1.2.2.2.2.2.1
  obtain ⟨hJK, hN, hx, hBasic⟩ := hT G p B Bs x L D J y K hc hL hKi hn
  have hCJ := hI1 G p B Bs x L D J hc hL labL labJ hΛL hΛJ (Or.inr (Or.inr hpair)) hhL hhJ
  have hker := ggTPNTrKernelI1_holds G p B Bs x L D J y K hc hL hKi hn hJK hN hx hCJ
  have hhJ' : GGHasLabel labJ (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)) :=
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK).symm hhJ
  have hcorners : GGTPNCorners p (J.subgroupOf K) := by
    refine ⟨fun hp7 hE6 => ?_, fun _ _ _ => ggTPNRankJ_of_typeA hrig hβ.1 hβ.2.1 hΛJ hreg hhJ'⟩
    have h7 := ggRegimeE6TwoSevenOut_of_two_le (p := p) (n := Nat.card Bs) (labJ := labJ)
      (labX := ⟨.E6, 0, 1⟩) hp7 rfl hreg.2.2.1
    exact ggTPNHalfJ_e6TwoSeven hE67 hBasic labJ hΛJ hhJ' h7.2.2.1 h7.2.2.2 hp7 hE6
  have hD : GGTPNDatumB p (Nat.card Bs) (fun _ _ => True) (ggAutsOf K Bs hN)
      (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) :=
    ⟨hBasic, hcorners⟩
  obtain ⟨labJ', labX', hΛJ', hΛX', hrow, hJ', hX'⟩ :=
    hK p hβ.1 hβ.2.1 ↥K (ggAutsOf K Bs hN) (ggAutsOf K B (hc.2.1.1.trans hN))
      (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) (Nat.card Bs) hD hker labJ labK hΛJ hΛK
      hreg hhJ' hhK
  exact ⟨labJ', labX', hΛJ', hΛX', hrow,
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) hJ', hX'⟩

theorem ggNbrTablePNbrInputOnL_typeA_of_leaves
    (hT : GGTPNTransferBNoCorners) (hB3 : GGK0ExcB3) :
    GGNbrTablePNbrInputOnL GGRegimeTypeAL :=
  ggNbrTablePNbrInputOnL_typeA ggLabelRigidInput_holds hT ggI1OfPairL_holds
    E6TwoSeven.ggE6TwoSevenComp_holds
    (ggTablePKnownRK_typeA (ggNonExcRK_holds GGRegimeTypeA)
      (ggClGenRK_of_regime
        (R := fun p n labJ labX => GGRegimeTypeA p n labJ labX ∧ p.Prime ∧ p ≠ 2)
        fun p n labJ labX h lab hiso => ggTypeA_regime_not_rankOne h.2.1 h.2.2 h.1 lab hiso)
      ggTypeAClRARK_holds ggTablePKnownR_a8Seven
      (ggExcGenRK_holds (ggK0ExcBS_of_B3 hB3) GGRegimeTypeA) (ggTypeAExcRERK_holds hB3)
      (ggTablePKnownR_e6TwoSevenOut E6TwoSeven.ggE6TwoSevenComp_holds))

end CFSG.StandardType

end
