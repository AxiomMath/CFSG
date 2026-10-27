module

public import CFSG.LocalAnalysis.StandardType.GGBcDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNRegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNClGen
public import CFSG.LocalAnalysis.StandardType.GGTPNClassicalCover
public import CFSG.LocalAnalysis.StandardType.GGTPNExcCover
public import CFSG.LocalAnalysis.StandardType.GGTPNNonExc
public import CFSG.LocalAnalysis.StandardType.GGBcClRA
public import CFSG.LocalAnalysis.StandardType.GGBcClA5
public import CFSG.LocalAnalysis.StandardType.GGBcExcPair
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrowC6
public import CFSG.LocalAnalysis.StandardType.GGTPNI1
public import CFSG.LocalAnalysis.StandardType.GGTPNI1Holds
public import CFSG.LocalAnalysis.StandardType.GGTPNE6TwoSeven
public import CFSG.LocalAnalysis.StandardType.GGE6TwoSevenComp
public import CFSG.LocalAnalysis.StandardType.GGTPNA8SevenR
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTablePKnownRK_bcClassical
    (hGen : GGClGenRK GGRegimeBC) (hTA : GGBcClTypeARK) (hA8 : GGTablePKnownR GGRegimeA8Seven) :
    GGTablePKnownRK fun p n labJ labX => GGRegimeBC p n labJ labX ∧ GGTPNClTag labX.tag := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨hreg, hcl⟩ := hr
  have hm : GGTPNMarked p (fun _ _ => True) A := hd.1.2.2.2.2.2.2.2
  rcases ggTPN_classicalCover hp hp2 hm hΛX hhX hcl with hg | hra | ⟨hp7, hX8⟩ | ⟨hp5, hX5⟩
  · exact hGen p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨hreg, hg⟩ hhJ hhX
  · exact hTA p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨hreg, Or.inl hra⟩ hhJ hhX
  · exact hA8 p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX ⟨hp7, hX8⟩ hhJ hhX
  · exact hTA p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨hreg, Or.inr ⟨hp5, hX5⟩⟩ hhJ hhX

theorem ggTablePKnownRK_bcExc
    (hPair : GGBcExcPairRK) (hE67 : GGTablePKnownR GGRegimeE6TwoSevenOut) :
    GGTablePKnownRK fun p n labJ labX => GGRegimeBC p n labJ labX ∧ GGTPNExcTag labX.tag := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨hreg, hexc⟩ := hr
  have hm : GGTPNMarked p (fun _ _ => True) A := hd.1.2.2.2.2.2.2.2
  rcases ggTPN_excCover hp hp2 hm hΛX hhX hexc with hpair | ⟨hp7, hX⟩
  · exact hPair p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨hreg, hpair⟩ hhJ hhX
  · exact hE67 p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX
      (ggRegimeE6TwoSevenOut_of_BC hp7 hX hreg.1) hhJ hhX

theorem ggTablePKnownRK_bc
    (hNon : GGNonExcRK GGRegimeBC)
    (hGen : GGClGenRK GGRegimeBC) (hTA : GGBcClTypeARK) (hA8 : GGTablePKnownR GGRegimeA8Seven)
    (hPair : GGBcExcPairRK) (hE67 : GGTablePKnownR GGRegimeE6TwoSevenOut) :
    GGTablePKnownRK GGRegimeBC := by
  refine GGTablePKnownRK.mono
    (GGTablePKnownRK.union (ggTablePKnownRK_bcClassical hGen hTA hA8)
      (GGTablePKnownRK.union (ggTablePKnownRK_bcExc hPair hE67) hNon)) ?_
  intro p n labJ labX hJ
  by_cases hcl : GGTPNClTag labX.tag
  · exact Or.inl ⟨hJ, hcl⟩
  · by_cases hexc : GGTPNExcTag labX.tag
    · exact Or.inr (Or.inl ⟨hJ, hexc⟩)
    · exact Or.inr (Or.inr ⟨hJ, hcl, hexc⟩)

theorem ggNbrTablePNbrInputOnL_bc
    (hrig : GGLabelRigidInput) (hT : GGTPNTransferBNoCorners) (hI1 : GGI1OfPairL)
    (hE67 : GGE6TwoSevenComp) (hK : GGTablePKnownRK GGRegimeBC) :
    GGNbrTablePNbrInputOnL GGRegimeBCL := by
  intro G _ _ p B Bs x L D J y K hc hL hKi hn labL labJ labK hΛL hΛJ hΛK hr hhL hhJ hhK
  have hpair : GGPairBC p labL labJ := hr
  have hreg : GGRegimeBC p (Nat.card Bs) labJ labK := hpair.regime _ labK
  obtain ⟨hJK, hN, hx, hBasic⟩ := hT G p B Bs x L D J y K hc hL hKi hn
  have hCJ := hI1 G p B Bs x L D J hc hL labL labJ hΛL hΛJ (Or.inr (Or.inl hpair)) hhL hhJ
  have hker := ggTPNTrKernelI1_holds G p B Bs x L D J y K hc hL hKi hn hJK hN hx hCJ
  have hhJ' : GGHasLabel labJ (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)) :=
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK).symm hhJ
  have hcorners : GGTPNCorners p (J.subgroupOf K) := by
    refine ⟨fun hp7 hE6 => ?_, fun _ _ _ => ggTPNRankJ_of_bc hrig hΛJ hreg hhJ'⟩
    have h7 := ggRegimeE6TwoSevenOut_of_BC (n := Nat.card Bs) (labJ := labJ)
      (labX := ⟨.E6, 0, 1⟩) hp7 rfl hreg.1
    exact ggTPNHalfJ_e6TwoSeven hE67 hBasic labJ hΛJ hhJ' h7.2.2.1 h7.2.2.2 hp7 hE6
  have hD : GGTPNDatumB p (Nat.card Bs) (fun _ _ => True) (ggAutsOf K Bs hN)
      (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) :=
    ⟨hBasic, hcorners⟩
  have hβ := hc.1.2.2.2.2.2.1
  obtain ⟨labJ', labX', hΛJ', hΛX', hrow, hJ', hX'⟩ :=
    hK p hβ.1 hβ.2.1 ↥K (ggAutsOf K Bs hN) (ggAutsOf K B (hc.2.1.1.trans hN))
      (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) (Nat.card Bs) hD hker labJ labK hΛJ hΛK
      hreg hhJ' hhK
  exact ⟨labJ', labX', hΛJ', hΛX', hrow,
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) hJ', hX'⟩

theorem ggBcClTypeARK_of_parts (h1 : GGBcClRARK) (h2 : GGBcClA5RK) : GGBcClTypeARK :=
  GGTablePKnownRK.mono (GGTablePKnownRK.union h1 h2) (by
    rintro p n labJ labX ⟨hreg, hx | ⟨hp5, hX5⟩⟩
    · exact Or.inl ⟨hreg, hx⟩
    · exact Or.inr ⟨hreg, hp5, hX5⟩)

theorem ggNbrTablePNbrInputOnL_bc_of_leaves
    (hT : GGTPNTransferBNoCorners) (hBS : GGK0ExcBS) :
    GGNbrTablePNbrInputOnL GGRegimeBCL :=
  ggNbrTablePNbrInputOnL_bc ggLabelRigidInput_holds hT ggI1OfPairL_holds
    E6TwoSeven.ggE6TwoSevenComp_holds
    (ggTablePKnownRK_bc (ggNonExcRK_holds GGRegimeBC)
      (ggClGenRK_of_regime fun p n labJ labX h lab hiso =>
        ggBc_regime_not_rankOne p n labJ labX h lab hiso)
      (ggBcClTypeARK_of_parts ggBcClRARK_holds ggBcClA5RK_holds) ggTablePKnownR_a8Seven
      (ggBcExcPairRK_holds hBS) (ggTablePKnownR_e6TwoSevenOut E6TwoSeven.ggE6TwoSevenComp_holds))


end CFSG.StandardType

end
