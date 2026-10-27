module

public import CFSG.LocalAnalysis.StandardType.GGA24Defs
public import CFSG.LocalAnalysis.StandardType.GGA24ExcPair
public import CFSG.LocalAnalysis.StandardType.GGTPNRegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNClGen
public import CFSG.LocalAnalysis.StandardType.GGTPNClassicalCover
public import CFSG.LocalAnalysis.StandardType.GGTPNExcCover
public import CFSG.LocalAnalysis.StandardType.GGTPNNonExc
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRAC1
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrowC6
public import CFSG.LocalAnalysis.StandardType.GGTPNI1
public import CFSG.LocalAnalysis.StandardType.GGTPNI1Holds
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTablePKnownRK_a24Classical
    (hGen : GGClGenRK GGRegimeA24) (hRA : GGTablePKnownR GGRegimeA24RA) :
    GGTablePKnownRK fun p n labJ labX => GGRegimeA24 p n labJ labX ∧ GGTPNClTag labX.tag := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨hreg, hcl⟩ := hr
  have hm : GGTPNMarked p (fun _ _ => True) A := hd.1.2.2.2.2.2.2.2
  rcases ggTPN_classicalCover hp hp2 hm hΛX hhX hcl with hg | hra | ⟨hp7, -⟩ | ⟨hp5, -⟩
  · exact hGen p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨hreg, hg⟩ hhJ hhX
  · exact hRA p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX ⟨hreg, hra⟩ hhJ hhX
  · have := hreg.1; omega
  · have := hreg.1; omega

theorem ggTablePKnownRK_a24Exc
    (hPair : GGA24ExcPairRK) :
    GGTablePKnownRK fun p n labJ labX => GGRegimeA24 p n labJ labX ∧ GGTPNExcTag labX.tag := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨hreg, hexc⟩ := hr
  have hm : GGTPNMarked p (fun _ _ => True) A := hd.1.2.2.2.2.2.2.2
  rcases ggTPN_excCover hp hp2 hm hΛX hhX hexc with hpair | ⟨hp7, -⟩
  · exact hPair p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨hreg, hpair⟩ hhJ hhX
  · have := hreg.1; omega

theorem ggTablePKnownRK_a24
    (hNon : GGNonExcRK GGRegimeA24)
    (hGen : GGClGenRK GGRegimeA24) (hRA : GGTablePKnownR GGRegimeA24RA)
    (hPair : GGA24ExcPairRK) : GGTablePKnownRK GGRegimeA24 := by
  refine GGTablePKnownRK.mono
    (GGTablePKnownRK.union (ggTablePKnownRK_a24Classical hGen hRA)
      (GGTablePKnownRK.union (ggTablePKnownRK_a24Exc hPair) hNon)) ?_
  intro p n labJ labX hJ
  by_cases hcl : GGTPNClTag labX.tag
  · exact Or.inl ⟨hJ, hcl⟩
  · by_cases hexc : GGTPNExcTag labX.tag
    · exact Or.inr (Or.inl ⟨hJ, hexc⟩)
    · exact Or.inr (Or.inr ⟨hJ, hcl, hexc⟩)

theorem ggNbrTablePNbrInputOnL_a24
    (hrig : GGLabelRigidInput) (hT : GGTPNTransferBNoCorners) (hI1 : GGI1OfPairL)
    (hK : GGTablePKnownRK GGRegimeA24) :
    GGNbrTablePNbrInputOnL GGRegimeA24L := by
  intro G _ _ p B Bs x L D J y K hc hL hKi hn labL labJ labK hΛL hΛJ hΛK hr hhL hhJ hhK
  have hpair : GGPairA24 p labL labJ := hr
  have hreg : GGRegimeA24 p (Nat.card Bs) labJ labK := hpair.regime _ labK
  obtain ⟨hJK, hN, hx, hBasic⟩ := hT G p B Bs x L D J y K hc hL hKi hn
  have hCJ := hI1 G p B Bs x L D J hc hL labL labJ hΛL hΛJ (Or.inl hpair) hhL hhJ
  have hker := ggTPNTrKernelI1_holds G p B Bs x L D J y K hc hL hKi hn hJK hN hx hCJ
  have hhJ' : GGHasLabel labJ (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)) :=
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK).symm hhJ
  have hcorners : GGTPNCorners p (J.subgroupOf K) :=
    ⟨fun hp7 _ => by have := hpair.1; omega,
      fun _ _ _ => ggTPNRankJ_of_a24 hrig hΛJ hreg hhJ'⟩
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

theorem ggNbrTablePNbrInputOnL_a24_of_leaves
    (hT : GGTPNTransferBNoCorners) (hBS : GGK0ExcBS) :
    GGNbrTablePNbrInputOnL GGRegimeA24L :=
  ggNbrTablePNbrInputOnL_a24 ggLabelRigidInput_holds hT ggI1OfPairL_holds
    (ggTablePKnownRK_a24 (ggNonExcRK_holds GGRegimeA24)
      (ggClGenRK_of_regime fun p n labJ labX h lab hiso =>
        ggA24_regime_not_rankOne p n labJ labX h lab hiso)
      (ggTablePKnownR_a24RA ggLabelRigidInput_holds) (ggA24ExcPairRK_holds hBS))

end CFSG.StandardType

end
