module

public import CFSG.LocalAnalysis.StandardType.GGN2Defs
public import CFSG.LocalAnalysis.StandardType.GGN2NotRankOne
public import CFSG.LocalAnalysis.StandardType.GGN2I1
public import CFSG.LocalAnalysis.StandardType.GGN2ExcPair
public import CFSG.LocalAnalysis.StandardType.GGN2RA
public import CFSG.LocalAnalysis.StandardType.GGTPNRegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNClGen
public import CFSG.LocalAnalysis.StandardType.GGTPNClassicalCover
public import CFSG.LocalAnalysis.StandardType.GGTPNExcCover
public import CFSG.LocalAnalysis.StandardType.GGTPNNonExc
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrowC6
public import CFSG.LocalAnalysis.StandardType.GGTPNI1
public import CFSG.LocalAnalysis.StandardType.GGTPNI1Gen
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTablePKnownRK_n2Classical
    (hGen : GGClGenRK GGRegimeN2) (hRA : GGTablePKnownR GGRegimeN2RA) :
    GGTablePKnownRK fun p n labJ labX => GGRegimeN2 p n labJ labX ∧ GGTPNClTag labX.tag := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨hreg, hcl⟩ := hr
  have hm : GGTPNMarked p (fun _ _ => True) A := hd.1.2.2.2.2.2.2.2
  rcases ggTPN_classicalCover hp hp2 hm hΛX hhX hcl with hg | hra | ⟨hp7, -⟩ | ⟨hp5, -⟩
  · exact hGen p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨hreg, hg⟩ hhJ hhX
  · exact hRA p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX ⟨hreg, hra⟩ hhJ hhX
  · have := hreg.1; omega
  · have := hreg.1; omega

theorem ggTablePKnownRK_n2Exc
    (hPair : GGN2ExcPairRK) :
    GGTablePKnownRK fun p n labJ labX => GGRegimeN2 p n labJ labX ∧ GGTPNExcTag labX.tag := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨hreg, hexc⟩ := hr
  have hm : GGTPNMarked p (fun _ _ => True) A := hd.1.2.2.2.2.2.2.2
  rcases ggTPN_excCover hp hp2 hm hΛX hhX hexc with hpair | ⟨hp7, -⟩
  · exact hPair p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨hreg, hpair⟩ hhJ hhX
  · have := hreg.1; omega

theorem ggTablePKnownRK_n2
    (hNon : GGNonExcRK GGRegimeN2) (hGen : GGClGenRK GGRegimeN2)
    (hRA : GGTablePKnownR GGRegimeN2RA) (hPair : GGN2ExcPairRK) :
    GGTablePKnownRK GGRegimeN2 := by
  refine GGTablePKnownRK.mono
    (GGTablePKnownRK.union (ggTablePKnownRK_n2Classical hGen hRA)
      (GGTablePKnownRK.union (ggTablePKnownRK_n2Exc hPair) hNon)) ?_
  intro p n labJ labX hJ
  by_cases hcl : GGTPNClTag labX.tag
  · exact Or.inl ⟨hJ, hcl⟩
  · by_cases hexc : GGTPNExcTag labX.tag
    · exact Or.inr (Or.inl ⟨hJ, hexc⟩)
    · exact Or.inr (Or.inr ⟨hJ, hcl, hexc⟩)

theorem ggNbrTablePNbrInputOnL_n2
    (hrig : GGLabelRigidInput) (hT : GGTPNTransferBNoCorners) (hI1 : GGI1OfPairLOn GGPairN2)
    (hK : GGTablePKnownRK GGRegimeN2) :
    GGNbrTablePNbrInputOnL GGRegimeN2L := by
  intro G _ _ p B Bs x L D J y K hc hL hKi hn labL labJ labK hΛL hΛJ hΛK hr hhL hhJ hhK
  obtain ⟨hp3, hcard, hlabL, hlabJ⟩ := hr
  have hpair : GGPairN2 p labL labJ := ⟨hp3, hlabL, hlabJ⟩
  have hreg : GGRegimeN2 p (Nat.card Bs) labJ labK := ⟨hp3, hcard, hlabJ⟩
  obtain ⟨hJK, hN, hx, hBasic⟩ := hT G p B Bs x L D J y K hc hL hKi hn
  have hCJ := hI1 G p B Bs x L D J hc hL labL labJ hΛL hΛJ hpair hhL hhJ
  have hker := ggTPNTrKernelI1_holds G p B Bs x L D J y K hc hL hKi hn hJK hN hx hCJ
  have hhJ' : GGHasLabel labJ (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)) :=
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK).symm hhJ
  have hcorners : GGTPNCorners p (J.subgroupOf K) :=
    ⟨fun hp7 _ => by have := hpair.1; omega,
      fun _ _ _ => ggTPNRankJ_of_n2 hrig hΛJ hreg hhJ'⟩
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

theorem ggNbrTablePNbrInputOnL_n2_of_leaves
    (hT : GGTPNTransferBNoCorners) (hB : GGK0ExcB) :
    GGNbrTablePNbrInputOnL fun p n labL labJ _ =>
      p = 3 ∧ n = 3 ^ 5 ∧ labL = ⟨.D, 4, 1⟩ ∧ labJ = ⟨.twA, 3, 1⟩ :=
  ggNbrTablePNbrInputOnL_n2 ggLabelRigidInput_holds hT (ggI1OfPairLOn_of_rank ggI1PairRankOn_n2)
    (ggTablePKnownRK_n2 (ggNonExcRK_holds GGRegimeN2)
      (ggClGenRK_of_regime fun p n labJ labX h lab hiso =>
        ggN2_regime_not_rankOne p n labJ labX h lab hiso)
      ggTablePKnownR_n2RA (ggN2ExcPairRK_holds hB))

end CFSG.StandardType

end
