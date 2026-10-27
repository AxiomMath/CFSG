module

public import CFSG.LocalAnalysis.StandardType.GGTPNTwA6Defs
public import CFSG.LocalAnalysis.StandardType.GGTypeADefs
public import CFSG.LocalAnalysis.StandardType.GGExcRegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNClassicalCover
public import CFSG.LocalAnalysis.StandardType.GGTPNExcCover
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrowC6
public import CFSG.LocalAnalysis.StandardType.GGTPNI1
public import CFSG.LocalAnalysis.StandardType.GGTPNClGen
public import CFSG.LocalAnalysis.StandardType.GGTPNNonExc
public import CFSG.LocalAnalysis.StandardType.GGExcGen
public import CFSG.LocalAnalysis.StandardType.GGExcCentred
public import CFSG.LocalAnalysis.StandardType.GGK0ExcB3
import CFSG.LocalAnalysis.StandardType.GGTPNTwA6ClRA
import CFSG.LocalAnalysis.StandardType.GGTPNTwA6ExcOneThree
import CFSG.LocalAnalysis.StandardType.GGTPNTwA6E6Three

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTablePKnownRK_twA6Classical
    (hGen : GGClGenRK fun p n labJ labX => GGRegimeTwA6 p n labJ labX ∧ p.Prime ∧ p ≠ 2)
    :
    GGTablePKnownRK fun p n labJ labX => GGRegimeTwA6 p n labJ labX ∧ GGTPNClTag labX.tag := by
  have hRA := ggTwA6ClRARK_holds
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨hreg, hcl⟩ := hr
  have hm : GGTPNMarked p (fun _ _ => True) A := hd.1.2.2.2.2.2.2.2
  rcases ggTPN_classicalCover hp hp2 hm hΛX hhX hcl with hg | hra | ⟨hp7, -⟩ | ⟨hp5, -⟩
  · exact hGen p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨⟨hreg, hp, hp2⟩, hg⟩ hhJ hhX
  · exact hRA p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨hreg, hra⟩ hhJ hhX
  · exact absurd (hreg.1.symm.trans hp7) (by norm_num)
  · exact absurd (hreg.1.symm.trans hp5) (by norm_num)

theorem ggTablePKnownRK_twA6Exc
    (hGenE : GGExcGenRK GGRegimeTwA6) (hC : GGExcCentredRK GGRegimeTwA6)
    (hO : GGTwA6ExcOneThreeRK) (hE : GGTwA6E6ThreeRK) :
    GGTablePKnownRK fun p n labJ labX => GGRegimeTwA6 p n labJ labX ∧ GGTPNExcTag labX.tag := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨hreg, hexc⟩ := hr
  have hm : GGTPNMarked p (fun _ _ => True) A := hd.1.2.2.2.2.2.2.2
  rcases ggTPN_excCover hp hp2 hm hΛX hhX hexc with hpair | ⟨hp7, -⟩
  · by_cases hg : GGKacGeneric labX p
    · exact hGenE p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨hreg, hg⟩ hhJ hhX
    · have hRE : GGKacRE labX p := ggKacRE_of_excPair_of_not_generic hpair hg
      rcases ggKacRE_cases hRE with hq | ho | h3
      · exact hC p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨hreg, hq⟩ hhJ hhX
      · exact hO p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨hreg, ho⟩ hhJ hhX
      · exact hE p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX
          ⟨hreg, h3.1, h3.2, hRE.toExcPair⟩ hhJ hhX
  · exact absurd (hreg.1.symm.trans hp7) (by norm_num)

theorem ggTablePKnownRK_twA6
    (hNon : GGNonExcRK GGRegimeTwA6)
    (hGen : GGClGenRK fun p n labJ labX => GGRegimeTwA6 p n labJ labX ∧ p.Prime ∧ p ≠ 2)
    (hGenE : GGExcGenRK GGRegimeTwA6) (hC : GGExcCentredRK GGRegimeTwA6)
    (hO : GGTwA6ExcOneThreeRK) (hE : GGTwA6E6ThreeRK) : GGTablePKnownRK GGRegimeTwA6 := by
  refine GGTablePKnownRK.mono
    (GGTablePKnownRK.union (ggTablePKnownRK_twA6Classical hGen)
      (GGTablePKnownRK.union (ggTablePKnownRK_twA6Exc hGenE hC hO hE) hNon)) ?_
  intro p n labJ labX hJ
  by_cases hcl : GGTPNClTag labX.tag
  · exact Or.inl ⟨hJ, hcl⟩
  · by_cases hexc : GGTPNExcTag labX.tag
    · exact Or.inr (Or.inl ⟨hJ, hexc⟩)
    · exact Or.inr (Or.inr ⟨hJ, hcl, hexc⟩)

theorem ggNbrTablePNbrInputI1On_twA6 (hrig : GGLabelRigidInput) (hT : GGTPNTransferBNoCorners)
    (hK : GGTablePKnownRK GGRegimeTwA6) : GGNbrTablePNbrInputI1On GGRegimeTwA6 := by
  intro G _ _ p B Bs x L D J y K hc hL hKi hn hI1 labJ labK hΛJ hΛK hr hhJ hhK
  have hβ := hc.1.2.2.2.2.2.1
  obtain ⟨hJK, hN, hx, hBasic⟩ := hT G p B Bs x L D J y K hc hL hKi hn
  have hker := ggTPNTrKernelI1_holds G p B Bs x L D J y K hc hL hKi hn hJK hN hx hI1
  have hhJ' : GGHasLabel labJ (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)) :=
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK).symm hhJ
  have hcorners : GGTPNCorners p (J.subgroupOf K) := by
    obtain ⟨hp3, -, ht, hrk, -⟩ := hr
    exact ⟨fun hp7 _ => absurd (hp3.symm.trans hp7) (by norm_num),
      fun _ _ _ => ggTPNRankJ_of_twA6 hrig ht hrk hΛJ hhJ'⟩
  have hD : GGTPNDatumB p (Nat.card Bs) (fun _ _ => True) (ggAutsOf K Bs hN)
      (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) :=
    ⟨hBasic, hcorners⟩
  obtain ⟨labJ', labX', hΛJ', hΛX', hrow, hJ', hX'⟩ :=
    hK p hβ.1 hβ.2.1 ↥K (ggAutsOf K Bs hN) (ggAutsOf K B (hc.2.1.1.trans hN))
      (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) (Nat.card Bs) hD hker labJ labK hΛJ hΛK
      hr hhJ' hhK
  exact ⟨labJ', labX', hΛJ', hΛX', hrow,
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) hJ', hX'⟩

theorem ggTablePKnownRK_twA6_of_B3
    (hB3 : GGK0ExcB3) : GGTablePKnownRK GGRegimeTwA6 :=
  ggTablePKnownRK_twA6 (ggNonExcRK_holds GGRegimeTwA6)
    (ggClGenRK_of_regime
      (R := fun p n labJ labX => GGRegimeTwA6 p n labJ labX ∧ p.Prime ∧ p ≠ 2)
      fun _ _ _ _ h lab hiso => ggRegimeTwA6_not_pRankOne h.1 lab hiso)
    (ggExcGenRK_holds (ggK0ExcBS_of_B3 hB3) GGRegimeTwA6)
    (ggExcCentredRK_holds hB3 GGRegimeTwA6) (ggTwA6ExcOneThree_holds (ggK0ExcBS_of_B3 hB3))
    (ggTwA6E6Three_holds (ggK0ExcBS_of_B3 hB3))

theorem ggNbrTablePNbrInputI1On_twA6_of_leaves
    (hT : GGTPNTransferBNoCorners) (hB3 : GGK0ExcB3) : GGNbrTablePNbrInputI1On GGRegimeTwA6 :=
  ggNbrTablePNbrInputI1On_twA6 ggLabelRigidInput_holds hT (ggTablePKnownRK_twA6_of_B3 hB3)

end CFSG.StandardType

end
