module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDTablePDefs
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
import CFSG.LocalAnalysis.StandardType.GGQTwoDTablePClRA
import CFSG.LocalAnalysis.StandardType.GGQTwoDTablePExc
import CFSG.LocalAnalysis.StandardType.GGQTwoDE7SU6CofHolds
import CFSG.LocalAnalysis.StandardType.GGK0ExcB3Holds
import CFSG.LocalAnalysis.StandardType.GGTPNNarrowC6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTablePKnownRK_delUClassical
    (hGen : GGClGenRK fun p n labJ labX =>
      GGRegimeDeletedUnitary1836 p n labJ labX ∧ p.Prime ∧ p ≠ 2)
    :
    GGTablePKnownRK fun p n labJ labX =>
      GGRegimeDeletedUnitary1836 p n labJ labX ∧ GGTPNClTag labX.tag := by
  have hRA := ggDelUClRARK_holds
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨hreg, hcl⟩ := hr
  have hm : GGTPNMarked p (fun _ _ => True) A := hd.1.2.2.2.2.2.2.2
  rcases ggTPN_classicalCover hp hp2 hm hΛX hhX hcl with hg | hra | ⟨hp7, -⟩ | ⟨hp5, -⟩
  · exact hGen p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨⟨hreg, hp, hp2⟩, hg⟩ hhJ hhX
  · exact hRA p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨hreg, hra⟩ hhJ hhX
  · exact absurd (hreg.1.symm.trans hp7) (by norm_num)
  · exact absurd (hreg.1.symm.trans hp5) (by norm_num)

theorem ggTablePKnownRK_delUExc
    (hGenE : GGExcGenRK GGRegimeDeletedUnitary1836)
    (hC : GGExcCentredRK GGRegimeDeletedUnitary1836)
    (hO : GGDelUExcOneThreeRK) (hE : GGDelUE6ThreeRK) :
    GGTablePKnownRK fun p n labJ labX =>
      GGRegimeDeletedUnitary1836 p n labJ labX ∧ GGTPNExcTag labX.tag := by
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

theorem ggTablePKnownRK_delU
    (hNon : GGNonExcRK GGRegimeDeletedUnitary1836)
    (hGen : GGClGenRK fun p n labJ labX =>
      GGRegimeDeletedUnitary1836 p n labJ labX ∧ p.Prime ∧ p ≠ 2)
    (hGenE : GGExcGenRK GGRegimeDeletedUnitary1836)
    (hC : GGExcCentredRK GGRegimeDeletedUnitary1836)
    (hO : GGDelUExcOneThreeRK) (hE : GGDelUE6ThreeRK) :
    GGTablePKnownRK GGRegimeDeletedUnitary1836 := by
  refine GGTablePKnownRK.mono
    (GGTablePKnownRK.union (ggTablePKnownRK_delUClassical hGen)
      (GGTablePKnownRK.union (ggTablePKnownRK_delUExc hGenE hC hO hE) hNon)) ?_
  intro p n labJ labX hJ
  by_cases hcl : GGTPNClTag labX.tag
  · exact Or.inl ⟨hJ, hcl⟩
  · by_cases hexc : GGTPNExcTag labX.tag
    · exact Or.inr (Or.inl ⟨hJ, hexc⟩)
    · exact Or.inr (Or.inr ⟨hJ, hcl, hexc⟩)

theorem ggNbrTablePNbrInputI1On_delU (hrig : GGLabelRigidInput) (hT : GGTPNTransferBNoCorners)
    (hK : GGTablePKnownRK GGRegimeDeletedUnitary1836) :
    GGNbrTablePNbrInputI1On GGRegimeDeletedUnitary1836 := by
  intro G _ _ p B Bs x L D J y K hc hL hKi hn hI1 labJ labK hΛJ hΛK hr hhJ hhK
  have hβ := hc.1.2.2.2.2.2.1
  obtain ⟨hJK, hN, hx, hBasic⟩ := hT G p B Bs x L D J y K hc hL hKi hn
  have hker := ggTPNTrKernelI1_holds G p B Bs x L D J y K hc hL hKi hn hJK hN hx hI1
  have hhJ' : GGHasLabel labJ (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)) :=
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK).symm hhJ
  have hcorners : GGTPNCorners p (J.subgroupOf K) := by
    obtain ⟨hp3, d, hd, -, hl⟩ := hr
    exact ⟨fun hp7 _ => absurd (hp3.symm.trans hp7) (by norm_num),
      fun _ _ _ => ggTPNRankJ_of_deletedUnitary1836 hrig hd hl hΛJ hhJ'⟩
  have hD : GGTPNDatumB p (Nat.card Bs) (fun _ _ => True) (ggAutsOf K Bs hN)
      (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) :=
    ⟨hBasic, hcorners⟩
  obtain ⟨labJ', labX', hΛJ', hΛX', hrow, hJ', hX'⟩ :=
    hK p hβ.1 hβ.2.1 ↥K (ggAutsOf K Bs hN) (ggAutsOf K B (hc.2.1.1.trans hN))
      (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) (Nat.card Bs) hD hker labJ labK hΛJ hΛK
      hr hhJ' hhK
  exact ⟨labJ', labX', hΛJ', hΛX', hrow,
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) hJ', hX'⟩

theorem ggTablePKnownRK_delU_of_B3
    (hB3 : GGK0ExcB3) : GGTablePKnownRK GGRegimeDeletedUnitary1836 :=
  ggTablePKnownRK_delU (ggNonExcRK_holds GGRegimeDeletedUnitary1836)
    (ggClGenRK_of_regime
      (R := fun p n labJ labX => GGRegimeDeletedUnitary1836 p n labJ labX ∧ p.Prime ∧ p ≠ 2)
      fun _ _ _ _ h lab hiso => ggRegimeDeletedUnitary1836_not_pRankOne h.1 lab hiso)
    (ggExcGenRK_holds (ggK0ExcBS_of_B3 hB3) GGRegimeDeletedUnitary1836)
    (ggExcCentredRK_holds hB3 GGRegimeDeletedUnitary1836)
    (ggDelUExcOneThree_holds (ggK0ExcBS_of_B3 hB3) ggQTwoDE7SU6Cof_holds)
    (ggDelUE6Three_holds (ggK0ExcBS_of_B3 hB3))

theorem ggNbrTablePNbrInputI1On_delU_of_leaves
    (hT : GGTPNTransferBNoCorners) (hB3 : GGK0ExcB3) :
    GGNbrTablePNbrInputI1On GGRegimeDeletedUnitary1836 :=
  ggNbrTablePNbrInputI1On_delU ggLabelRigidInput_holds hT (ggTablePKnownRK_delU_of_B3 hB3)

theorem ggNbrTablePNbrInputI1On_delU_of_transfer
    (hT : GGTPNTransferBNoCorners) : GGNbrTablePNbrInputI1On GGRegimeDeletedUnitary1836 :=
  ggNbrTablePNbrInputI1On_delU_of_leaves hT GGK0ExcB3Prod.ggK0ExcB3_holds

theorem ggTablePRow_delU_of_config
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hc : GGConfig p B Bs x L D J) (hL : GGInnerDiagOn Bs L)
    (hKi : GGInnerDiagOn Bs K) (hn : GGNbr p B x D J y K)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) (hJK : J ≤ K) (hpJ : p ∣ Nat.card J)
    (hLB : GGLBalanceInput) {labJ labK : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hΛK : LargeEvenInLambda2 labK) (hr : GGRegimeDeletedUnitary1836 p (Nat.card Bs) labJ labK)
    (hhJ : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hhK : GGHasLabel labK (K ⧸ Subgroup.center K)) :
    ∃ labJ' labK' : LargeEvenLabel, LargeEvenInLambda2 labJ' ∧ LargeEvenInLambda2 labK' ∧
      GGTablePRow p labJ' labK' ∧
      GGHasLabel labJ' (J ⧸ Subgroup.center J) ∧ GGHasLabel labK' (K ⧸ Subgroup.center K) := by
  have hβ := hc.1.2.2.2.2.2.1
  obtain ⟨hN, hx, hBasic⟩ := ggTPNBasicB_of_config hc hL hKi hn hJK hpJ hLB
  have hker := ggTPNTrKernelI1_holds G p B Bs x L D J y K hc hL hKi hn hJK hN hx hI1
  have hhJ' : GGHasLabel labJ (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)) :=
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK).symm hhJ
  have hcorners : GGTPNCorners p (J.subgroupOf K) := by
    obtain ⟨hp3, d, hd, -, hl⟩ := hr
    exact ⟨fun hp7 _ => absurd (hp3.symm.trans hp7) (by norm_num),
      fun _ _ _ => ggTPNRankJ_of_deletedUnitary1836 ggLabelRigidInput_holds hd hl hΛJ hhJ'⟩
  have hD : GGTPNDatumB p (Nat.card Bs) (fun _ _ => True) (ggAutsOf K Bs hN)
      (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) :=
    ⟨hBasic, hcorners⟩
  obtain ⟨labJ', labX', hΛJ', hΛX', hrow, hJ', hX'⟩ :=
    ggTablePKnownRK_delU_of_B3 GGK0ExcB3Prod.ggK0ExcB3_holds p hβ.1 hβ.2.1 ↥K (ggAutsOf K Bs hN)
      (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K)
      (Nat.card Bs) hD hker labJ labK hΛJ hΛK hr hhJ' hhK
  exact ⟨labJ', labX', hΛJ', hΛX', hrow,
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) hJ', hX'⟩

end CFSG.StandardType

end
