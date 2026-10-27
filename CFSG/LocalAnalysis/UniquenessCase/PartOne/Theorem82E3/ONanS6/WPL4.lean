module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG
open CFSG.RankThree.LocalRank
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
variable {G : Type} [Group G] [Finite G] {D : Data G}

noncomputable abbrev componentsQuot (e : G) : Type :=
  ↥(Subgroup.centralizer ({e} : Set G)) ⧸
    CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
      ↥(Subgroup.centralizer ({e} : Set G))

noncomputable abbrev componentsImage (e : G) : Subgroup (componentsQuot e) :=
  (((Subgroup.centralizer ({e} : Set G) ⊓ CFSG.Open.pCoreOf 2 D.M).subgroupOf
      (Subgroup.centralizer ({e} : Set G))).map
    (QuotientGroup.mk' (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
      ↥(Subgroup.centralizer ({e} : Set G)))))

@[expose] def TrivialZComponentAction (c : Ctx82E3 D) (P : Subgroup G) (e : G)
    (J : Subgroup (componentsQuot e)) : Prop :=
  ∃ L ∈ thetaComponentsAt 3 e,
    (L.subgroupOf (Subgroup.centralizer ({e} : Set G))).map
        (QuotientGroup.mk' (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
          ↥(Subgroup.centralizer ({e} : Set G)))) = J ∧
      Nat.card (autThetaQuot (zSub P c.L) L) = 1

@[expose] def ComponentsStepTwoConfig (c : Ctx82E3 D) (P : Subgroup G) (e : G) : Prop :=
  ∀ J : Subgroup (componentsQuot e), CFSG.IsComponent J →
    TrivialZComponentAction (D := D) c P e J →
      J ≤ Subgroup.normalizer ((componentsImage (D := D) e : Subgroup _) : Set _) ∧
        componentsImage (D := D) e ≤ Subgroup.normalizer (J : Set _)

theorem components_step2 {X : Type*} [Group X] [Finite X] {K W : Subgroup X}
    (hK : CFSG.IsComponent K) (hW2 : IsPGroup 2 W)
    (hKW : K ≤ Subgroup.normalizer (W : Set X))
    (hWK : W ≤ Subgroup.normalizer (K : Set X)) :
    ⁅K, W⁆ = ⊥ := by
  classical
  have hcommW : ⁅K, W⁆ ≤ W := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.le_normalizer_iff_commutator_le_left).mp hKW
  have hcommK : ⁅K, W⁆ ≤ K :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hWK
  have hnormal : ((⁅K, W⁆).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcommK).mpr
      (Subgroup.normalizer_commutator_ge_left K W)
  have h2 : IsPGroup 2 ((⁅K, W⁆).subgroupOf K) :=
    (hW2.to_le hcommW).of_equiv (Subgroup.subgroupOfEquivOfLe hcommK).symm
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hK.1 hnormal with htop | hcenter
  · exfalso
    haveI : Group.IsPerfect K := hK.1.1
    haveI : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
    have htop2 : IsPGroup 2 (⊤ : Subgroup K) := htop ▸ h2
    haveI : Group.IsNilpotent ↥(⊤ : Subgroup K) := htop2.isNilpotent
    have hnil : Group.IsNilpotent K :=
      Group.nilpotent_of_mulEquiv (Subgroup.topEquiv (G := K))
    exact Group.IsPerfect.not_isNilpotent K hnil
  · have hcentX : ⁅K, W⁆ ≤ Subgroup.centralizer (K : Set X) := by
      intro q hq k hk
      have hqK : q ∈ K := hcommK hq
      have hqcenter : (⟨q, hqK⟩ : K) ∈ Subgroup.center K :=
        hcenter (Subgroup.mem_subgroupOf.mpr hq)
      rw [Subgroup.mem_center_iff] at hqcenter
      simpa using congrArg Subtype.val (hqcenter ⟨k, hk⟩)
    have hdouble : ⁅⁅K, W⁆, K⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentX
    exact CFSG.LocalCores.perfect_double_commutator hK.1.1 hdouble

theorem components_step2_context (c : Ctx82E3 D) (P : Subgroup G) (e : G)
    (hStep2 : ComponentsStepTwoConfig (D := D) c P e)
    {J : Subgroup (componentsQuot e)} (hJ : CFSG.IsComponent J)
    (htriv : TrivialZComponentAction (D := D) c P e J) :
    componentsImage (D := D) e ≤ Subgroup.centralizer (J : Set _) := by
  obtain ⟨hKW, hWK⟩ := hStep2 J hJ htriv
  have hW2 : IsPGroup 2 (componentsImage (D := D) e) := by
    let W : Subgroup G := Subgroup.centralizer ({e} : Set G) ⊓ CFSG.Open.pCoreOf 2 D.M
    have hQ2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 D.M) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M
    have hWQ : W ≤ CFSG.Open.pCoreOf 2 D.M := inf_le_right
    have hWQ2 : IsPGroup 2 (W.subgroupOf (CFSG.Open.pCoreOf 2 D.M)) :=
      hQ2.to_subgroup _
    have hW2G : IsPGroup 2 W :=
      hWQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hWQ)
    have hW2H : IsPGroup 2 (W.subgroupOf (Subgroup.centralizer ({e} : Set G))) :=
      hW2G.of_equiv (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : W ≤ Subgroup.centralizer ({e} : Set G))).symm
    let π : ↥(Subgroup.centralizer ({e} : Set G)) →* componentsQuot e :=
      QuotientGroup.mk' (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
        ↥(Subgroup.centralizer ({e} : Set G)))
    simpa [componentsImage, W, π] using IsPGroup.map hW2H π
  have hcomm : ⁅J, componentsImage (D := D) e⁆ = ⊥ :=
    components_step2 hJ hW2 hKW hWK
  have hcomm' : ⁅componentsImage (D := D) e, J⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hcomm
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm'

@[expose] def SuzukiComponentStep
    (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz)
    (hSzB : Sz.SzBorel) (hSzO : Sz.SzOutOdd) (hSzF : Sz.SzFix) (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (P : Subgroup G) (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (e : G) (hP3 : CFSG.Open.pRank 7 (Subgroup.centralizer ({e} : Set G)) = 1)
    (hZ3 : ∀ J ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card J →
      Nat.card (autThetaQuot (zSub P c.L) J) = 1)
    (he : e ∈ P ⊓ c.L) (he3 : orderOf e = 3) (heZ : e ∉ zSub P c.L) : Prop :=
  ∀ J : Subgroup (componentsQuot e), CFSG.IsComponent J →
    ¬ TrivialZComponentAction (D := D) c P e J →
      componentsImage (D := D) e ≤ Subgroup.centralizer (J : Set _)

theorem components_step3
    (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz)
    (hSzB : Sz.SzBorel) (hSzO : Sz.SzOutOdd) (hSzF : Sz.SzFix) (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (P : Subgroup G) (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (e : G) (hP3 : CFSG.Open.pRank 7 (Subgroup.centralizer ({e} : Set G)) = 1)
    (hZ3 : ∀ J ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card J →
      Nat.card (autThetaQuot (zSub P c.L) J) = 1)
    (he : e ∈ P ⊓ c.L) (he3 : orderOf e = 3) (heZ : e ∉ zSub P c.L)
    (hStep3 : SuzukiComponentStep (D := D) hPSz hSzB hSzO hSzF c hON h7
      P hNZ e hP3 hZ3 he he3 heZ)
    {J : Subgroup (componentsQuot e)} (hJ : CFSG.IsComponent J)
    (hntriv : ¬ TrivialZComponentAction (D := D) c P e J) :
    componentsImage (D := D) e ≤ Subgroup.centralizer (J : Set _) :=
  hStep3 J hJ hntriv

theorem pcore_centralizer_le_theta_components'
    (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz)
    (hSzB : Sz.SzBorel) (hSzO : Sz.SzOutOdd) (hSzF : Sz.SzFix) (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    {e : G} (hP3 : CFSG.Open.pRank 7 (Subgroup.centralizer ({e} : Set G)) = 1)
    (hZ3 : ∀ J ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card J →
      Nat.card (autThetaQuot (zSub P c.L) J) = 1)
    (he : e ∈ P ⊓ c.L) (he3 : orderOf e = 3) (heZ : e ∉ zSub P c.L)
    (hStep2 : ComponentsStepTwoConfig (D := D) c P e)
    (hStep3 : SuzukiComponentStep (D := D) hPSz hSzB hSzO hSzF c hON h7 P hNZ e hP3 hZ3
      he he3 heZ) :
    ∀ J : Subgroup (componentsQuot e), CFSG.IsComponent J →
      (((Subgroup.centralizer ({e} : Set G) ⊓ CFSG.Open.pCoreOf 2 D.M).subgroupOf
          (Subgroup.centralizer ({e} : Set G))).map
        (QuotientGroup.mk' (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
          ↥(Subgroup.centralizer ({e} : Set G))))) ≤
      Subgroup.centralizer (J : Set _) := by
  intro J hJ
  by_cases htriv : TrivialZComponentAction (D := D) c P e J
  · exact components_step2_context c P e hStep2 hJ htriv
  · exact components_step3 hPSz hSzB hSzO hSzF c hON h7 P hNZ e hP3 hZ3 he he3 heZ hStep3 hJ htriv

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
