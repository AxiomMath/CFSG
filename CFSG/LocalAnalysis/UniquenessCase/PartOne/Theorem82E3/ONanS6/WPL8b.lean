module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL6

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

theorem inCatalog_component_centerQuot (c : Ctx82E3 D) {e : G} (he1 : e ≠ 1)
    {J : Subgroup (componentsQuot e)} (hJ : CFSG.IsComponent J) :
    CFSG.Assembly.InCatalog (J ⧸ Subgroup.center J) := by
  classical
  have hK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({e} : Set G)) :=
    isKGroup_centralizer (D := D) c he1
  let π : ↥(Subgroup.centralizer ({e} : Set G)) →* componentsQuot e :=
    QuotientGroup.mk' (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
      ↥(Subgroup.centralizer ({e} : Set G)))
  have hX : CFSG.Open.IsKGroup (componentsQuot e) := hK.of_surjective π
    (QuotientGroup.mk'_surjective _)
  haveI : IsSimpleGroup (J ⧸ Subgroup.center J) := hJ.1.2.1
  exact hX.isCatalogGroup_of_surjective J hJ.1.2.2
    (QuotientGroup.mk' (Subgroup.center J)) (QuotientGroup.mk'_surjective _)

theorem exists_suzukiModel_component (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz)
    (c : Ctx82E3 D) (P : Subgroup G) {e : G}
    (hZ3 : ∀ J ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card J →
      Nat.card (autThetaQuot (zSub P c.L) J) = 1)
    (he1 : e ≠ 1)
    {J : Subgroup (componentsQuot e)} (hJ : CFSG.IsComponent J)
    (hntriv : ¬ TrivialZComponentAction (D := D) c P e J) :
    ∃ f : ℕ, CFSG.Blueprint.SuzukiModel (J ⧸ Subgroup.center J) 2 f := by
  classical
  have hJ3 : ¬ 3 ∣ Nat.card J :=
    not_three_dvd_card_of_nontrivial e c P hZ3 hJ hntriv
  have h3q : ¬ 3 ∣ Nat.card (J ⧸ Subgroup.center J) := by
    intro h3
    apply hJ3
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center J)]
    exact dvd_mul_of_dvd_left h3 _
  have hcat : CFSG.Assembly.InCatalog (J ⧸ Subgroup.center J) :=
    inCatalog_component_centerQuot c he1 hJ
  haveI : IsSimpleGroup (J ⧸ Subgroup.center J) := hJ.1.2.1
  exact hPSz (J ⧸ Subgroup.center J) hJ.1.2.2 hcat h3q

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
