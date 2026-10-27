module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestSetup
public import CFSG.LocalAnalysis.StandardType.GGSporKRestComp
public import CFSG.LocalAnalysis.StandardType.GGSporKRestTransportMark
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenE6Components

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint
  CFSG.ComponentClassification.OuterAutomorphisms

private theorem ggSporKRestL11s_isComponentOf_subgroupOf {W : Type} [Group W] {H F C : Subgroup W}
    (hCF : C ≤ F) (hC : IsComponentOf C (H ⊓ F)) :
    IsComponentOf (C.subgroupOf F) (H.subgroupOf F) := by
  have h := ggIsComponentOf_subgroupOf_of_le F hCF hC
  rwa [Subgroup.inf_subgroupOf_right H F] at h

private theorem ggSporKRestL11s_lieModel_centerQuot {W : Type} [Group W] {F C : Subgroup W}
    (hCF : C ≤ F)
    (h : LieModel (↥(C.subgroupOf F) ⧸ Subgroup.center ↥(C.subgroupOf F)) .POmegaPlus 4 2 1) :
    LieModel (↥C ⧸ Subgroup.center ↥C) .POmegaPlus 4 2 1 :=
  ggLieModel_centerQuot_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hCF).symm h

theorem ggSporKRest_not_unmarked {W : Type} [Group W] [Finite W] {p : ℕ} {H E : Subgroup W}
    (hyp : GGHypThreeSixteenFlat p H E)
    (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥)
    (hOut : Nat.card (Outer ↥(CFSG.generalizedFitting W)) ≤ 2) :
    ¬ SporKRestUnmarked ↥(H.subgroupOf (CFSG.generalizedFitting W)) := by
  intro hU
  let F : Subgroup W := CFSG.generalizedFitting W
  let N : Subgroup W := H ⊓ F
  have hFn : F.Normal := (CFSG.LocalCores.generalized_fitting_characteristic (G := W)).2
  have hNH : N ≤ H := inf_le_left
  have hNsub : N.subgroupOf H = F.subgroupOf H := Subgroup.inf_subgroupOf_left F H
  have hNnorm : (N.subgroupOf H).Normal := by
    rw [hNsub]
    exact Subgroup.normal_subgroupOf
  have hidx : (N.subgroupOf H).index ≤ 2 := by
    have hrel : (N.subgroupOf H).index = F.relIndex H := by
      rw [hNsub]
      rfl
    rw [hrel]
    have hdiv : F.relIndex H ∣ F.index := Subgroup.relIndex_dvd_index_of_normal F H
    have hle : F.index ≤ 2 := le_trans (ggSporKRest_index_fstar_le (W := W)) hOut
    have hpos : 0 < F.index :=
      Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (G := W) (H := F))
    exact le_trans (Nat.le_of_dvd hpos hdiv) hle
  obtain ⟨C, hC⟩ := ggSporKRest_exists_component_of_layer (X := GGHypQuot H) hL
  have hmarkC : LargeEvenMarking ↥C (fun _ _ _ _ _ _ => True) :=
    ggSporKRest_marking_true_of_marking (hyp.2.2.1 C hC).2
  obtain ⟨C', hC'comp, ⟨eCC'⟩⟩ :=
    ggSporKRest_component_transfer (W := W) (H := H) (N := N) hNH hNnorm hidx C hC
  have hmarkC' : LargeEvenMarking ↥C' (fun _ _ _ _ _ _ => True) :=
    ggSporKRest_marking_true_of_mulEquiv eCC' hmarkC
  have hNsubF : N.subgroupOf F = H.subgroupOf F := Subgroup.inf_subgroupOf_right H F
  let eHN : ↥(H.subgroupOf F) ≃* ↥N :=
    (MulEquiv.subgroupCongr hNsubF.symm).trans
      (Subgroup.subgroupOfEquivOfLe (H := N) (K := F) inf_le_right)
  have hUN : SporKRestUnmarked ↥N := SporKRestUnmarked.of_mulEquiv eHN hU
  exact (hUN C' hC'comp) hmarkC'

theorem ggSporKRest_false_of_coverOrUnmarked {W : Type} [Group W] [Finite W] {p : ℕ}
    {H E : Subgroup W} (hyp : GGHypThreeSixteenFlat p H E)
    (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥)
    (hK : ¬ CFSG.generalizedFitting W ≤ H)
    (hOut : Nat.card (Outer ↥(CFSG.generalizedFitting W)) ≤ 2)
    (hCov : SporKRestCoverOrUnmarked p ↥(CFSG.generalizedFitting W)) : False := by
  obtain ⟨_, hEab, hE2, ⟨S, hSH⟩, hctl⟩ := ggSporKRest_setup hyp hOut
  rcases hCov (E.subgroupOf (CFSG.generalizedFitting W)) hEab hE2 with
    ⟨x, hxE, hx1, hgen⟩ | hrest
  · have hHF : H.subgroupOf (CFSG.generalizedFitting W) = ⊤ :=
      hgen (H.subgroupOf (CFSG.generalizedFitting W)) ⟨S, hSH⟩ (hctl x hxE hx1)
    refine hK (fun f hf => ?_)
    have hx : (⟨f, hf⟩ : ↥(CFSG.generalizedFitting W)) ∈
        H.subgroupOf (CFSG.generalizedFitting W) := by
      rw [hHF]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hx
  · have hY : H.subgroupOf (CFSG.generalizedFitting W) ≠ ⊤ := by
      intro htop
      exact hK (fun f hf =>
        Subgroup.mem_subgroupOf.mp (by
          rw [htop]
          exact Subgroup.mem_top (⟨f, hf⟩ : ↥(CFSG.generalizedFitting W))))
    exact ggSporKRest_not_unmarked hyp hL hOut (hrest _ hY ⟨S, hSH⟩ hctl)

theorem ggSporKRest_exception_of_fi22 {W : Type} [Group W] [Finite W] {H E : Subgroup W}
    (hyp : GGHypThreeSixteenFlat 5 H E) (hK : ¬ CFSG.generalizedFitting W ≤ H)
    (hOut : Nat.card (Outer ↥(CFSG.generalizedFitting W)) ≤ 2)
    (he : Nonempty (↥(CFSG.generalizedFitting W) ≃* TauCeti.SporadicName.Fi22.Group))
    (hCov : SporKRestFi22Exc ↥(CFSG.generalizedFitting W)) : GGFusionException 5 H E := by
  refine Or.inr (Or.inr (Or.inr ⟨rfl, he, ?_⟩))
  intro C hC
  let F : Subgroup W := CFSG.generalizedFitting W
  obtain ⟨-, hEab, hE2, ⟨S, hSH⟩, hctl⟩ := ggSporKRest_setup hyp hOut
  have hY : H.subgroupOf F ≠ ⊤ := by
    intro htop
    apply hK
    intro f hf
    exact Subgroup.mem_subgroupOf.mp (by
      rw [htop]
      exact Subgroup.mem_top (⟨f, hf⟩ : ↥F))
  have hCF : C ≤ F := hC.1.trans inf_le_right
  have hC' : IsComponentOf (C.subgroupOf F) (H.subgroupOf F) :=
    ggSporKRestL11s_isComponentOf_subgroupOf hCF hC
  have hLie : LieModel (↥(C.subgroupOf F) ⧸ Subgroup.center ↥(C.subgroupOf F))
      .POmegaPlus 4 2 1 :=
    hCov (E.subgroupOf F) hEab (by rw [hE2]; norm_num) (H.subgroupOf F) hY ⟨S, hSH⟩ hctl
      (C.subgroupOf F) hC'
  exact ggSporKRestL11s_lieModel_centerQuot hCF hLie

end CFSG.StandardType.SporadicShape
