module

public import CFSG.LocalAnalysis.StandardType.GGFusionExceptionFull
public import CFSG.LocalAnalysis.StandardType.GGFusionShadowComponents
import CFSG.Assembly.GL83StatedBridge
import CFSG.CharacterTheory.Burnside
import CFSG.GH74.GLS.Stage4.Q9.Rigidity
import CFSG.GroupTheory.OrderBelowSixtySolvable
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.LocalAnalysis.StandardType.GGHypThreeSixteenFlatMarking
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatRootCent
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummand
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerBasic
public import CFSG.LieType.ChevTwo.Layered
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExc

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

noncomputable abbrev ggRCSTt {X : Type} [Group X] (V E K : Subgroup X)
    [((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal] :
    Subgroup (↥(E ⊔ K) ⧸ (ggRCSU V E K).subgroupOf (E ⊔ K)) :=
  ((E ⊔ (K ⊓ V)).subgroupOf (E ⊔ K)).map
    (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)))

noncomputable abbrev ggRCSHK {X : Type} [Group X] (V E K : Subgroup X)
    [((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal] :
    Subgroup (↥(E ⊔ K) ⧸ (ggRCSU V E K).subgroupOf (E ⊔ K)) :=
  ggRCSTt V E K ⊓ CFSG.generalizedFitting (↥(E ⊔ K) ⧸ (ggRCSU V E K).subgroupOf (E ⊔ K))

section Generic

variable {A B : Type} [Group A] [Group B]

theorem nontrivial_of_open_isQuasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) : Nontrivial Q := by
  haveI := hQ.2
  exact (QuotientGroup.mk'_surjective (Subgroup.center Q)).nontrivial

theorem ggRCS_commutator_subgroupOf_normal (H : Subgroup A) :
    (⁅H, H⁆.subgroupOf H).Normal := by
  have h : ⁅H, H⁆.subgroupOf H = commutator ↥H := by
    rw [← Subgroup.map_subtype_commutator H]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [h]
  exact Subgroup.commutator_normal ⊤ ⊤

theorem ggRCS_central_lift [Finite A] (φ : A →* B) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center A) {C : Subgroup B} (hC : CFSG.Open.IsComponentOf C ⊤) :
    CFSG.Open.IsComponentOf ⁅C.comap φ, C.comap φ⁆ ⊤ ∧
      (⁅C.comap φ, C.comap φ⁆).map φ = C ∧
      Nonempty (↥(⁅C.comap φ, C.comap φ⁆) ⧸
          Subgroup.center ↥⁅C.comap φ, C.comap φ⁆ ≃*
        ↥C ⧸ Subgroup.center ↥C) := by
  set M := C.comap φ with hM
  set N := ⁅M, M⁆ with hN
  have hCperf : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.mp ⟨hC.2.2.1⟩
  have hmapN : N.map φ = C :=
    CFSG.ClassicalInvolution.RouteD.Exotic.map_commutator_comap_eq φ hφ hCperf
  have hNq : CFSG.Open.IsQuasisimple ↥N :=
    CFSG.ClassicalInvolution.RouteD.Exotic.isQuasisimple_commutator_comap φ hφ hker hC.2.2
  have hNM : N ≤ M := Subgroup.commutator_le_self M
  have hMsub : CFSG.Open.IsSubnormal M ⊤ := hC.2.1.comap φ
  have hstep : CFSG.Open.IsSubnormal N M :=
    CFSG.Open.IsSubnormal.step hNM (ggRCS_commutator_subgroupOf_normal M)
      (CFSG.Open.IsSubnormal.refl M)
  have hNsub : CFSG.Open.IsSubnormal N ⊤ := hstep.trans hMsub
  refine ⟨⟨le_top, hNsub, hNq⟩, hmapN, ?_⟩
  let π : ↥N →* ↥C := (φ.comp N.subtype).codRestrict C fun x =>
    Subgroup.mem_comap.mp (hNM x.2)
  have hπsurj : Function.Surjective π := by
    rintro ⟨c, hc⟩
    have hc' : c ∈ N.map φ := by rw [hmapN]; exact hc
    obtain ⟨n, hn, hnc⟩ := hc'
    exact ⟨⟨n, hn⟩, Subtype.ext hnc⟩
  have hπker : π.ker ≤ Subgroup.center ↥N := by
    intro x hx
    have hx1 : φ (x : A) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxA : (x : A) ∈ Subgroup.center A := hker (MonoidHom.mem_ker.mpr hx1)
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxA (y : A))
  haveI : Group.IsPerfect ↥N := ⟨hNq.1⟩
  exact CFSG.LieType.ChevTwo.nonempty_quotCenter_equiv_of_surjective π hπsurj hπker

theorem ggRCS_isQuasisimple_map_of_solvable_ker (φ : A →* B) (hφ : Function.Surjective φ)
    (hsol : Group.IsSolvable ↥φ.ker) {C : Subgroup A}
    (hC : CFSG.Open.IsQuasisimple ↥C) : CFSG.Open.IsQuasisimple ↥(C.map φ) := by
  have hKf : ¬ C ≤ φ.ker := by
    intro hle
    have hCsolv : Group.IsSolvable ↥C :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    haveI : Nontrivial ↥C := nontrivial_of_open_isQuasisimple hC
    haveI : Group.IsPerfect ↥C := ⟨hC.1⟩
    exact Group.IsPerfect.not_isSolvable ↥C hCsolv
  have hnatC : CFSG.IsQuasisimple ↥C :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mpr hC)
  have hnat : CFSG.IsQuasisimple ↥(C.map φ) := CFSG.LocalCores.isQuasisimple_map hnatC φ hKf
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hnat)

theorem ggRCS_component_map_solvable_ker [Finite A] (φ : A →* B)
    (hφ : Function.Surjective φ) (hsol : Group.IsSolvable ↥φ.ker) {C : Subgroup A}
    (hC : CFSG.Open.IsComponentOf C ⊤) :
    CFSG.Open.IsComponentOf (C.map φ) ⊤ ∧
      Nonempty (↥(C.map φ) ⧸ Subgroup.center ↥(C.map φ) ≃*
        ↥C ⧸ Subgroup.center ↥C) := by
  have hCq : CFSG.Open.IsComponentOf (C.map φ) ⊤ :=
    ⟨le_top, by
      have h := hC.2.1.map φ
      rwa [Subgroup.map_top_of_surjective φ hφ] at h,
      ggRCS_isQuasisimple_map_of_solvable_ker φ hφ hsol hC.2.2⟩
  have hψsurj : Function.Surjective (φ.subgroupMap C) := φ.subgroupMap_surjective C
  have hnorm : ((φ.ker).subgroupOf C).Normal :=
    Subgroup.Normal.subgroupOf (MonoidHom.normal_ker φ) C
  have hKf : ¬ C ≤ φ.ker := by
    intro hle
    have hCsolv : Group.IsSolvable ↥C :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    haveI : Nontrivial ↥C := nontrivial_of_open_isQuasisimple hC.2.2
    haveI : Group.IsPerfect ↥C := ⟨hC.2.2.1⟩
    exact Group.IsPerfect.not_isSolvable ↥C hCsolv
  have hψker : (φ.subgroupMap C).ker ≤ Subgroup.center ↥C := by
    intro x hx
    have hx1 : φ (x : A) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxK : (x : C) ∈ (φ.ker).subgroupOf C := by
      rw [Subgroup.mem_subgroupOf]
      exact MonoidHom.mem_ker.mpr hx1
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups_assembly hC.2.2
      hnorm with htop | hcent
    · exfalso
      apply hKf
      intro y hy
      have hy' : (⟨y, hy⟩ : ↥C) ∈ (φ.ker).subgroupOf C := by
        rw [htop]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hy'
    · exact hcent hxK
  haveI : Group.IsPerfect ↥C := ⟨hC.2.2.1⟩
  refine ⟨hCq, ?_⟩
  obtain ⟨e⟩ := CFSG.LieType.ChevTwo.nonempty_quotCenter_equiv_of_surjective (φ.subgroupMap C)
    hψsurj hψker
  exact ⟨e.symm⟩

theorem ggRCS_map_injOn_components_of_solvable_ker [Finite A] (φ : A →* B)
    (hφ : Function.Surjective φ) (hsol : Group.IsSolvable ↥φ.ker) :
    Set.InjOn (fun C : Subgroup A => C.map φ) {C | CFSG.Open.IsComponentOf C ⊤} := by
  intro C₁ hC₁ C₂ hC₂ heq
  have heq' : C₁.map φ = C₂.map φ := heq
  by_contra hne
  have hC₁' : CFSG.IsComponent C₁ := (CFSG.isComponent_iff_open C₁).mpr hC₁
  have hC₂' : CFSG.IsComponent C₂ := (CFSG.isComponent_iff_open C₂).mpr hC₂
  rcases CFSG.LocalCores.distinct_components_commute hC₁' hC₂' with hEq | hcomm
  · exact hne hEq
  · have hle : C₁.map φ ≤ Subgroup.centralizer (C₂.map φ : Set B) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, ← Subgroup.map_commutator, hcomm,
        Subgroup.map_bot]
    have hle' : C₂.map φ ≤ Subgroup.centralizer (C₂.map φ : Set B) := heq' ▸ hle
    have hab : ⁅C₁.map φ, C₁.map φ⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, heq']
      exact hle'
    have hq := (ggRCS_component_map_solvable_ker φ hφ hsol hC₁).1
    have hperf : ⁅C₁.map φ, C₁.map φ⁆ = C₁.map φ := Subgroup.isPerfect_iff.mp ⟨hq.2.2.1⟩
    have hDne : C₁.map φ ≠ ⊥ := by
      intro hbot
      haveI : Nontrivial ↥(C₁.map φ) := nontrivial_of_open_isQuasisimple hq.2.2
      have hsub : Subsingleton ↥(C₁.map φ) := by rw [hbot]; infer_instance
      obtain ⟨a, b, hab⟩ := ‹Nontrivial ↥(C₁.map φ)›.exists_pair_ne
      exact hab (hsub.elim a b)
    rw [hab] at hperf
    exact hDne hperf.symm

end Generic

end CFSG.StandardType
