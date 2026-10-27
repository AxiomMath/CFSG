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
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.LieType.Universal.SpinOmega.Center
public import CFSG.Timmesfeld.Orders.ClassicalOmega
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Assembly.Subnormal
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Families
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

theorem ggRCS_perfect_le_generalizedFitting {X : Type} [Group X] [Finite X] {V E K : Subgroup X}
    (hK : CFSG.IsComponent K) (hEK : E ≤ Subgroup.normalizer (K : Set X))
    (hE : ∀ a ∈ E, ∀ b ∈ E, Commute a b)
    [((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal] :
    ∀ P : Subgroup (↥(E ⊔ K) ⧸ (ggRCSU V E K).subgroupOf (E ⊔ K)),
      ⁅P, P⁆ = P → P ≤ CFSG.generalizedFitting
        (↥(E ⊔ K) ⧸ (ggRCSU V E K).subgroupOf (E ⊔ K)) := by
  intro P hP
  set W₀ := E ⊔ K with hW₀
  set U := ggRCSU V E K with hU
  haveI hUinst : (U.subgroupOf W₀).Normal := inferInstance
  set π : ↥W₀ →* ↥W₀ ⧸ U.subgroupOf W₀ := QuotientGroup.mk' (U.subgroupOf W₀) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπ1 : ∀ w : ↥W₀, π w = 1 ↔ (w : X) ∈ U := fun w => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hKW : K ≤ W₀ := le_sup_right
  have hKn : (K.subgroupOf W₀).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKW]
    intro h k hh hk
    have hkN : k ∈ Subgroup.normalizer (K : Set X) := (sup_le hEK Subgroup.le_normalizer) hk
    exact (Subgroup.mem_normalizer_iff.mp hkN h).mp hh
  haveI hKnInst : (K.subgroupOf W₀).Normal := hKn
  have hKnat : CFSG.IsQuasisimple ↥K := hK.1
  have hKA : CFSG.Assembly.IsQuasisimple ↥K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hKnat
  have hKcW : IsComponentOf K W₀ := ⟨hKW, ggIsSubnormal_of_normal hKW hKn, hKA⟩
  set Kbar : Subgroup (↥W₀ ⧸ U.subgroupOf W₀) := (K.subgroupOf W₀).map π with hKbar
  haveI hKbarN : Kbar.Normal := hKn.map π hπs
  have hUC : U ≤ Subgroup.centralizer (K : Set X) := inf_le_right
  have hKnotker : ¬ K.subgroupOf W₀ ≤ π.ker := by
    intro hle
    refine ggComponent_not_commute hKcW fun a ha c hc => ?_
    have haU : a ∈ U := (hπ1 ⟨a, hKW ha⟩).mp (hle (Subgroup.mem_subgroupOf.mpr ha))
    exact (Subgroup.mem_centralizer_iff.mp (hUC haU) c hc).symm
  have hKcomp : CFSG.IsComponent (K.subgroupOf W₀) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hKW).mp hKcW
  have hKbarC : CFSG.IsComponent Kbar :=
    ⟨CFSG.LocalCores.isQuasisimple_map hKcomp.1 π hKnotker, (hKn.map π hπs).isSubnormal⟩
  have hKbarF : Kbar ≤ CFSG.generalizedFitting (↥W₀ ⧸ U.subgroupOf W₀) := by
    have h1 : Kbar ≤ CFSG.layer (↥W₀ ⧸ U.subgroupOf W₀) :=
      CFSG.LocalCores.component_le_layer hKbarC
    have h2 : CFSG.layer (↥W₀ ⧸ U.subgroupOf W₀) ≤
        CFSG.generalizedFitting (↥W₀ ⧸ U.subgroupOf W₀) := le_sup_right
    exact h1.trans h2
  haveI hEsolv : Group.IsSolvable ↥E :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (hE a.1 a.2 b.1 b.2).eq
  let φ : ↥E →* (↥W₀ ⧸ U.subgroupOf W₀) ⧸ Kbar :=
    (QuotientGroup.mk' Kbar).comp (π.comp (Subgroup.inclusion (le_sup_left : E ≤ W₀)))
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective Kbar y
    obtain ⟨w, rfl⟩ := hπs z
    have hw : w ∈ (E.subgroupOf W₀) ⊔ (K.subgroupOf W₀) := by
      have htop : (E.subgroupOf W₀) ⊔ (K.subgroupOf W₀) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup (le_sup_left : E ≤ W₀) (le_sup_right : K ≤ W₀)]
        exact Subgroup.subgroupOf_self W₀
      rw [htop]
      exact Subgroup.mem_top w
    obtain ⟨e, he, k, hk, hw_eq⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := E.subgroupOf W₀) (t := K.subgroupOf W₀)).mp hw
    refine ⟨⟨(e : X), Subgroup.mem_subgroupOf.mp he⟩, ?_⟩
    have hkbar : π k ∈ Kbar := Subgroup.mem_map_of_mem π hk
    have hkbar1 : (QuotientGroup.mk' Kbar) (π k) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hkbar
    have hπw : π w = π e * π k := by rw [← hw_eq, map_mul]
    have hφe : φ ⟨(e : X), Subgroup.mem_subgroupOf.mp he⟩ =
        (QuotientGroup.mk' Kbar) (π e) := by
      show (QuotientGroup.mk' Kbar) (π (Subgroup.inclusion (le_sup_left : E ≤ W₀) _)) =
        (QuotientGroup.mk' Kbar) (π e)
      rw [show Subgroup.inclusion (le_sup_left : E ≤ W₀)
          ⟨(e : X), Subgroup.mem_subgroupOf.mp he⟩ = e from Subtype.ext rfl]
    rw [hφe, hπw, map_mul, hkbar1, mul_one]
  haveI hsolv : Group.IsSolvable ((↥W₀ ⧸ U.subgroupOf W₀) ⧸ Kbar) :=
    Group.isSolvable_of_surjective hφsurj
  have hPK : P ≤ Kbar := by
    intro x hx
    have hφx : (QuotientGroup.mk' Kbar) x = 1 := by
      let ψ : ↥P →* (↥W₀ ⧸ U.subgroupOf W₀) ⧸ Kbar :=
        (QuotientGroup.mk' Kbar).comp P.subtype
      haveI hPperf : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
      haveI hperf'' : Group.IsPerfect ↥ψ.range :=
        Group.IsPerfect.ofSurjective ψ.rangeRestrict_surjective
      haveI hrangeSolv : Group.IsSolvable ↥ψ.range :=
        Group.isSolvable_of_isSolvable_injective (f := ψ.range.subtype)
          (Subgroup.subtype_injective ψ.range)
      have hss : Subsingleton ↥ψ.range := by
        by_contra h
        rw [not_subsingleton_iff_nontrivial] at h
        exact Group.IsPerfect.not_isSolvable (G := ↥ψ.range) inferInstance
      have h1 : (⟨ψ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ : ↥ψ.range) = 1 := Subsingleton.elim _ _
      exact congrArg Subtype.val h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hφx
    exact hφx
  exact hPK.trans hKbarF

end CFSG.StandardType
