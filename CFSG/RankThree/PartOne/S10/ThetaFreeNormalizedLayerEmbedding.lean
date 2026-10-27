module

import CFSG.RankThree.GroupTheory.SteinbergBYThetaCentralizeNormal
import CFSG.RankThree.GroupTheory.SteinbergBYThetaInnerContainment
import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.RankThree.GroupTheory.ThetaComponents

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.GroupTheory.SteinbergBY CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace ThetaFreeEmbedding

variable {H : Type*} [Group H] [Finite H]

theorem fittingSubgroup_le_pCore {p : ℕ} (hp : p.Prime) (hθ : aschbacherSolvableCore p H = ⊥) :
    fittingSubgroup H ≤ pCore p H := by
  rw [LocalCores.fittingSubgroup_eq_iSup_pCore]
  refine iSup_le fun q => ?_
  by_cases hq : (q : ℕ) = p
  · rw [hq]
  · exact ((solvable_prime_complement_core_characterization hp).2.2.2.2.2.2 q
      (Nat.prime_of_mem_primeFactors q.2) hq).trans (hθ ▸ bot_le)

theorem exists_component_not_commuting {Y : Subgroup H} (hperf : ⁅Y, Y⁆ = Y) (hne : Y ≠ ⊥)
    (hF : ⁅Y, fittingSubgroup H⁆ = ⊥) :
    ∃ L : Subgroup H, IsComponent L ∧ ⁅Y, L⁆ ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  have hlayer : layer H ≤ Subgroup.centralizer (Y : Set H) :=
    sSup_le fun L hL => Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcon L hL))
  have hfit : fittingSubgroup H ≤ Subgroup.centralizer (Y : Set H) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hF)
  have hgen : generalizedFitting H ≤ Subgroup.centralizer (Y : Set H) := sup_le hfit hlayer
  have hY : Y ≤ generalizedFitting H := fun y hy =>
    centralizer_generalizedFitting_le H (Subgroup.le_centralizer_iff.mpr hgen hy)
  have hcomm : ⁅Y, Y⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hY.trans hgen)
  exact hne (hperf ▸ hcomm)

omit [Finite H] in
theorem inner_action_of_perfect {L Y : Subgroup H} (hL : IsQuasisimple L)
    (hout : Group.IsSolvable (ComponentClassification.OuterAutomorphisms.Outer
      (L ⧸ Subgroup.center L)))
    (hYL : Y ≤ Subgroup.normalizer (L : Set H)) (hperf : ⁅Y, Y⁆ = Y) :
    ∀ y ∈ Y, ∃ l ∈ L, ∀ z ∈ L, y * z * y⁻¹ = l * z * l⁻¹ := by
  have : Group.IsPerfect L := hL.1
  have : Group.IsPerfect Y := Subgroup.isPerfect_iff.mpr hperf
  have := hout
  intro y hy
  let ρ : Y →* MulAut (L ⧸ Subgroup.center L) :=
    (ComponentClassification.PerfectAutomorphisms.centerQuotientHom L).comp
      (L.normalizerMonoidHom.comp (Subgroup.inclusion hYL))
  obtain ⟨s, hs⟩ := ComponentClassification.OuterAutomorphisms.perfect_action_inner ρ ⟨y, hy⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective s
  have hconj : L.normalizerMonoidHom (Subgroup.inclusion hYL ⟨y, hy⟩) = MulAut.conj l :=
    ComponentClassification.CentralCover.perfect_central_quotient_automorphism_faithful L
      (hs.trans (ComponentClassification.OuterAutomorphisms.centerQuotient_conj l).symm)
  refine ⟨l, l.2, fun z hz => ?_⟩
  have h := congrArg (fun φ : MulAut L => ((φ ⟨z, hz⟩ : L) : H)) hconj
  simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using h

theorem ne_bot_of_mem_thetaComponents {K : Type*} [Group K] [Finite K] {p : ℕ} {Y : Subgroup K}
    (hY : Y ∈ thetaComponents p K) : Y ≠ ⊥ := by
  rintro rfl
  obtain ⟨-, -, a, b, hab⟩ := hY.2.2
  have : Subsingleton (↥(⊥ : Subgroup K)) := inferInstance
  have hs : Subsingleton (↥(⊥ : Subgroup K) ⧸ aschbacherSolvableCore p ↥(⊥ : Subgroup K)) :=
    Function.Surjective.subsingleton (QuotientGroup.mk'_surjective _)
  have hs' : Subsingleton ((↥(⊥ : Subgroup K) ⧸ aschbacherSolvableCore p ↥(⊥ : Subgroup K)) ⧸
      Subgroup.center (↥(⊥ : Subgroup K) ⧸ aschbacherSolvableCore p ↥(⊥ : Subgroup K))) :=
    Function.Surjective.subsingleton (QuotientGroup.mk'_surjective _)
  exact hab (Subsingleton.elim _ _)

end ThetaFreeEmbedding

theorem theta_free_normalized_layer_local_component_embedding :
    SchreierFor InCatalog →
    ∀ (H : Type) [Group H] [Finite H], CFSG.IsKGroup H → ∀ p : ℕ, p.Prime →
      aschbacherSolvableCore p H = ⊥ → ∀ x : H, (∃ k : ℕ, orderOf x = p ^ k) →
      ∀ Y ∈ thetaComponentsAt p x,
      (∀ L : Subgroup H, IsComponent L → x ∈ Subgroup.normalizer (L : Set H)) →
      (∀ L : Subgroup H, IsComponent L → Y ≤ Subgroup.normalizer (L : Set H)) →
      ∃ L : Subgroup H, IsComponent L ∧ Y ≤ L := by
  intro hS H _ _ hK p hp hθ x hx Y hY hxn hYn
  obtain ⟨Y₀, hY₀, rfl⟩ := hY
  set Yh : Subgroup H := Y₀.map (Subgroup.centralizer ({x} : Set H)).subtype with hYh
  have hperf : ⁅Yh, Yh⁆ = Yh := by
    rw [hYh, ← Subgroup.map_commutator]
    exact congrArg _ (Subgroup.isPerfect_iff.mp hY₀.1)
  have hne : Yh ≠ ⊥ := fun h => ThetaFreeEmbedding.ne_bot_of_mem_thetaComponents hY₀
    ((Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h)
  have hF : ⁅Yh, fittingSubgroup H⁆ = ⊥ := by
    have h := (local_theta_components_centralize_normal_defining_prime_subgroups hp hx hY₀
      pCore_normal pCore_isPGroup).2
    exact eq_bot_iff.mpr (h ▸ Subgroup.commutator_mono le_rfl
      (ThetaFreeEmbedding.fittingSubgroup_le_pCore hp hθ))
  obtain ⟨L, hL, hnt⟩ := ThetaFreeEmbedding.exists_component_not_commuting hperf hne hF
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.1.2.1
  have hout : Group.IsSolvable (ComponentClassification.OuterAutomorphisms.Outer
      (L ⧸ Subgroup.center L)) :=
    hS (L ⧸ Subgroup.center L) hL.1.2.2 (hK L (Subgroup.center L) inferInstance)
  exact ⟨L, hL, local_theta_component_nontrivial_inner_action_containment hp hY₀ hL (hxn L hL)
    (hYn L hL) (ThetaFreeEmbedding.inner_action_of_perfect hL.1 hout (hYn L hL) hperf) hnt⟩

end CFSG.RankThree.PartOne
