module

public import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S10.MovingThetaCore
import CFSG.RankThree.GroupTheory.SteinbergBMSimplePlaneFixedTwoCommutator
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.Assembly CFSG.RankThree.GroupTheory.SteinbergBY CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem moving_theta_component_quasisimplicity_reduces_to_odd_core_centralization_of
    (hB5 : SelectedPrimeElementsNormalizeThetaComponents) :
    MovingThetaComponentQuasisimplicityReducesToOddCoreCentralization := by
  intro G _ _ he p hp hp3 hvan A hAe hAcard L hL0
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hLfam, R, hRL, hR1, hR2, hAR, hRA⟩ := hL0
  have hAL : A ≤ normalizer (L : Set G) := hB5.2 G he p hp hp3 A hAe L hLfam
  obtain ⟨c, hcA, hc1, hLc⟩ := mem_thetaComponentFamily_iff.mp hLfam
  have hperf : Group.IsPerfect L := isPerfect_of_mem_thetaComponentsAt hLc
  have hLq := isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hLc
  have : IsElementaryAbelian p A := hAe
  let _ : MulDistribMulAction A L := conjActionOn hAL
  have hsmul : ∀ (a : A) (l : L), ((a • l : L) : G) = (a : G) * l * (a : G)⁻¹ := fun _ _ => rfl
  have hNθ : inSubgroup (aschbacherSolvableCore p) L ≤
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({c} : Set G)) := by
    rw [theta_eq_inf_of_mem_thetaComponentsAt hp hLc]
    exact inf_le_right
  have hcent : ∀ U : Subgroup L, U ≤ aschbacherSolvableCore p L → IsPGroup 2 U →
      (∀ a : A, ∀ x ∈ U, a • x ∈ U) → ∀ a : A, ∀ x ∈ U, a • x = x := by
    intro U hUN hU2 hUinv a x hx
    have hUθ : U.map L.subtype ≤
        inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({c} : Set G)) :=
      (Subgroup.map_mono hUN).trans hNθ
    have hUA : A ≤ normalizer ((U.map L.subtype : Subgroup G) : Set G) := by
      refine le_normalizer_of_conj_mem_forall fun a ha g hg => ?_
      obtain ⟨u, hu, rfl⟩ := hg
      exact Subgroup.mem_map.mpr ⟨(⟨a, ha⟩ : A) • u, hUinv ⟨a, ha⟩ u hu, rfl⟩
    have hbot := vanishing_centralizes_invariant_two_subgroups hp hvan hAe hAcard hcA hc1 hUθ
      (hU2.map _) hUA
    have hxc := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
      (Subgroup.mem_map_of_mem L.subtype hx)
    have h : (a : G) * (x : G) = (x : G) * (a : G) :=
      Subgroup.mem_centralizer_iff.mp hxc (a : G) a.2
    apply Subtype.ext
    rw [hsmul]
    calc (a : G) * x * (a : G)⁻¹ = x * a * (a : G)⁻¹ := by rw [h]
      _ = x := by group
  set T := R.subgroupOf L with hT
  have hRT : T.map L.subtype = R := Subgroup.map_subgroupOf_eq_of_le hRL
  have hT1 : T ≠ ⊥ := fun h => hR1 (by rw [← hRT, h, Subgroup.map_bot])
  have hT2 : IsPGroup 2 T := hR2.comap_subtype
  have hTinv : ∀ a : A, ∀ x ∈ T, a • x ∈ T := fun a x hx => by
    rw [hT, Subgroup.mem_subgroupOf] at hx ⊢
    rw [hsmul]
    exact (Subgroup.mem_normalizer_iff.mp (hAR a.2) x).mp hx
  have hTA : actionCommutator A T = T := by
    apply Subgroup.map_injective L.subtype_injective
    rw [SteinbergBM.map_actionCommutator_conj hAL T, hRT, ← hRA]
  obtain ⟨h1, h2, h3⟩ := moving_theta_odd_core_quotient hp hp2 hperf hLq hcent T hT1 hT2 hTinv hTA
  have hTop : (⊤ : Subgroup L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hOeq := oddThetaCore_eq_map (p := p) L
  have hNmap : (aschbacherSolvableCore p L).map L.subtype =
      inSubgroup (aschbacherSolvableCore p) L := rfl
  set O' := inSubgroup (pPrimeCore 2) (aschbacherSolvableCore p L) with hO'
  have hOsub : (oddThetaCore p L).subgroupOf L = O' := by
    rw [hOeq, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  refine ⟨hAL, ?_, ?_, ?_, ?_⟩
  · have h := SteinbergBM.map_actionCommutator_conj hAL (⊤ : Subgroup L)
    rw [h1, hTop] at h
    exact h.symm
  · have h := Subgroup.map_mono (f := L.subtype) h2
    rw [Subgroup.map_commutator, hTop, hNmap, ← hOeq] at h
    exact h
  · intro hn
    exact LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hOsub.symm) h3
  · constructor
    · intro hqs
      have hO'n : O'.Normal := inferInstance
      rcases LocalCores.quasisimple_normal_subgroups hqs hO'n with h | h
      · exfalso
        have hθs := (solvable_prime_complement_core_characterization (H := L) hp).1
        have hθtop : aschbacherSolvableCore p L = ⊤ :=
          eq_top_iff.mpr (h ▸ (Subgroup.map_subtype_le _ : O' ≤ aschbacherSolvableCore p L))
        have hsolv : Group.IsSolvable ↥(⊤ : Subgroup L) := by
          rw [← hθtop]
          exact hθs
        have hsolvL : Group.IsSolvable L :=
          Group.isSolvable_of_isSolvable_injective
            (f := (Subgroup.topEquiv (G := L)).symm.toMonoidHom) (MulEquiv.injective _)
        have hnt : Nontrivial L := by
          by_contra hns
          rw [not_nontrivial_iff_subsingleton] at hns
          have : Subsingleton (L ⧸ Subgroup.center L) :=
            Function.Surjective.subsingleton (QuotientGroup.mk'_surjective _)
          obtain ⟨-, -, a, b, hab⟩ := hqs
          exact hab (Subsingleton.elim _ _)
        have := hperf
        exact Group.IsPerfect.not_isSolvable L hsolvL
      · rw [hOeq, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro l hl
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨o, ho, rfl⟩
        exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp (h ho) ⟨l, hl⟩)).symm
    · intro hcomm
      have hcen : O' ≤ Subgroup.center L := by
        intro o ho
        rw [Subgroup.mem_center_iff]
        intro l
        have hl : (l : G) ∈ Subgroup.centralizer (oddThetaCore p L : Set G) :=
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) l.2
        have h := Subgroup.mem_centralizer_iff.mp hl (L.subtype o) (by
          rw [hOeq]
          exact Subgroup.mem_map_of_mem _ ho)
        exact Subtype.ext h.symm
      have hq := LocalCores.quasisimple_central_extension_derived O' hcen h3
      have htop : IsQuasisimple ↥(⊤ : Subgroup L) := by
        rw [← hperf.commutator_eq_top]
        exact hq
      exact LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv htop

end CFSG.RankThree.PartOne
