module

public import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
import CFSG.RankThree.PartOne.S10.HyperplaneObstructionSupplement
import CFSG.RankThree.PartOne.S10.HyperplaneObstructionPerfectSupplement
import CFSG.RankThree.PartOne.S10.HyperplaneObstructionTwoLocal
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.GroupTheory.SteinbergBMFaithfulPlaneTwoGroupWitness
import CFSG.RankThree.GroupTheory.SteinbergBMSimplePlaneFixedTwoCommutator

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY
  CFSG.RankThree.PartOne.HyperplaneObstruction
open scoped commutatorElement

theorem section_ten_hyperplane_local_residual_obstruction :
    SectionTenHyperplaneLocalResidualObstruction := by
  intro G _ _ p A hS L hL B hBA hBcard hLB
  by_contra hcon
  push Not at hcon
  have hp := sectionTenSetup_prime hS
  have hp3 := sectionTenSetup_three_lt hS
  have hp2 : p ≠ 2 := by omega
  have hvan := sectionTenSetup_vanishing hS
  have he : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq hS).le
  obtain ⟨-, -, -, hG, -, -, hAe, hAcard, ⟨Q₀, hQ₀1, hQ₀2, hAQ₀⟩, -⟩ := id hS
  have hBe : IsElementaryAbelian p B := SteinbergBM.isElementaryAbelian_of_le hAe hBA
  have hAL : A ≤ normalizer (L : Set G) :=
    selected_prime_elements_normalize_theta_components.2 G he p hp hp3 A hAe L hL
  have hBL : B ≤ normalizer (L : Set G) := hBA.trans hAL
  obtain ⟨a₀, -, -, hLa₀⟩ := mem_thetaComponentFamily_iff.mp hL
  have hLq := isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hLa₀
  obtain ⟨-, hres⟩ := hyperplane_fixed_residual_common_theta_supplement hp
    (IsElementaryAbelian.isPGroup p B) hBe.toIsMulCommutative hBL hLq hLB
  obtain ⟨⟨-, hS2, hAS⟩, -, b, hbB, hb1, hRne, hR2, hBR, -⟩ :=
    SteinbergBM.characteristic_two_type_faithful_plane_two_group_witness hG hp hp2 hAe hQ₀2 hQ₀1
      hAQ₀ hBA hBcard
  have hBb : ∀ c ∈ B, c * b = b * c := fun c hc =>
    congrArg Subtype.val (hBe.is_comm.comm ⟨c, hc⟩ ⟨b, hbB⟩)
  have hBW := SteinbergBM.le_normalizer_inf_centralizer (hBA.trans hAS) hBb
  obtain ⟨-, hP₀X, hXsup, hBX, hXB⟩ := hres b hbB
  obtain ⟨K, hK, hK1, hKX, hKR, hKB, hXK⟩ :=
    exists_perfect_supplement_centralizing_commutator he hp hp3 hvan hAe hAcard hBA hBcard hbB hb1
      (hcon b hbB hb1) hBX hXB (hS2.to_le inf_le_left) inf_le_right hBW
  have hsup : ∀ d ∈ B, d ≠ 1 → K ≤ inSubgroup perfectResidual (thetaSupplementAt p L d) ∧
      inSubgroup perfectResidual (thetaSupplementAt p L d) =
        inSubgroup (aschbacherSolvableCore p)
          (inSubgroup perfectResidual (thetaSupplementAt p L d)) ⊔ K := by
    intro d hd hd1
    obtain ⟨-, hP₀Ld, hLdsup, -, -⟩ := hres d hd
    exact residual_supplement_of_perfect_cover hp (hcon d hd hd1) hXsup hLdsup
      (hP₀X.trans inf_le_right) (hP₀Ld.trans inf_le_right) hK hKX
      (hKB.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hd))) hXK
  refine false_of_perfect_cover_at_plane hG hp hp2 hvan hAe hAcard hBA hBcard hR2 hRne hBR hK hK1
    hKR hKB (Ld := fun d => inSubgroup perfectResidual (thetaSupplementAt p L d)) hcon
    (fun d hd hd1 => (hsup d hd hd1).1) fun d hd hd1 => ?_
  have hθ : inSubgroup (aschbacherSolvableCore p)
      (inSubgroup perfectResidual (thetaSupplementAt p L d)) ≤
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({d} : Set G)) :=
    (theta_eq_inf_of_mem_thetaComponentsAt hp (hcon d hd hd1)).le.trans inf_le_right
  exact (hsup d hd hd1).2.le.trans (sup_le (hθ.trans le_sup_right) le_sup_left)

end CFSG.RankThree.PartOne
