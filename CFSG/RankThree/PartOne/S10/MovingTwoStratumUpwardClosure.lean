module

public import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.Assembly CFSG.RankThree.GroupTheory.SteinbergBY
open scoped commutatorElement

theorem section_ten_moving_two_stratum_upward_closure_of
    (hB5 : SelectedPrimeElementsNormalizeThetaComponents) :
    SectionTenMovingTwoStratumUpwardClosure := by
  intro G _ _ he p hp hp3 hvan A hAe hAcard L hL K hK hLK hL0
  have hp2 : p ≠ 2 := by omega
  have hAL : A ≤ normalizer (L : Set G) := hB5.2 G he p hp hp3 A hAe L hL
  have hAK : A ≤ normalizer (K : Set G) := hB5.2 G he p hp hp3 A hAe K hK
  obtain ⟨-, R, hRL, hR1, hR2, hAR, hRA⟩ := hL0
  obtain ⟨c, hcA, hc1, hLc⟩ := mem_thetaComponentFamily_iff.mp hL
  obtain ⟨hNL, hNn⟩ := theta_le_and_normal p L
  have hAN := le_normalizer_theta_of_le_normalizer hp hAL
  have hNθ : inSubgroup (aschbacherSolvableCore p) L ≤
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({c} : Set G)) := by
    rw [theta_eq_inf_of_mem_thetaComponentsAt hp hLc]
    exact inf_le_right
  have hRN : ⁅R ⊓ inSubgroup (aschbacherSolvableCore p) L, A⁆ = ⊥ :=
    vanishing_centralizes_invariant_two_subgroups hp hvan hAe hAcard hcA hc1
      (inf_le_right.trans hNθ) (hR2.to_le inf_le_left)
      (le_normalizer_inf_of_le_normalizer hAR hAN)
  obtain ⟨T, hTM, hT1, hT2, hAT, hTA⟩ := ambient_two_commutator_lift hp hp2
    (IsElementaryAbelian.isPGroup p A) hAL hNL hNn hAN (theta_solvable_and_not_dvd hp L).2
    (M := L ⊓ K) inf_le_left (le_normalizer_inf_of_le_normalizer hAL hAK) hLK hRL hR1 hR2 hAR
    hRA.symm hRN
  exact ⟨hK, T, hTM.trans inf_le_right, hT1, hT2, hAT, hTA.symm⟩

end CFSG.RankThree.PartOne
