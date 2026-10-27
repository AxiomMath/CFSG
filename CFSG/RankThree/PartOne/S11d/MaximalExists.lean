module

public import CFSG.RankThree.PartOne.S11d.Sec109Common
public import CFSG.RankThree.PartOne.S11d.Facts
public import CFSG.RankThree.PartOne.S11d.LiftC
import CFSG.RankThree.PartOne.S10.ThetaNodesUnconditional
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
import CFSG.RankThree.PartOne.S12.Sec125Moved

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.ComponentClassification CFSG.RankThree
  CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace Sec109

theorem maximalExists_of (hS : SchreierFor InCatalog) (hbranch : MaximalBranchThree) :
    MaximalExists := by
  intro G _ _ p A c L B n h b S K hW hK hSK
  have hsetup := h.setup
  have : IsSimpleGroup G := hsetup.1
  have hp : p.Prime := h.prime
  have hp3 : 3 < p := sectionTenSetup_three_lt hsetup
  have hev : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq hsetup).le
  have hAe := h.A_elem
  have hbB : b ∈ B := hW.b_mem
  have hbA : b ∈ A := h.B_le_A hbB
  have hb1 : b ≠ 1 := hW.b_ne_one
  have hKF : K ∈ thetaComponentFamily p A := hK.1.1
  by_cases hstar : K ∈ sectionTenStar p A
  · exact ⟨b, S, K, hW, ⟨⟨hK.1, hstar⟩, hK.2⟩, hSK⟩
  · have htr : ∀ J ∈ thetaComponentFamily p A, ∀ K₁ ∈ thetaComponentFamily p A,
        ∀ K₂ ∈ thetaComponentFamily p A, sectionTenRel p J K₁ → sectionTenRel p K₁ K₂ →
        sectionTenRel p J K₂ := fun J hJ K₁ hK₁ K₂ hK₂ =>
      section_ten_component_supplement_transitivity hS G hsetup.2.1 hsetup.2.2.1 hev p hp hp3 A
        hAe J hJ K₁ hK₁ K₂ hK₂
    obtain ⟨K', hK'F, hKK', hmax⟩ := Sec125.exists_maximal_above (sectionTenRel p)
      (thetaComponentFamily p A) (fun a _ => sectionTenRel_refl p a) htr hKF
    have hK'0 : K' ∈ sectionTenZero p A :=
      section_ten_moving_two_stratum_upward_closure G hev p hp hp3
        (sectionTenSetup_vanishing hsetup) A hAe h.A_card K hKF K' hK'F hKK' hK.1
    have hK'zs : K' ∈ sectionTenZeroStar p A := ⟨hK'0, hK'F, hmax⟩
    obtain ⟨a', ha'A, ha'1, hK'a⟩ := mem_thetaComponentFamily_iff.mp hK'F
    have hK'at : K' ∈ sectionTenAt p (sectionTenZeroStar p A) a' := ⟨hK'zs, hK'a⟩
    by_cases ha'B : a' ∈ B
    ·
      have h81 := selected_prime_elements_normalize_theta_components
      have hAK : A ≤ normalizer (K : Set G) := h81.2 G hev p hp hp3 A hAe K hKF
      have hAK' : A ≤ normalizer (K' : Set G) := h81.2 G hev p hp hp3 A hAe K' hK'F
      obtain ⟨hθK, hθn⟩ := theta_le_and_normal p K
      have hAθ : A ≤ normalizer ((inSubgroup (aschbacherSolvableCore p) K : Subgroup G) : Set G) :=
        le_normalizer_theta_of_le_normalizer hp hAK
      have hθp := (theta_solvable_and_not_dvd hp K).2
      have hAC : A ≤ centralizer ({b} : Set G) := fun x hx =>
        mem_centralizer_singleton_iff.mpr (h.A_comm x hx b hbA)
      have hθeq := theta_eq_inf_of_mem_thetaComponentsAt hp hK.2
      have hRN : ⁅S ⊓ inSubgroup (aschbacherSolvableCore p) K, A⁆ = ⊥ := by
        have hU : S ⊓ inSubgroup (aschbacherSolvableCore p) K ≤
            inSubgroup (aschbacherSolvableCore p) (centralizer ({b} : Set G)) := by
          rw [hθeq]
          exact inf_le_right.trans inf_le_right
        exact vanishing_centralizes_invariant_two_subgroups hp (sectionTenSetup_vanishing hsetup)
          hAe h.A_card hbA hb1 hU (hW.S_two.to_le inf_le_left)
          (le_normalizer_inf_of_le_normalizer hW.S_norm hAθ)
      obtain ⟨T, hTM, hT1, hT2, hAT, hTc⟩ := S11d.ambient_two_commutator_lift_c hp
        (by omega) (IsElementaryAbelian.isPGroup p A) h.A_comm h.c_mem hAK hθK hθn hAθ hθp
        (inf_le_left : K ⊓ K' ≤ K) (le_normalizer_inf_of_le_normalizer hAK hAK') (hKK')
        hSK hW.S_ne_bot hW.S_two hW.S_norm hW.S_comm.symm hRN
      have hTK' : T ≤ K' := hTM.trans inf_le_right
      have hK'C : K' ≤ centralizer ({a'} : Set G) := (mem_thetaComponentsAt_iff.mp hK'a).1
      exact ⟨a', T, K', ⟨ha'B, ha'1, hTK'.trans hK'C, hT1, hT2, hAT, hTc.symm⟩, hK'at, hTK'⟩
    · exact (hbranch G p A c L B n h b S K K' a' hW hK hSK hK'at ha'A ha'B hKK').elim

end Sec109

end CFSG.RankThree.PartOne
