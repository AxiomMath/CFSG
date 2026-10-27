module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSCornerDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommAux
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommCornerLeaf
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommCornerLeafB

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

theorem ggSecFiveNSCornerInput_holds : GGSecFiveNSCornerInput := by
  intro G _ _ p B Bs K _ _ _ f ψ h hp b₁ hb₁ b₂ hb₂ g₁ g₂ h₁ h₂
  subst hp
  obtain ⟨z, hz⟩ := ggNSPosPF_commutator_scalar h hb₁ hb₂ h₁ h₂
  have hz1 : z = 1 := by
    by_contra hz1
    have hz0 : z ≠ 0 := ggNSPosPF3C_scalar_ne_zero h rfl hb₁ hb₂ h₁ h₂ hz
    have hz3 : z ^ 3 = 1 := ggNSPosPF3C_scalar_pow_three h rfl hb₁ hb₂ h₁ h₂ hz
    have hz6 : z ^ 6 = 1 := ggNSPosPF_commutator_pow_n_aux h hb₁ hb₂ h₁ h₂ hz
    have hdvd : 3 ∣ 2 ^ f + 1 := h.dvd
    by_cases hxeq : ψ (ggNSPosPF3C_scalarSU (n := 6) z hz3 hz6 hz0 hdvd) = 1
    · exact ggNSPosPF3C_centre_killed_contradiction h hb₁ hb₂ h₁ h₂ hz hz1 hz0
        (ggNSPosPF3C_scalarSU_coe z hz3 hz6 hz0 hdvd) hxeq
    · exact ggNSPosPF3C_retained_centre_contradiction h hb₁ hb₂ h₁ h₂ hz hz1 hz0
        (ggNSPosPF3C_scalarSU_coe z hz3 hz6 hz0 hdvd) hxeq
  have hc : ggNSPosPF_commutator g₁ g₂ = 1 := by
    refine Units.ext ?_
    rw [hz, hz1, one_smul]
    rfl
  exact (ggNSPosPF_commutator_eq_one_iff g₁ g₂).mp hc

end CFSG.StandardType

end
