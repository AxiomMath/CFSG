module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFrameIrred
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoSevenFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration

section Main


theorem ggSCWeylIrred_adjoint_E6_two_seven {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (r : ℕ) : GGSCWeylIrred 7 r (adjointGroup .E6 K) := by
  haveI : CharP K 2 := charP_two_of_card (K := K) (m := 1) (by rw [pow_one]; exact hK)
  haveI : Finite (ModGL Tag.E6 K) := finite_modGL
  haveI : Finite (adjointGroup .E6 K) := inferInstance
  obtain ⟨s, m, hs, hm, hZ⟩ := exists_order_seven_frobenius_sl3 hK
  obtain ⟨ρ, hρ, hc, hmove⟩ := exists_sl3_frame_E6 (K := K)
  refine ggSCWeylIrred_of_sylowTorus_frameGen (N := 3) Nat.prime_seven (2 : ZMod 7)
    (by decide) s m hs hm hZ (sylowTorus_adjoint_E6_two_seven hK) ρ hρ hc (fun i => ?_)
    fin_three_connected r
  obtain ⟨j, hji, g, hg⟩ := hmove i
  refine ⟨j, hji, g, 1, one_ne_zero, ?_⟩
  have h1 : (1 : ZMod 7).val = 1 := rfl
  rw [h1, pow_one]
  exact hg s

end Main

end CFSG.StandardType

end
