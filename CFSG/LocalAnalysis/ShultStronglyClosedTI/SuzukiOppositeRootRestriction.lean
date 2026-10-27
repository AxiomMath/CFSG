module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiLayerKernel

public section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Blueprint CFSG.LieType.Ree CFSG.LocalAnalysis.ComponentInitial
open SuzukiModel SuzukiLayerKernel
open scoped commutatorElement

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem suzuki_opposite_pair_inner_root_restriction_rigidity
    (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : MulAut (suzukiGroup a K))
    (hβU : (suzukiU a K).map β.toMonoidHom = suzukiU a K)
    (hβV : ((suzukiU a K).map (MulAut.conj (suzukiWElt a K)).toMonoidHom).map β.toMonoidHom =
      (suzukiU a K).map (MulAut.conj (suzukiWElt a K)).toMonoidHom)
    (hβt : ∃ t ∈ suzukiU a K, ∀ x ∈ suzukiU a K, β x = t * x * t⁻¹) : β = 1 := by
  obtain ⟨t, ht, hβt⟩ := hβt
  have hcent := (suzuki_unipotent_structure hK).2.2.2.2.2.1
  obtain ⟨s, hs, hβs⟩ := suzuki_rank_one_Sylow_layer_kernel ha hK
    ((suzukiU_isPGroup_index hK).1.toSylow (suzukiU_isPGroup_index hK).2) (suzukiZ0 a K)
    (map_omega₁_suzukiU hK).symm β hβU
    (fun v hv => by rw [hβt v (suzukiZ0_le_suzukiU hv), ← hcent v hv t ht, mul_inv_cancel_right])
    (fun x hx => by
      rw [hβt x hx]
      convert commutatorElement_mem_suzukiZ0 hK (inv_mem hx) ht using 1
      rw [commutatorElement_def, inv_inv]
      group)
  obtain ⟨P, hPU, -, -, ⟨φ, hφ, -, hφ0, -, -⟩, -, -⟩ := Suzuki_model_opposite_root_interface ha hK
  have hso : s • (⟨suzukiLine a K 0 0, suzukiLine_mem_suzukiOmega a K 0 0⟩ : suzukiOmegaSub hK) =
      ⟨suzukiLine a K 0 0, suzukiLine_mem_suzukiOmega a K 0 0⟩ := by
    apply φ.injective
    rw [hφ, hφ0]
    refine Sylow.ext ?_
    rw [coe_smul_sylow', coe_smul_sylow', hPU, ← hβs]
    exact hβV
  have hso' : s • suzukiLine a K 0 0 = suzukiLine a K 0 0 := by
    have h := congrArg Subtype.val hso
    rwa [SubMulAction.val_smul] at h
  obtain ⟨c, d, rfl⟩ := (mem_suzukiU_iff hK).1 hs
  rw [suzukiSElt_smul_suzukiLine_zero hK, suzukiLine_eq_iff] at hso'
  obtain ⟨rfl, rfl⟩ := hso'
  rw [hβs, suzukiSElt_zero_zero hK, map_one]

end CFSG.ShultStronglyClosedTI
