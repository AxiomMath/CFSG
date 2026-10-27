module

public import CFSG.LocalAnalysis.StandardType.FS81.S7E7Incl
import CFSG.LocalAnalysis.SeitzReduction.EPilotHeisIrr

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction CFSG.QuasithinUnique

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis CFSG.SeitzReduction.EPilot.HeisIrr

section E7Model


theorem commutator_highRadical_le_zpowers {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    ∀ x ∈ EPilot.highRadical τ K, ∀ y ∈ EPilot.highRadical τ K,
      x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers (EPilot.pinnedElt τ (highRoot τ) (1 : K)) := by
  have hnode : iθ τ = highNode τ := by rcases hτ with rfl | rfl <;> rfl
  intro x hx y hy
  have hXQ : (x : ModGL τ K) ∈ Qθ τ K := mem_Qθ_of_mem_highRadical hnode hx
  have hYQ : (y : ModGL τ K) ∈ Qθ τ K := mem_Qθ_of_mem_highRadical hnode hy
  have hXYQ : (x : ModGL τ K) * (y : ModGL τ K) ∈ Qθ τ K := mul_mem hXQ hYQ
  have hXYXQ : (x : ModGL τ K) * (y : ModGL τ K) * (x : ModGL τ K)⁻¹ ∈ Qθ τ K :=
    mul_mem hXYQ (inv_mem hXQ)
  have hC_mem : x * y * x⁻¹ * y⁻¹ ∈ EPilot.highRadical τ K :=
    mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have hcoe : ((x * y * x⁻¹ * y⁻¹ : adjointGroup τ K) : ModGL τ K) =
      (x : ModGL τ K) * (y : ModGL τ K) * (x : ModGL τ K)⁻¹ * (y : ModGL τ K)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hcoord : heisCoord τ K ((x * y * x⁻¹ * y⁻¹ : adjointGroup τ K) : ModGL τ K) = 0 := by
    rw [hcoe]
    rw [(heisCoord_spec τ K).mul _ hXYXQ _ (inv_mem hYQ),
        (heisCoord_spec τ K).mul _ hXYQ _ (inv_mem hXQ),
        (heisCoord_spec τ K).mul _ hXQ _ hYQ,
        heisCoord_inv hXQ, heisCoord_inv hYQ]
    abel
  exact CFSG.SeitzReduction.EPilot.HeisIrr.mem_zpowers_of_heisCoord_eq_zero hnode hK hC_mem hcoord

end E7Model

end CFSG.StandardType.FrameRoute.FS81

end
