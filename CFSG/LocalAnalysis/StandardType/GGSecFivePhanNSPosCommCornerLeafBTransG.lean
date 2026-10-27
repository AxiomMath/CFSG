module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGHalfShear
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommCornerGrp

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggNSPosPF3C_false_of_shear {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    (hNT : GGNoTransvection 3 Bs) (hBs : CFSG.Open.IsElemAbelian 3 Bs) {c₀ γ : G}
    (hc₀ : c₀ ∈ Bs) (hc₀1 : c₀ ≠ 1) (hc₀3 : c₀ ^ 3 = 1) (hγc : γ * c₀ = c₀ * γ)
    (hγ : ∀ b ∈ Bs, ∃ j : ℕ, γ * b * γ⁻¹ * b⁻¹ = c₀ ^ j)
    (hγ1 : ∃ b ∈ Bs, γ * b * γ⁻¹ * b⁻¹ ≠ 1) : False := by
  have hfwd : ∀ b ∈ Bs, γ * b * γ⁻¹ ∈ Bs := by
    intro b hb
    obtain ⟨j, hj⟩ := hγ b hb
    have h1 : γ * b * γ⁻¹ = c₀ ^ j * b := by
      calc γ * b * γ⁻¹ = (γ * b * γ⁻¹ * b⁻¹) * b := by group
        _ = c₀ ^ j * b := by rw [hj]
    rw [h1]
    exact Bs.mul_mem (pow_mem hc₀ j) hb
  have hn : γ ∈ Subgroup.normalizer (Bs : Set G) :=
    ggNSPosPF3C_mem_normalizer_of_conj_mem hfwd
  have hcomm : ∀ b ∈ Bs, ∀ c ∈ Bs, b * c = c * b :=
    fun b hb c hc => congrArg Subtype.val (hBs.1.is_comm.comm ⟨b, hb⟩ ⟨c, hc⟩)
  have hexp : ∀ b ∈ Bs, b ^ 3 = 1 := fun b hb => hBs.2 b hb
  have hna : γ * c₀ * γ⁻¹ = c₀ := by rw [hγc]; group
  have himg : ∀ b ∈ Bs, γ * b * γ⁻¹ * b⁻¹ ∈ Subgroup.zpowers c₀ := by
    intro b hb
    obtain ⟨j, hj⟩ := hγ b hb
    rw [hj]
    exact pow_mem (Subgroup.mem_zpowers c₀) j
  have hmove : ∃ b ∈ Bs, γ * b * γ⁻¹ ≠ b := by
    obtain ⟨b, hb, hbne⟩ := hγ1
    exact ⟨b, hb, fun heq => hbne (by rw [heq, mul_inv_cancel])⟩
  exact (GGHalf.not_noTransvection_of_shear hcomm hexp hn hc₀ hc₀1 hna himg hmove) hNT

end CFSG.StandardType

end
