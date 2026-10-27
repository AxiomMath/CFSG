module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridge
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGPseudoReflStabModInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J →
      ∀ φ ∈ ggAutomizer (Subgroup.centralizer ({x} : Set G)) Bs, GGIsPseudoReflection p φ →
        ∃ ψ ∈ ggAutomizer (ggG0 p B x L D J) Bs, (∀ b : ↥Bs, (b : G) = x → ψ b = b) ∧
          ∀ b : ↥Bs, (((ψ b)⁻¹ * φ b : ↥Bs) : G) ∈ Subgroup.zpowers x

theorem ggPseudoReflStabInput_of_mod (h : GGPseudoReflStabModInput) : GGPseudoReflStabInput := by
  intro G _ _ p B Bs x L D J hH φ hφ hφp
  obtain ⟨ψ, hψ, hψx, hmod⟩ := h G p B Bs x L D J hH φ hφ hφp
  have hcfg := hH.1
  have : Fact p.Prime := ⟨hcfg.1.2.2.2.2.2.1.1⟩
  have hS := hcfg.1.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hS.2.1
  have hx1 : (⟨x, hxBs⟩ : ↥Bs) ≠ 1 := fun h => hS.2.2.1 (congrArg Subtype.val h)
  have hφx : φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ :=
    ggAutomizer_apply_eq_of_le_centralizer (x := ⟨x, hxBs⟩) le_rfl hφ
  have hmod' : ∀ b : ↥Bs, (ψ b)⁻¹ * φ b ∈ Subgroup.zpowers (⟨x, hxBs⟩ : ↥Bs) := by
    intro b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hmod b)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
  rw [eq_of_mem_zpowers_of_noTransvection hcfg.2.1.2.1 hH.2.2.2.1 hx1
    (mem_ggInduced_top_of_mem_ggAutomizer hφ) (mem_ggInduced_top_of_mem_ggAutomizer hψ) hφx
    (hψx _ rfl) hmod']
  exact hψ

theorem ggPseudoReflStabModInput_of_stab (h : GGPseudoReflStabInput) : GGPseudoReflStabModInput := by
  intro G _ _ p B Bs x L D J hH φ hφ hφp
  refine ⟨φ, h G p B Bs x L D J hH φ hφ hφp, fun b hb => ?_, fun b => ?_⟩
  · have hc : (⟨x, hb ▸ b.2⟩ : ↥Bs) = b := Subtype.ext hb.symm
    rw [← hc]
    exact ggAutomizer_apply_eq_of_le_centralizer le_rfl hφ
  · rw [inv_mul_cancel, Subgroup.coe_one]
    exact Subgroup.one_mem _

end CFSG.StandardType
