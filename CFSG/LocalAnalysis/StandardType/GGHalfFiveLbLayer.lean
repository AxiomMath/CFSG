module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveBElt
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveLayer
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂)

include h

theorem centralizer_b_inf_L :
    Subgroup.centralizer ({bElt φ₁ φ₂} : Set G) ⊓ L =
      (Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2))).map φ₁ := by
  ext l
  constructor
  · intro hl
    rw [Subgroup.mem_inf] at hl
    obtain ⟨hlC, hlL⟩ := hl
    rw [← h.coords.range₁] at hlL
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hlL
    rw [Subgroup.mem_map]
    refine ⟨s, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hlC ⊢
    have h1 : bElt φ₁ φ₂ * φ₁ s * (bElt φ₁ φ₂)⁻¹ = φ₁ s := by
      rw [← hlC]; group
    rw [bElt_act_L h s] at h1
    have h2 : zeta5 * s * zeta5⁻¹ = s := h.coords.inj₁ h1
    have h4 : zeta5 * s = s * zeta5 := by
      calc zeta5 * s = zeta5 * s * zeta5⁻¹ * zeta5 := by group
        _ = s * zeta5 := by rw [h2]
    exact h4.symm
  · intro hl
    rw [Subgroup.mem_map] at hl
    obtain ⟨s, hs, rfl⟩ := hl
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff] at hs ⊢
      have h2 : zeta5 * s * zeta5⁻¹ = s := by rw [← hs]; group
      have hb : bElt φ₁ φ₂ * φ₁ s * (bElt φ₁ φ₂)⁻¹ = φ₁ s := by
        rw [bElt_act_L h s, h2]
      calc φ₁ s * bElt φ₁ φ₂
          = (bElt φ₁ φ₂ * φ₁ s * (bElt φ₁ φ₂)⁻¹) * bElt φ₁ φ₂ := by rw [hb]
        _ = bElt φ₁ φ₂ * φ₁ s := by group
    · rw [← h.coords.range₁]
      exact MonoidHom.mem_range.mpr ⟨s, rfl⟩

theorem lb_layer :
    sl3four.map φ₁ = LargeEvenLayer (Subgroup.centralizer ({bElt φ₁ φ₂} : Set G) ⊓ L) := by
  rw [centralizer_b_inf_L h, largeEvenLayer_map_of_injective φ₁ h.coords.inj₁, sl3four_layer.1]

theorem isComponentOf_lb :
    IsComponentOf (sl3four.map φ₁) (Subgroup.centralizer ({bElt φ₁ φ₂} : Set G) ⊓ L) := by
  rw [centralizer_b_inf_L h]
  exact isComponentOf_map_of_injective φ₁ h.coords.inj₁ sl3four_layer.2

end GGHalfCtx

end CFSG.StandardType

end
