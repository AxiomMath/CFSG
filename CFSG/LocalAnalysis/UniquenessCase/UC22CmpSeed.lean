module

public import CFSG.Quasithin.Background.C118Class

public section

namespace CFSG.Quasithin

open Subgroup CFSG CFSG.QuasithinUnique.Setup.Campbell

namespace SeedData

variable {T : Type} [Group T]

theorem natLike_twist (X₁ : SeedData T) (β : T ≃* T) :
    NatLike (⊤ : Subgroup T) (X₁.Qh.map β.toMonoidHom) (X₁.Vh.map β.toMonoidHom)
      (X₁.Zh.map β.toMonoidHom) (Nat.card X₁.k) := by
  have := X₁.partnerData.nat.map (equiv_injective β)
  rwa [map_top_equiv] at this

theorem blockType_of_not_le [Finite T] (X₁ X₂ : SeedData T) (β : T ≃* T)
    (hβ : ¬ X₁.Vh.map β.toMonoidHom ≤ X₂.Qh) : X₂.BlockType := by
  obtain ⟨-, -, hsup⟩ := (X₁.natLike_twist β).outside X₂.partnerData.nat hβ
  have hN := (X₁.partnerData_at X₂ β).nat
  refine ⟨(X₁.Vh.map β.toMonoidHom).map X₂.f, hN.V_le, hN.V_normal, hN.V_elem, ?_, ?_⟩
  · refine le_trans hN.comm_le ?_
    intro z hz
    exact Subgroup.mem_centralizer_iff.mpr fun s hs => hN.Z_central s hs z hz
  · have := congrArg (Subgroup.map X₂.f) hsup
    rw [Subgroup.map_sup, X₂.map_Qh, X₂.map_top] at this
    exact this.symm

theorem not_le_symm (X₁ X₂ : SeedData T) (β : T ≃* T) (hβ : ¬ X₁.Vh.map β.toMonoidHom ≤ X₂.Qh) :
    ¬ X₂.Vh.map β.symm.toMonoidHom ≤ X₁.Qh := by
  obtain ⟨-, hV₂⟩ := (X₁.natLike_twist β).inf_eq_of_not_le X₂.partnerData.nat hβ
  intro hle
  apply hV₂
  have h2 := Subgroup.map_mono (f := β.toMonoidHom) hle
  have hcomp : β.toMonoidHom.comp β.symm.toMonoidHom = MonoidHom.id T := by
    ext x
    simp
  rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at h2

theorem fh_map_le_core_or_blockType [Finite T] (X₁ X₂ : SeedData T) (β : T ≃* T) :
    (X₁.Fh.map β.toMonoidHom).map X₂.f ≤ CFSG.pCore 2 X₂.G ∨ X₁.BlockType := by
  by_cases hV : X₁.Vh.map β.toMonoidHom ≤ X₂.Qh
  · left
    refine PartnerData.fp_le_core X₂.seed (X₁.partnerData_at X₂ β) ?_
    rw [← X₂.map_Qh]
    exact Subgroup.map_mono hV
  · right
    exact blockType_of_not_le X₂ X₁ β.symm (not_le_symm X₁ X₂ β hV)

end SeedData

end CFSG.Quasithin
