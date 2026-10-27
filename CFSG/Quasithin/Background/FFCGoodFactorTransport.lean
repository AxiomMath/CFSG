module

public import CFSG.Quasithin.Background.FFC4Tr2

public section

namespace CFSG.Quasithin

namespace FFC

namespace SplitTransport

open CFSG.Open CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] {G G₁ G₂ : Subgroup (MulAut V)}

theorem map_commV_le (hstab : G₂ ≤ stabSub (fixV G₁)) :
    (commV (autSub G₂ (fixV G₁))).map (fixV G₁).subtype ≤ commV G₂ := by
  rw [commV_eq_commSub, map_commSub_autSub hstab, map_top_eq]
  exact commSub_mono le_top le_rfl |>.trans (commV_eq_commSub (X := G₂) ▸ le_rfl)

theorem goodFactor_transport (hstab : G₂ ≤ stabSub (fixV G₁))
    (hfaith : ∀ g ∈ G₂, (∀ v ∈ fixV G₁, g v = v) → g = 1) (hfix : fixV G = fixV G₁ ⊓ fixV G₂)
    (hcomm : commV G₂ ≤ fixV G₁) (hg : GoodFactor (autSub G₂ (fixV G₁))) :
    B56FactorList ↥G₂ ∧ B56Piece G₂ (fixV G₁) (fixV G) := by
  obtain ⟨hF, hP⟩ := hg
  refine ⟨B56FactorList.of_mulEquiv (resEquiv hstab hfaith) hF, ?_⟩
  have hT : ∀ (hT : (⊤ : Subgroup ↥(fixV G₁)) =
      commV (autSub G₂ (fixV G₁)) ⊔ fixV (autSub G₂ (fixV G₁))),
      fixV G₁ = commV G₂ ⊔ fixV G := fun hT => by
    have := congrArg (Subgroup.map (fixV G₁).subtype) hT
    rw [map_top_eq, Subgroup.map_sup, map_fixV_eq hstab hfix] at this
    refine le_antisymm ?_ (sup_le hcomm (by rw [hfix]; exact inf_le_left))
    rw [this]
    exact sup_le_sup_right (map_commV_le hstab) _
  rcases hP with ⟨hT₀, hmod⟩ | ⟨hT₀, m, K, hK, hf, hc, hd⟩ | hC
  · refine Or.inl ⟨hT hT₀, ?_⟩
    rcases hmod with ⟨n, hn⟩ | hn | ⟨m, hm⟩
    · exact Or.inl ⟨n, binaryNaturalSL_transport hstab hfaith hfix hn⟩
    · exact Or.inr (Or.inl (symmetricNatural_transport hstab hfaith hfix hn))
    · exact Or.inr (Or.inr ⟨m, binaryNaturalSL_transport hstab hfaith hfix hm⟩)
  · exact Or.inr (Or.inl ⟨hT hT₀, m, K, hK, hf, hc, directSum_transport hstab hfaith hfix hd⟩)
  · exact Or.inr (Or.inr (pieceC_transport hstab hfaith hfix hcomm hC))

end SplitTransport

end FFC

end CFSG.Quasithin
