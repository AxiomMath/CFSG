module

public import CFSG.Quasithin.EmptyFaithful.Gold14610Defs
public import CFSG.Quasithin.EmptyFaithful.S14610Q1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

theorem concl14610Core_of_coreW {G : Type} [Group G] [Finite G] {I K : Subgroup G}
    (c : Gold14610.Concl14610CoreW I K) : Concl14610Core I K := by
  refine ⟨?_⟩
  rcases c.shape with h | ⟨hb, hHat | hG2 | ⟨h6, hw⟩ | ⟨h7, hw⟩⟩
  · exact Or.inl ⟨h, trivial⟩
  · exact Or.inr ⟨hb, Or.inl ⟨hHat, trivial⟩⟩
  · exact Or.inr ⟨hb, Or.inr (Or.inl ⟨hG2, trivial⟩)⟩
  · exact Or.inr ⟨hb, Or.inr (Or.inr (Or.inl ⟨h6, trivial, hw⟩))⟩
  · exact Or.inr ⟨hb, Or.inr (Or.inr (Or.inr ⟨h7, trivial, hw⟩))⟩

theorem input14610ListN_of_listW (h : Gold14610.Input14610ListW) : Input14610ListN :=
  fun G _ _ T M H u I I₂ h27 c hsyl hLT hT hF =>
    concl14610Core_of_coreW (h G T M H u I I₂ h27 c hsyl hLT hT hF)

end CFSG.Quasithin
