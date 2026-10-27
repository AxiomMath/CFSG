module

public import CFSG.Timmesfeld.Orders.ExceptionalTwisted
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.Timmesfeld

open CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank ExceptionalOrders

theorem card_chevalleyExceptionalModel_untwisted {G : Type} [Group G] {t : StatedLieTag}
    {p f : ℕ} (h : ChevalleyExceptionalModel G t p f) :
    (t = .G2 → Nat.card G = ordG2 (p ^ f)) ∧ (t = .F4 → Nat.card G = ordF4 (p ^ f)) ∧
      (t = .E6 → Nat.card G = ordE6 (p ^ f)) ∧ (t = .E7 → Nat.card G = ordE7 (p ^ f)) ∧
        (t = .E8 → Nat.card G = ordE8 (p ^ f)) := by
  obtain ⟨-, hm⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl
  · exact card_of_untwistedChevalleyModel_G2 hm
  · exact card_of_untwistedChevalleyModel_F4 hm
  · exact card_of_untwistedChevalleyModel_E6 hm
  · exact card_of_untwistedChevalleyModel_E7 hm
  · exact card_of_untwistedChevalleyModel_E8 hm

theorem card_chevalleyExceptionalModel_two {G : Type} [Group G] {t : StatedLieTag} {f : ℕ}
    (h : ChevalleyExceptionalModel G t 2 f) :
    Nat.card G = match t with
      | .G2 => ordG2 (2 ^ f) | .F4 => ordF4 (2 ^ f) | .E6 => ordE6 (2 ^ f)
      | .E7 => ordE7 (2 ^ f) | .E8 => ordE8 (2 ^ f) | .twistedE6 => ordTwistedE6 (2 ^ f)
      | .trialityD4 => ordTrialityD4 (2 ^ f) | _ => 0 := by
  obtain ⟨⟨-, hf, -⟩, hm⟩ := h
  cases t
  case G2 => exact card_of_untwistedChevalleyModel_G2 hm
  case F4 => exact card_of_untwistedChevalleyModel_F4 hm
  case E6 => exact card_of_untwistedChevalleyModel_E6 hm
  case E7 => exact card_of_untwistedChevalleyModel_E7 hm
  case E8 => exact card_of_untwistedChevalleyModel_E8 hm
  case twistedE6 => exact card_of_twistedChevalleyModel_E6_two hf hm
  case trialityD4 => exact card_of_twistedChevalleyModel_D4_two hf hm
  all_goals exact hm.elim

end CFSG.Timmesfeld
