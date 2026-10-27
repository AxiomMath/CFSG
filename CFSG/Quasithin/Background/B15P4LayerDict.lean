module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.Quasithin.B15P4

variable {V : Type} [CommGroup V]

theorem card_mul_card_fixV_bot :
    Nat.card (⊥ : Subgroup (MulAut V)) * Nat.card (fixV (⊥ : Subgroup (MulAut V))) =
      Nat.card V := by
  rw [Subgroup.card_bot, B1.fixV_bot, Subgroup.card_top, one_mul]

theorem isElemAbelian2_of_le {A B : Subgroup (MulAut V)} (hA : IsElemAbelian2 A) (hBA : B ≤ A) :
    IsElemAbelian2 B :=
  ⟨fun a ha b hb => hA.1 a (hBA ha) b (hBA hb), fun a ha => hA.2 a (hBA ha)⟩

theorem isFFStarMin_iff_isBestOffender {H A : Subgroup (MulAut V)} :
    IsFFStarMin H A ↔ CFSG.QuasithinUnique.Setup.Family.IsBestOffender H A := by
  constructor
  · rintro ⟨hA, hmin⟩
    refine ⟨hA.1, hA.2.1, hA.2.2.1, ?_, fun B hBA hB0 hBne => ?_⟩
    · have h := hA.2.2.2 ⊥ bot_le
      rwa [card_mul_card_fixV_bot] at h
    · refine lt_of_le_of_ne (hA.2.2.2 B hBA) fun heq => hBne (hmin B ?_ ?_)
      · exact B1_4_2 hA ⟨⟨hBA.trans hA.1, hB0, isElemAbelian2_of_le hA.2.2.1 hBA⟩, hA.isA2, hBA,
          heq⟩
      · exact ⟨⟨hBA.trans hA.1, hB0, isElemAbelian2_of_le hA.2.2.1 hBA⟩, hA.isA2, hBA, heq⟩
  · rintro ⟨hAH, hA0, hAel, hoff, hstrict⟩
    have hoff' : IsFFStarOffender H A := by
      refine ⟨hAH, hA0, hAel, fun B hBA => ?_⟩
      by_cases hB0 : B = ⊥
      · rw [hB0, card_mul_card_fixV_bot]
        exact hoff
      · by_cases hBA' : B = A
        · rw [hBA']
        · exact (hstrict B hBA hB0 hBA').le
    refine ⟨hoff', fun B hB hBA => ?_⟩
    by_contra hne
    have h := hstrict B hBA.2.2.1 hB.2.1 hne
    rw [hBA.2.2.2] at h
    exact lt_irrefl _ h

end CFSG.Quasithin.B15P4
