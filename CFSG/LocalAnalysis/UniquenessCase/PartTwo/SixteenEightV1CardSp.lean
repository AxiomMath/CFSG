module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelPiece

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem s16e_card_eq_of_isSpn_six {X Y : Type} [Group X] [Group Y] (hX : IsSpn X 6 1)
    (hY : IsSpn Y 6 1) : Nat.card X = Nat.card Y := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  obtain ⟨-, K', _, _, hK', ⟨e'⟩⟩ := hY
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype K' := Fintype.ofFinite K'
  have hcard : Fintype.card K = Fintype.card K' := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hK']
  let σ : K ≃+* K' := FiniteField.ringEquivOfCardEq hcard
  rw [Nat.card_congr e.toEquiv, Nat.card_congr e'.toEquiv,
    CFSG.SeitzReduction.SymplecticPilot.card_statedSp_eq_of_ringEquiv σ]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
