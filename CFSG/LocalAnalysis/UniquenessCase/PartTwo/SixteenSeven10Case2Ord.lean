module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SixteenOrd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1CardO

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

theorem s16c1610_card_of_isSym {X : Type} [Group X] {n : ℕ} (h : IsSym X n) :
    Nat.card X = Nat.factorial n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin n)),
    Fintype.card_perm, Fintype.card_fin]

theorem s16c1610_card_of_isSpn_six {X : Type} [Group X] (h : IsSpn X 6 1) :
    Nat.card X = 1451520 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv,
    show (6 / 2 : ℕ) = 3 from rfl,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK]
  decide

theorem s16c1610_card_of_isOmegaMinus_eight {Y : Type} [Group Y] (h : IsOmegaMinus Y 8 1) :
    Nat.card Y = 197406720 := by
  obtain ⟨-, K, _, _, b, c, hK, hirr, ⟨e⟩⟩ := h
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have h8 := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus (K := K)
    (n := 4) (by norm_num) hirr
  rw [hK] at h8
  rw [Nat.card_congr e.toEquiv]
  have h9 : ((Nat.card (StatedProj (StatedOmega (StatedQuadMinus (8 / 2) K b c))) : ℕ) : ℤ) =
      197406720 := by
    rw [show (8 / 2 : ℕ) = 4 from rfl, h8]
    decide
  exact_mod_cast h9

theorem s16c1610_card_of_isOMinus_six {X Y : Type} [Group X] [Group Y] (hX : IsOMinus X 6 1)
    (hY : IsOmegaMinus Y 6 1) : Nat.card X = 51840 := by
  rw [s16e_card_eq_two_mul_of_isOMinus (Or.inl rfl) hX hY, s16c167_card_isOmegaMinus_six hY]

theorem s16c1610_card_of_isOMinus_eight {X Y : Type} [Group X] [Group Y] (hX : IsOMinus X 8 1)
    (hY : IsOmegaMinus Y 8 1) : Nat.card X = 394813440 := by
  rw [s16e_card_eq_two_mul_of_isOMinus (Or.inr rfl) hX hY, s16c1610_card_of_isOmegaMinus_eight hY]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
