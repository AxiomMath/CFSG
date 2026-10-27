module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Hyp
public import CFSG.Quasithin.EmptyFaithful.S1421L2Two

public section

namespace CFSG.Quasithin.Fan86.Univ

variable {A C B : Type} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

theorem card_oTwoQuot_left (h : Hyp53 X) :
    Nat.card (oTwoQuot A) = 10 ∨ Nat.card (oTwoQuot A) = 20 := by
  rcases h.quot_left with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · left
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
  · right
    rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.card_sz_zero]

theorem card_oTwoQuot_right (h : Hyp53 X) : Nat.card (oTwoQuot B) = 6 := by
  obtain ⟨e⟩ := isL2Quot_one_iff_perm3.mp h.quot_right
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
  rfl

end CFSG.Quasithin.Fan86.Univ
