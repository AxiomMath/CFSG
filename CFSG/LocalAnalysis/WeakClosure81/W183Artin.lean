module

public import CFSG.LocalAnalysis.WeakClosure81.W183CF
public import CFSG.LocalAnalysis.WeakClosure81.W183ArtinArith
public import CFSG.ClassicalInvolution.Orders.Classical

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.Blueprint (LieModel)

theorem w183art_artinTOrder_of_model {T : Type} [Group T] {p : ℕ} (hp2 : p ≠ 2)
    (h : (∃ e : ℕ, 9 < p ^ e ∧ CFSG.Quasithin.F6.IsL2 p e T) ∨ LieModel T .PSL 3 p 1 ∨
      LieModel T .PSU 3 p 1 ∨ LieModel T .PSp 2 p 1) : ArtinTOrder p (Nat.card T) := by
  rcases h with ⟨e, he, hL⟩ | h | h | h
  · have hc : Nat.card T = ordA (2 - 1) (p ^ e) :=
      (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 hL).1 rfl
    rw [show (2 : ℕ) - 1 = 1 by norm_num] at hc
    exact Or.inl ⟨e, he, hc⟩
  · have hc : Nat.card T = ordA (3 - 1) (p ^ 1) :=
      (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
        (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h)).1 rfl
    rw [show (3 : ℕ) - 1 = 2 by norm_num, pow_one] at hc
    exact Or.inr (Or.inl hc)
  · have hc : Nat.card T = ordTwistedA (3 - 1) (p ^ 1) :=
      (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
        (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h)).2.1 rfl
    rw [show (3 : ℕ) - 1 = 2 by norm_num, pow_one] at hc
    exact Or.inr (Or.inr (Or.inl hc))
  · have hc : Nat.card T = ordBC 2 (p ^ 1) :=
      (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
        (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h)).2.2.1 rfl
    rw [pow_one] at hc
    exact Or.inr (Or.inr (Or.inr hc))

theorem w183art_artinTpOrder_of_model {T' : Type} [Group T'] {q : ℕ} (hq2 : q ≠ 2)
    (h : (∃ f : ℕ, f ≤ 2 ∧ LieModel T' .PSL 2 q f) ∨ LieModel T' .PSp 2 q 1 ∨
      LieModel T' .PSL 4 q 1 ∨ LieModel T' .PSU 4 q 1 ∨
      (∃ n : ℕ, LieModel T' .POmegaOdd n q 1 ∨ LieModel T' .POmegaPlus n q 1 ∨
        LieModel T' .POmegaMinus n q 1)) : ArtinTpOrder q (Nat.card T') := by
  rcases h with ⟨f, hf, hL⟩ | h | h | h | ⟨n, hOdd | hPlus | hMinus⟩
  · obtain ⟨-, hf1, -, -, hne⟩ := hL.admissible
    have hq3 : q ^ f ≠ 3 := fun h3 => hne (by rw [h3])
    have hc : Nat.card T' = ordA (2 - 1) (q ^ f) :=
      (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hq2
        (LieModel.statedClassicalModel_of_ne_zero (by norm_num) hL)).1 rfl
    rw [show (2 : ℕ) - 1 = 1 by norm_num] at hc
    exact Or.inl ⟨f, hf1, hf, hq3, hc⟩
  · have hc : Nat.card T' = ordBC 2 (q ^ 1) :=
      (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hq2
        (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h)).2.2.1 rfl
    rw [pow_one] at hc
    exact Or.inr (Or.inl hc)
  · have hc : Nat.card T' = ordA (4 - 1) (q ^ 1) :=
      (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hq2
        (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h)).1 rfl
    rw [show (4 : ℕ) - 1 = 3 by norm_num, pow_one] at hc
    exact Or.inr (Or.inr (Or.inl hc))
  · have hc : Nat.card T' = ordTwistedA (4 - 1) (q ^ 1) :=
      (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hq2
        (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h)).2.1 rfl
    rw [show (4 : ℕ) - 1 = 3 by norm_num, pow_one] at hc
    exact Or.inr (Or.inr (Or.inr (Or.inl hc)))
  · obtain ⟨-, -, hn3, -⟩ := hOdd.admissible
    have hc : Nat.card T' = ordBC n (q ^ 1) :=
      (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hq2
        (LieModel.statedClassicalModel_of_ne_zero (by omega) hOdd)).2.2.2.1 rfl
    rw [pow_one] at hc
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn3, hc⟩))))
  · obtain ⟨-, -, hn4⟩ := hPlus.admissible
    have hc : Nat.card T' = ordD n (q ^ 1) :=
      (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hq2
        (LieModel.statedClassicalModel_of_ne_zero (by omega) hPlus)).2.2.2.2.1 rfl
    rw [pow_one] at hc
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn4, hc⟩)))))
  · obtain ⟨-, -, hn4⟩ := hMinus.admissible
    have hc : Nat.card T' = ordTwistedD n (q ^ 1) :=
      (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hq2
        (LieModel.statedClassicalModel_of_ne_zero (by omega) hMinus)).2.2.2.2.2 rfl
    rw [pow_one] at hc
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, hn4, hc⟩)))))

theorem artinDistinctOddOrders_holds : ArtinDistinctOddOrders := by
  intro T T' _ _ _ _ _ _ p q hp hq hp2 hpq hq35 hT hT' hcard
  have hq2 : q ≠ 2 := by rcases hq35 with rfl | rfl <;> decide
  exact artin_orders_ne hp hp2 hq35 hpq (w183art_artinTOrder_of_model hp2 hT)
    (hcard ▸ w183art_artinTpOrder_of_model hq2 hT')

end CFSG.LocalAnalysis.WeakClosure81
