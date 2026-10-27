module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432L2List
public import CFSG.RankThree.PartTwo.Sec4.RonanK432L2Outer
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.GorensteinWalter
open CFSG.Assembly.RankThreeEven (projSL)

theorem nine_le_card_of_char_three {F : Type} [Field F] [Finite F] [CharP F 3]
    (h4 : 4 ≤ Nat.card F) : 9 ≤ Nat.card F := by
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e, he⟩ := FiniteField.card F 3
  have hcard : Nat.card F = 3 ^ (e : ℕ) := by rw [Nat.card_eq_fintype_card, he.2]
  rw [hcard] at h4 ⊢
  have h2 : 2 ≤ (e : ℕ) := by
    by_contra h
    have h1 : (e : ℕ) ≤ 1 := by omega
    have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) h1
    omega
  calc 9 = 3 ^ 2 := by norm_num
    _ ≤ 3 ^ (e : ℕ) := Nat.pow_le_pow_right (by norm_num) h2

theorem goodRow_psl2 (F : Type) [Field F] [Finite F] : GoodRow (PSL2 F) := by
  refine ⟨?_, outerRow_psl2⟩
  by_cases h4 : 4 ≤ Nat.card F
  · by_cases h3 : ringChar F = 3
    · haveI : CharP F 3 := h3 ▸ ringChar.charP F
      exact listRow_psl2_of_char_three (nine_le_card_of_char_three h4)
    · exact listRow_psl2_of_char_ne_three h3 h4
  · have h1 : 1 < Nat.card F := Finite.one_lt_card
    have hc := card_psl2_mul_gcd F
    have hF : Nat.card F = 2 ∨ Nat.card F = 3 := by omega
    rcases hF with hF | hF
    · rw [hF] at hc
      have : Nat.card (PSL2 F) = 6 := by simpa using hc
      exact listRow_of_card (by rw [this]; norm_num) (by rw [this]; norm_num)
    · rw [hF] at hc
      have : Nat.card (PSL2 F) = 12 := by simp at hc; omega
      exact listRow_of_card (by rw [this]; norm_num) (by rw [this]; norm_num)

theorem rowOf_projSL_two (F : Type) [Field F] [Finite F] : RowOf (projSL 2 F) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv (e.trans (projSLEquivPSL F)).symm (goodRow_psl2 F)

end CFSG.RankThree.PartTwo.Sec4.RonanK432
