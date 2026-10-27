module

public import CFSG.Quasithin.EmptyFaithful.T1521SCutOrd

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.Quasithin.T1521SCut

theorem famOrders_mul_two_pow_alt :
    ∀ m ∈ famOrders, ∀ k < 40, m * 2 ^ k ≠ 360 ∧ m * 2 ^ k ≠ 2520 := by
  decide

@[expose] def TypeCutCompAlt1521 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), CFSG.Open.IsQuasisimple ↥L →
    (IsBender1516 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ (∃ n : ℕ, IsPSL 3 2 n (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
      ∃ n : ℕ, IsPSp4 2 n (↥L ⧸ CFSG.pCore 2 ↥L)) → ¬ (IsAlt 6 ↥L ∨ IsAlt 7 ↥L)

theorem typeCutCompAlt1521 : TypeCutCompAlt1521 := by
  intro G _ _ L _ hfam hbad
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
  have hcard : Nat.card ↥L = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) * 2 ^ k := by
    rw [(CFSG.pCore 2 ↥L).card_eq_card_quotient_mul_card_subgroup, hk]
  have hmain : ∀ N : ℕ, (N = 360 ∨ N = 2520) → Nat.card ↥L = N → False := by
    intro N hN hLN
    have hNle : N ≤ orderBound := by
      unfold orderBound
      rcases hN with rfl | rfl <;> norm_num
    have hN40 : N < 2 ^ 40 := by
      rcases hN with rfl | rfl <;> norm_num
    have h : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) * 2 ^ k = N := by rw [← hcard, hLN]
    have hY : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ≤ orderBound := by
      refine le_trans ?_ hNle
      rw [← h]
      exact Nat.le_mul_of_pos_right _ (by positivity)
    obtain ⟨hmem, -⟩ := famCases hfam hY
    have hk40 : k < 40 := lt_forty_of_mul_two_pow (famOrders_pos _ hmem) hN40 h
    obtain ⟨h1, h2⟩ := famOrders_mul_two_pow_alt _ hmem k hk40
    rcases hN with rfl | rfl
    · exact h1 h
    · exact h2 h
  rcases hbad with hA6 | hA7
  · exact hmain 360 (Or.inl rfl) (card_isAlt_six hA6)
  · exact hmain 2520 (Or.inr rfl) (card_isAlt_seven hA7)

end CFSG.Quasithin.E9
