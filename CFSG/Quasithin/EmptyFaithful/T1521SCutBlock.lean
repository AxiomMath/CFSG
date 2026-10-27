module

public import CFSG.Quasithin.EmptyFaithful.T1521SCutDefs
public import CFSG.Quasithin.EmptyFaithful.T1521SCutOrd
import CFSG.Assembly.OrderReductions.LinearOrders

public section

namespace CFSG.Quasithin.T1521SCut

open CFSG.Quasithin CFSG.QuasithinUnique

theorem card_quotient_isAltType {G : Type} [Group G] {L : Subgroup G} (h : IsAltType L 5) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 60 := by
  obtain ⟨α, hα, hker, -⟩ := h
  have e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem card_quotient_isLin2Type {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (hn : 1 ≤ n)
    (h : IsLin2Type L n) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2 ^ n * ((2 ^ n) ^ 2 - 1) ∧
      Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
  obtain ⟨F, _, _, hF, α, hα, hker, -⟩ := h
  have e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  have hFc : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv,
      CFSG.OrderReductions.LinearOrders.card_specialLinear F 2 (by norm_num), hFc]
    simp
  · have hc : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) = 1 := by
      rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 2 (by norm_num), hFc]
      exact Nat.coprime_two_left.mpr (odd_two_pow_sub_one hn)
    have hc' : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 1 := by
      rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hc]
    exact Subgroup.card_eq_one.mp hc'

theorem block_ne {Q : Type} [Group Q]
    (hQ : Nat.card Q = 60 ∨ ∃ n : ℕ, 2 ≤ n ∧ Nat.card Q = 2 ^ n * ((2 ^ n) ^ 2 - 1) ∧
      Subgroup.center Q = ⊥) :
    ¬ (IsAlt 7 (Q ⧸ Subgroup.center Q) ∨ IsPSL 3 2 1 (Q ⧸ Subgroup.center Q) ∨
        IsAlt 6 (Q ⧸ Subgroup.center Q) ∨ IsPSU 3 3 1 (Q ⧸ Subgroup.center Q)) ∧
      ¬ (IsPSL 4 2 1 Q ∨ IsPSL 5 2 1 Q) := by
  have hdvd : Nat.card (Q ⧸ Subgroup.center Q) ∣ Nat.card Q := (Subgroup.center Q).index_dvd_card
  have hmul := (Subgroup.center Q).card_eq_card_quotient_mul_card_subgroup
  rcases hQ with h60 | ⟨n, hn, hcard, hZ⟩
  · rw [h60] at hdvd
    refine ⟨?_, ?_⟩
    · rintro (h | h | h | h)
      · have := card_isAlt_seven h
        rw [this] at hdvd
        revert hdvd
        decide
      · have := card_isPSL_three_two_one h
        rw [this] at hdvd
        revert hdvd
        decide
      · have := card_isAlt_six h
        rw [this] at hdvd
        revert hdvd
        decide
      · have := card_isPSU_three_three_one h
        rw [this] at hdvd
        revert hdvd
        decide
    · rintro (h | h)
      · have := card_isPSL_four_two_one h
        omega
      · have := card_isPSL_five_two_one h
        omega
  · have hZc : Nat.card (Subgroup.center Q) = 1 := by
      rw [hZ]
      exact Subgroup.card_bot
    rw [hZc, mul_one] at hmul
    rw [show (2 ^ n) ^ 2 = 4 ^ n by rw [← pow_mul, mul_comm, pow_mul]; norm_num] at hcard
    refine ⟨?_, ?_⟩
    · rintro (h | h | h | h)
      · exact lin2_order_ne hn (Or.inl rfl) (by rw [← hcard, hmul, card_isAlt_seven h])
      · exact lin2_order_ne hn (Or.inr (Or.inl rfl))
          (by rw [← hcard, hmul, card_isPSL_three_two_one h])
      · exact lin2_order_ne hn (Or.inr (Or.inr (Or.inl rfl)))
          (by rw [← hcard, hmul, card_isAlt_six h])
      · exact lin2_order_ne hn (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          (by rw [← hcard, hmul, card_isPSU_three_three_one h])
    · rintro (h | h)
      · exact lin2_order_ne hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
          (by rw [← hcard, card_isPSL_four_two_one h])
      · exact lin2_order_ne hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
          (by rw [← hcard, card_isPSL_five_two_one h])

end CFSG.Quasithin.T1521SCut

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Quasithin.T1521SCut

theorem typeCutBlock1521 : TypeCutBlock1521 := by
  intro G _ _ L _ hL
  refine block_ne ?_
  rcases hL with h5 | ⟨n, hn, hlin⟩
  · exact Or.inl (card_quotient_isAltType h5)
  · obtain ⟨hc, hZ⟩ := card_quotient_isLin2Type (by omega) hlin
    exact Or.inr ⟨n, hn, hc, hZ⟩

end CFSG.Quasithin
