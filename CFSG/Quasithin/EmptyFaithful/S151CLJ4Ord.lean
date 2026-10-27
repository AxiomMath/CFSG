module

public import CFSG.Quasithin.EmptyFaithful.S151XF
public import CFSG.Quasithin.EmptyFaithful.S146zXGOrder
public import CFSG.Quasithin.H13.VolIA38Orders
public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.Quasithin.EmptyFaithful.A38c8M24

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.VolI
open scoped commutatorElement

namespace J4Excl

theorem isQuasisimple_of_isSporadic_m24 {Q : Type} [Group Q]
    (h : IsSporadic .M24 Q) : CFSG.IsQuasisimple Q := by
  have hZ := A38c8.center_eq_bot_of_isSporadic_m24 h
  obtain ⟨e⟩ := h
  have hs0 : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M24) :=
    CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  have hs : IsSimpleGroup Q := e.isSimpleGroup
  have hnc : ∃ a b : Q, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have htop : Subgroup.center Q = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro g
      exact hcon g x
    rw [hZ] at htop
    obtain ⟨x, hx⟩ := exists_ne (1 : Q)
    have hx' : x ∈ (⊥ : Subgroup Q) := htop ▸ Subgroup.mem_top x
    exact hx (Subgroup.mem_bot.1 hx')
  have e2 : (Q ⧸ Subgroup.center Q) ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨?_, e2.isSimpleGroup, ?_⟩
  · rw [Group.isPerfect_def]
    have : (commutator Q).Normal := inferInstance
    rcases hs.eq_bot_or_eq_top_of_normal (commutator Q) with h1 | h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      have : ⁅a, b⁆ ∈ commutator Q := Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
        (Subgroup.mem_top b)
      rw [h1, Subgroup.mem_bot] at this
      exact (commutatorElement_eq_one_iff_mul_comm.1 this)
    · exact h1
  · obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e2.symm a, e2.symm b, fun h => hab (by
      have := congrArg e2 h
      simpa using this)⟩

theorem twoPart_m24 : ∃ r : ℕ, Odd r ∧ (244823040 : ℕ) = 2 ^ 10 * r :=
  ⟨239085, by decide, by norm_num⟩

theorem card_isAlt {m : ℕ} (hm : 2 ≤ m) {X : Type} [Group X] (h : IsAlt m X) :
    Nat.card X = m.factorial / 2 := by
  obtain ⟨e⟩ := h
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
    Fintype.card_fin]

theorem not_isPSL_two_two_of_card {Q : Type} [Group Q] (hN : Nat.card Q = 244823040) (n : ℕ)
    (hn : 2 ≤ n) : ¬ IsPSL 2 2 n Q := by
  intro h
  have h1 := S146zX.card_isPSL_two_even h
  rw [hN] at h1
  by_cases h10 : n = 10
  · subst h10
    norm_num at h1
  · have h2 := two_part_ordA_one (n := n) (by omega)
    rw [ordA_one_two_pow (by omega)] at h2
    exact ne_of_two_part twoPart_m24 h2 (Ne.symm h10) h1

theorem not_isPSL_three_two_of_card {Q : Type} [Group Q] (hN : Nat.card Q = 244823040) (n : ℕ)
    (hn : 2 ≤ n) : ¬ IsPSL 3 2 n Q := by
  intro h
  have h1 : Nat.card Q = ordA 2 (2 ^ n) := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
  rw [hN] at h1
  exact ne_of_two_part twoPart_m24 (two_part_ordA_two (e := n) (by omega)) (by omega) h1

theorem not_isPSp4_two_of_card {Q : Type} [Group Q] (hN : Nat.card Q = 244823040) (n : ℕ)
    (hn : 2 ≤ n) : ¬ IsPSp4 2 n Q := by
  intro h
  have h1 : Nat.card Q = ordBC 2 (2 ^ n) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.1 rfl
  rw [hN] at h1
  exact ne_of_two_part twoPart_m24 (two_part_ordBC_two (e := n) (by omega)) (by omega) h1

theorem not_isG2_two_of_card
    {Q : Type} [Group Q] (hN : Nat.card Q = 244823040) (n : ℕ)
    (hn : 2 ≤ n) : ¬ IsG2 2 n Q := by
  intro h
  have h1 : Nat.card Q = ordG2 (2 ^ n) := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
  rw [hN] at h1
  exact ne_of_two_part twoPart_m24 (two_part_ordG2 (e := n) (by omega)) (by omega) h1

theorem not_isPSL_four_five_of_card {Q : Type} [Group Q] (hN : Nat.card Q = 244823040) :
    ¬ (IsPSL 4 2 1 Q ∨ IsPSL 5 2 1 Q) := by
  rintro (h | h)
  · have := S146zX.card_isPSL_four_two h
    omega
  · have := S146zX.card_isPSL_five_two h
    omega

theorem not_typeD_of_card {Q : Type} [Group Q] (hN : Nat.card Q = 244823040)
    (hZ : Subgroup.center Q = ⊥) :
    ¬ (IsAlt 7 (Q ⧸ Subgroup.center Q) ∨ IsPSL 3 2 1 (Q ⧸ Subgroup.center Q) ∨
      IsAlt 6 (Q ⧸ Subgroup.center Q) ∨ IsPSU 3 3 1 (Q ⧸ Subgroup.center Q)) := by
  have hc : Nat.card (Q ⧸ Subgroup.center Q) = 244823040 := by
    rw [← hN]
    exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv
  rintro (h | h | h | h)
  · have := S146zX.card_isAlt_seven h
    omega
  · have := S146zX.card_isPSL_three_two h
    omega
  · have h6 := card_isAlt (m := 6) (by norm_num) h
    have : Nat.factorial 6 / 2 = 360 := by decide
    omega
  · have := CFSG.Quasithin.H13.card_of_statedClassicalModel_psu_three_three h
    omega

theorem not_lists_of_isSporadic_m24
    {G : Type} [Group G] {K : Subgroup G}
    (h : IsSporadic .M24 (↥K ⧸ CFSG.pCore 2 ↥K)) :
    ¬ (ListA15120 K ∨ ListB15120 K ∨ ListC15120 K ∨ ListD15120 K) := by
  have hN := A38c8.card_of_isSporadic_m24 h
  have hZ := A38c8.center_eq_bot_of_isSporadic_m24 h
  rintro (⟨n, hn, hA⟩ | (⟨n, hn, hB⟩ | ⟨n, hn, hB⟩ | ⟨n, hn, hB⟩) | hC | hD)
  · exact not_isPSL_two_two_of_card hN n hn hA
  · exact not_isPSL_three_two_of_card hN n hn hB
  · exact not_isPSp4_two_of_card hN n hn hB
  · exact not_isG2_two_of_card hN n hn hB
  · exact not_isPSL_four_five_of_card hN hC
  · exact not_typeD_of_card hN hZ hD

end J4Excl

end CFSG.Quasithin
