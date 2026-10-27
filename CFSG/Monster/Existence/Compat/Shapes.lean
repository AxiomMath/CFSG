module

public import CFSG.Monster.Existence.Defs

public section

namespace CFSG.Monster.Existence.Compat

open CFSG CFSG.Open CFSG.Blueprint CFSG.Monster.Existence

structure TwoAFacts : Prop where
  b_simple : IsSimpleGroup NativeSporadic.B
  b_card : Nat.card NativeSporadic.B = monsterBabyOrder
  co2_simple : IsSimpleGroup NativeSporadic.Co2
  co2_card : Nat.card NativeSporadic.Co2 = monsterCo2Order
  fi23_simple : IsSimpleGroup NativeSporadic.Fi23
  fi23_card : Nat.card NativeSporadic.Fi23 = monsterFi23Order
  th_simple : IsSimpleGroup NativeSporadic.Th
  th_card : Nat.card NativeSporadic.Th = monsterThOrder
  mcl_simple : IsSimpleGroup NativeSporadic.McL
  mcl_card : Nat.card NativeSporadic.McL = monsterMcLOrder
  hn_simple : IsSimpleGroup NativeSporadic.HN
  hn_card : Nat.card NativeSporadic.HN = monsterHNOrder
  fi22_simple : IsSimpleGroup NativeSporadic.Fi22
  fi22_card : Nat.card NativeSporadic.Fi22 = monsterFi22Order
  e6_simple : ∀ (X : Type) [Group X], LieModel X .twistedE6 0 2 1 → IsSimpleGroup X
  e6_card : ∀ (X : Type) [Group X], LieModel X .twistedE6 0 2 1 → Nat.card X = ordTwistedE6 2
  f4_simple : ∀ (X : Type) [Group X], LieModel X .F4 0 2 1 → IsSimpleGroup X
  f4_card : ∀ (X : Type) [Group X], LieModel X .F4 0 2 1 → Nat.card X = ordF4 2
  u62_card : ∀ (X : Type) [Group X], LieModel X .PSU 6 2 1 → Nat.card X = ordTwistedA 5 2

variable {G : Type} [Group G]

theorem monsterHasShape_of_quot {H : Subgroup G} {N : Subgroup H} (hn : N.Normal) {k n : ℕ}
    (hN : Nat.card N = 2 ^ k) (hs : IsSimpleGroup (H ⧸ N)) (hc : Nat.card (H ⧸ N) = n) :
    MonsterHasShape H k n :=
  ⟨N, hn, hN, hs, hc⟩

section PerIndex

variable (F : TwoAFacts) (H : Subgroup G)
include F

theorem shape_zero (h : TwoPointShape H 0) : MonsterHasShape H 1 monsterBabyOrder := by
  obtain ⟨N, hn, hN, ⟨e⟩⟩ := h
  exact monsterHasShape_of_quot hn hN (@MulEquiv.isSimpleGroup _ _ _ _ F.b_simple e)
    ((Nat.card_congr e.toEquiv).trans F.b_card)

theorem shape_one (h : TwoPointShape H 1) : MonsterHasShape H 2 (ordTwistedE6 2) := by
  obtain ⟨N, hn, -, hN, hm⟩ := h
  exact monsterHasShape_of_quot hn hN (F.e6_simple _ hm) (F.e6_card _ hm)

theorem shape_two (h : TwoPointShape H 2) : MonsterHasShape H 24 monsterCo2Order := by
  obtain ⟨N, hn, N₀, -, -, -, -, -, hN, ⟨e⟩⟩ := h
  exact monsterHasShape_of_quot hn hN (@MulEquiv.isSimpleGroup _ _ _ _ F.co2_simple e)
    ((Nat.card_congr e.toEquiv).trans F.co2_card)

theorem shape_three (h : TwoPointShape H 3) : MonsterHasShape H 0 monsterFi23Order := by
  obtain ⟨e⟩ := h
  exact monsterHasShape_of_quot (N := ⊥) inferInstance (by rw [Subgroup.card_bot, pow_zero])
    (@MulEquiv.isSimpleGroup _ _ _ _ F.fi23_simple ((QuotientGroup.quotientBot).trans e))
    ((Nat.card_congr ((QuotientGroup.quotientBot).trans e).toEquiv).trans F.fi23_card)

theorem shape_four (h : TwoPointShape H 4) : MonsterHasShape H 0 monsterThOrder := by
  obtain ⟨e⟩ := h
  exact monsterHasShape_of_quot (N := ⊥) inferInstance (by rw [Subgroup.card_bot, pow_zero])
    (@MulEquiv.isSimpleGroup _ _ _ _ F.th_simple ((QuotientGroup.quotientBot).trans e))
    ((Nat.card_congr ((QuotientGroup.quotientBot).trans e).toEquiv).trans F.th_card)

theorem shape_five (h : TwoPointShape H 5) : MonsterHasShape H 23 monsterMcLOrder := by
  obtain ⟨N, hn, -, hN, ⟨e⟩⟩ := h
  exact monsterHasShape_of_quot hn hN (@MulEquiv.isSimpleGroup _ _ _ _ F.mcl_simple e)
    ((Nat.card_congr e.toEquiv).trans F.mcl_card)

theorem shape_six (h : TwoPointShape H 6) : MonsterHasShape H 1 (ordF4 2) := by
  obtain ⟨N, hn, hN, hm⟩ := h
  exact monsterHasShape_of_quot hn hN (F.f4_simple _ hm) (F.f4_card _ hm)

theorem shape_seven (h : TwoPointShape H 7) : MonsterHasShape H 0 monsterHNOrder := by
  obtain ⟨e⟩ := h
  exact monsterHasShape_of_quot (N := ⊥) inferInstance (by rw [Subgroup.card_bot, pow_zero])
    (@MulEquiv.isSimpleGroup _ _ _ _ F.hn_simple ((QuotientGroup.quotientBot).trans e))
    ((Nat.card_congr ((QuotientGroup.quotientBot).trans e).toEquiv).trans F.hn_card)

theorem shape_eight (h : TwoPointShape H 8) : MonsterHasShape H 1 monsterFi22Order := by
  obtain ⟨N, hn, hN, ⟨e⟩⟩ := h
  exact monsterHasShape_of_quot hn hN (@MulEquiv.isSimpleGroup _ _ _ _ F.fi22_simple e)
    ((Nat.card_congr e.toEquiv).trans F.fi22_card)

end PerIndex

theorem hasShape_of_twoPointShape (F : TwoAFacts) (H : Subgroup G) (i : Fin 9)
    (h : TwoPointShape H i) :
    MonsterHasShape H (monsterSuborbitTwoExponent i) (monsterSuborbitSimpleOrder i) := by
  match i, h with
  | 0, h => exact shape_zero F H h
  | 1, h => exact shape_one F H h
  | 2, h => exact shape_two F H h
  | 3, h => exact shape_three F H h
  | 4, h => exact shape_four F H h
  | 5, h => exact shape_five F H h
  | 6, h => exact shape_six F H h
  | 7, h => exact shape_seven F H h
  | 8, h => exact shape_eight F H h

end CFSG.Monster.Existence.Compat
