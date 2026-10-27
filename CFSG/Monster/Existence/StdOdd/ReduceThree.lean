module

public import CFSG.Monster.Existence.StdOdd.Reduce

public section

namespace CFSG.Monster.Existence.StdOdd

open CFSG.LieType.Chevalley.C2E6Std CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

theorem babyLineOddThree_of_std
    (h : (∀ M : Subgroup Rgrp, Odd (Nat.card M) → Nat.card M ≤ 54463) ∧
      (∀ M : Subgroup Rgrp, Odd (Nat.card M) → Nat.card M ∣ 3 ^ 6 * 5 ^ 2 * 7 * 11 * 19 →
        Nat.card M ≤ 9477) ∧
      (∀ M : Subgroup Rgrp, Odd (Nat.card M) → Nat.card M ∣ 3 ^ 7 * 5 ^ 2 * 7 * 11 * 19 →
        Nat.card M ≤ 15309)) :
    ∀ r : B, BabyInv 0 r → ∀ M : Subgroup B, M ≤ Subgroup.centralizer ({r} : Set B) →
      Odd (Nat.card M) → Nat.card M ≤ 54463 ∧
        (Nat.card M ∣ 3 ^ 6 * 5 ^ 2 * 7 * 11 * 19 → Nat.card M ≤ 9477) ∧
        (Nat.card M ∣ 3 ^ 7 * 5 ^ 2 * 7 * 11 * 19 → Nat.card M ≤ 15309) := by
  have h3 : Nat.card ↥(Subgroup.centralizer ({babyRep 3} : Set B)) ≠ babyCentOrder 0 := by
    have e : Nat.card ↥(Subgroup.centralizer ({babyRep 3} : Set B)) = babyCentOrder 2 :=
      natCard_centralizer_rep_three
    rw [e]
    decide
  intro r hr M hM hodd
  obtain ⟨N, hN⟩ := exists_subgroup_stdGroup_card_eq h3 hr hM hodd
  have hNodd : Odd (Nat.card N) := by rwa [hN]
  refine ⟨hN ▸ h.1 N hNodd, fun hd => hN ▸ h.2.1 N hNodd (hN ▸ hd),
    fun hd => hN ▸ h.2.2 N hNodd (hN ▸ hd)⟩

end CFSG.Monster.Existence.StdOdd
