module

public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.Monster.GMS.Facts.BabyTables
public import CFSG.Monster.GMS.Defs

public section

namespace CFSG.Monster.Existence.StdOdd

open CFSG.LieType.Chevalley.C2E6Std CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

abbrev Rgrp : Type := ↥stdGroup

@[expose] def StdOddBounds (R : Type*) [Group R] : Prop :=
  (∀ M : Subgroup R, Odd (Nat.card M) → Nat.card M ≤ 54463) ∧
  (∀ M : Subgroup R, Odd (Nat.card M) → Nat.card M ∣ 3 ^ 6 * 5 ^ 2 * 7 * 11 * 19 →
    Nat.card M ≤ 9477)

@[expose] def BabyLineOddOrderWeak : Prop :=
  ∀ r : B, BabyInv 0 r → ∀ M : Subgroup B, M ≤ Subgroup.centralizer ({r} : Set B) →
    Odd (Nat.card M) → Nat.card M ≤ 54463 ∧
      (Nat.card M ∣ 3 ^ 6 * 5 ^ 2 * 7 * 11 * 19 → Nat.card M ≤ 9477)

structure CentralizerFacts (R : Type*) [Group R] : Prop where
  c5 : ∀ x : R, orderOf x = 5 →
    Nat.card (Subgroup.centralizer ({x} : Set R)) ∣ 2 ^ 6 * 3 ^ 2 * 5 ^ 2 * 7
  c7 : ∀ x : R, orderOf x = 7 →
    Nat.card (Subgroup.centralizer ({x} : Set R)) ∣ 2 ^ 6 * 3 ^ 2 * 5 * 7 ^ 2
  c11 : ∀ x : R, orderOf x = 11 → Nat.card (Subgroup.centralizer ({x} : Set R)) ∣ 2 * 3 * 11
  c13 : ∀ x : R, orderOf x = 13 → Nat.card (Subgroup.centralizer ({x} : Set R)) = 13
  c17 : ∀ x : R, orderOf x = 17 → Nat.card (Subgroup.centralizer ({x} : Set R)) ∣ 3 * 17
  c19 : ∀ x : R, orderOf x = 19 → Nat.card (Subgroup.centralizer ({x} : Set R)) ∣ 3 * 19

structure ThreeLocalFacts (R : Type*) [Group R] : Prop where
  rank3 : ∀ A : Subgroup R, (∀ a ∈ A, a ^ 3 = 1) → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
    Nat.card A ≤ 3 ^ 5
  syl5 : ∀ T : Subgroup R, Nat.card T = 3 ^ 9 →
    ∀ g ∈ Subgroup.normalizer (T : Set R), orderOf g ≠ 5
  syl13 : ∀ T : Subgroup R, Nat.card T = 3 ^ 9 →
    ∀ g ∈ Subgroup.normalizer (T : Set R), orderOf g ≠ 13
  sub7 : ∀ F : Subgroup R, Nat.card F = 3 ^ 8 →
    ∀ g ∈ Subgroup.normalizer (F : Set R), orderOf g ≠ 7
  elem11 : ∀ X : Subgroup R, (∀ a ∈ X, a ^ 3 = 1) → (∀ a ∈ X, ∀ b ∈ X, a * b = b * a) →
    Nat.card X = 3 ^ 5 → ∀ g ∈ Subgroup.normalizer (X : Set R), orderOf g ≠ 11

end CFSG.Monster.Existence.StdOdd
