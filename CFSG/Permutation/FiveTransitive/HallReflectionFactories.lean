module

public import CFSG.Permutation.FiveTransitive.HallReflectionData

public section

namespace CFSG

namespace FiveTransitive.Research.HallReflectionFactories

open MulAction
open Research.HallOrbitTransitivity
open Research.HallReflectionData
open Research.HallDihedralLifts

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

theorem reflectionFactory_six
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hX : 8 ≤ Fintype.card X)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b)
    (haBase : ∀ i, a • e i =
      e (Research.SharpFourBound.baseSingleSwap i))
    (hbBase : ∀ i, b • e i =
      e (Research.SharpFourBound.baseDoubleSwap i))
    (p q : X) (hap : a • p = q) (hpq : p ≠ q)
    (hFa : MulAction.fixedBy X a = {e 0, e 1})
    (hFb : MulAction.fixedBy X b = {p, q})
    (hFc : MulAction.fixedBy X (a * b) = {e 2, e 3}) :
    ∀ y : X, y ∉ exceptionalSet (X := X) a b →
      ∃ y₀ : X, ∃ v : G,
        (y₀ = y ∨ y₀ = b • y) ∧
          y₀ ∉ exceptionalSet (X := X) a b ∧
          HallReflectionAt (exceptionalSet (X := X) a b)
            (exceptionalReflection e p q) a b y₀ v := by
  intro y hy
  have hya : a • y ≠ y := by
    intro h
    exact hy (Or.inl (Or.inl h))
  have hyb : b • y ≠ y := by
    intro h
    exact hy (Or.inl (Or.inr h))
  have hyc : (a * b) • y ≠ y := by
    intro h
    exact hy (Or.inr h)
  have hbp : b • p = p := by
    change p ∈ MulAction.fixedBy X b
    rw [hFb]
    simp
  have hbq : b • q = q := by
    change q ∈ MulAction.fixedBy X b
    rw [hFb]
    simp
  obtain ⟨u, huY, huAY, huBY, huCY, huSq, hua, hub⟩ :=
    exists_hall_quarterTurn_of_odd_stabilizer
      h4 e hodd a b haTwo hbTwo hab y hya hyb hyc
  obtain ⟨y₀, u', v, _huChoice, _hv, hyChoice, _hyOrbit,
      hy₀E, href⟩ :=
    exists_HallReflectionAt_six h4 hX e hodd a b haTwo hbTwo hab
      haBase hbBase p q hap hpq hbp hbq hFa hFb hFc y hya hyb hyc
      u huY huAY huBY huCY huSq hua hub
  exact ⟨y₀, v, hyChoice, hy₀E, href⟩

theorem reflectionFactory_seven
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hX : 8 ≤ Fintype.card X)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b)
    (haBase : ∀ i, a • e i =
      e (Research.SharpFourBound.baseSingleSwap i))
    (hbBase : ∀ i, b • e i =
      e (Research.SharpFourBound.baseDoubleSwap i))
    (p q r : X) (hap : a • p = q) (hpq : p ≠ q)
    (hFa : MulAction.fixedBy X a = {e 0, e 1, r})
    (hFb : MulAction.fixedBy X b = {p, q, r})
    (hFc : MulAction.fixedBy X (a * b) = {e 2, e 3, r})
    (hD : MulAction.fixedBy X a ∩ MulAction.fixedBy X b = {r}) :
    ∀ y : X, y ∉ exceptionalSet (X := X) a b →
      ∃ y₀ : X, ∃ v : G,
        (y₀ = y ∨ y₀ = b • y) ∧
          y₀ ∉ exceptionalSet (X := X) a b ∧
          HallReflectionAt (exceptionalSet (X := X) a b)
            (exceptionalReflection e p q) a b y₀ v := by
  intro y hy
  have hya : a • y ≠ y := by
    intro h
    exact hy (Or.inl (Or.inl h))
  have hyb : b • y ≠ y := by
    intro h
    exact hy (Or.inl (Or.inr h))
  have hyc : (a * b) • y ≠ y := by
    intro h
    exact hy (Or.inr h)
  have hbp : b • p = p := by
    change p ∈ MulAction.fixedBy X b
    rw [hFb]
    simp
  have hbq : b • q = q := by
    change q ∈ MulAction.fixedBy X b
    rw [hFb]
    simp
  obtain ⟨u, huY, huAY, huBY, huCY, huSq, hua, hub⟩ :=
    exists_hall_quarterTurn_of_odd_stabilizer
      h4 e hodd a b haTwo hbTwo hab y hya hyb hyc
  obtain ⟨y₀, u', v, _huChoice, _hv, hyChoice, _hyOrbit,
      hy₀E, href⟩ :=
    exists_HallReflectionAt_seven h4 hX e hodd a b haTwo hbTwo hab
      haBase hbBase p q r hap hpq hbp hbq hFa hFb hFc hD
      y hya hyb hyc u huY huAY huBY huCY huSq hua hub
  exact ⟨y₀, v, hyChoice, hy₀E, href⟩

theorem exists_orientedQuarterTurn_six
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b)
    (haBase : ∀ i, a • e i =
      e (Research.SharpFourBound.baseSingleSwap i))
    (hbBase : ∀ i, b • e i =
      e (Research.SharpFourBound.baseDoubleSwap i))
    (p q : X) (hap : a • p = q)
    (hFa : MulAction.fixedBy X a = {e 0, e 1})
    (hFb : MulAction.fixedBy X b = {p, q})
    (hFc : MulAction.fixedBy X (a * b) = {e 2, e 3})
    (y : X) (hy : y ∉ exceptionalSet (X := X) a b) :
    ∃ u : G,
      u • e 0 = e 0 ∧ u • e 1 = e 1 ∧
      u • e 2 = q ∧ u • q = e 3 ∧
      u • e 3 = p ∧ u • p = e 2 := by
  have hya : a • y ≠ y := fun h ↦ hy (Or.inl (Or.inl h))
  have hyb : b • y ≠ y := fun h ↦ hy (Or.inl (Or.inr h))
  have hyc : (a * b) • y ≠ y := fun h ↦ hy (Or.inr h)
  obtain ⟨u, huY, huAY, _huBY, _huCY, huSq, hua, hub⟩ :=
    exists_hall_quarterTurn_of_odd_stabilizer
      h4 e hodd a b haTwo hbTwo hab y hya hyb hyc
  obtain ⟨u', _huChoice, hu0, hu1, hu2, huq, hu3, hup⟩ :=
    Research.HallExceptionalOrientation.exists_oriented_quarterTurn_six
      h4 e hodd a b haTwo hbTwo hab haBase hbBase p q hap
        hFa hFb hFc y hya u huY huAY huSq hua hub
  exact ⟨u', hu0, hu1, hu2, huq, hu3, hup⟩

theorem exists_orientedQuarterTurn_seven
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b)
    (haBase : ∀ i, a • e i =
      e (Research.SharpFourBound.baseSingleSwap i))
    (hbBase : ∀ i, b • e i =
      e (Research.SharpFourBound.baseDoubleSwap i))
    (p q r : X) (hap : a • p = q)
    (hFa : MulAction.fixedBy X a = {e 0, e 1, r})
    (hFb : MulAction.fixedBy X b = {p, q, r})
    (hD : MulAction.fixedBy X a ∩ MulAction.fixedBy X b = {r})
    (y : X) (hy : y ∉ exceptionalSet (X := X) a b) :
    ∃ u : G,
      u • e 0 = e 0 ∧ u • e 1 = e 1 ∧ u • r = r ∧
      u • e 2 = q ∧ u • q = e 3 ∧
      u • e 3 = p ∧ u • p = e 2 := by
  have hya : a • y ≠ y := fun h ↦ hy (Or.inl (Or.inl h))
  have hyb : b • y ≠ y := fun h ↦ hy (Or.inl (Or.inr h))
  have hyc : (a * b) • y ≠ y := fun h ↦ hy (Or.inr h)
  obtain ⟨u, huY, huAY, _huBY, _huCY, huSq, hua, hub⟩ :=
    exists_hall_quarterTurn_of_odd_stabilizer
      h4 e hodd a b haTwo hbTwo hab y hya hyb hyc
  obtain ⟨u', _huChoice, hu0, hu1, hur, hu2, huq, hu3, hup⟩ :=
    Research.HallExceptionalOrientation.exists_oriented_quarterTurn
      h4 e hodd a b haTwo hbTwo hab haBase hbBase p q r hap
        hFa hFb hD y hya u huY huAY huSq hua hub
  exact ⟨u', hu0, hu1, hur, hu2, huq, hu3, hup⟩

end FiveTransitive.Research.HallReflectionFactories

end CFSG
