module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.Monster.GMS

variable {G : Type*} [Group G]

@[expose] def twoANbr (a x : G) : Set G := {y | IsConj a y ∧ IsConj a (x * y)}

@[expose] def twoABNbr (a z₀ x : G) : Set G := {w | IsConj z₀ w ∧ IsConj a (x * w)}

@[expose] def twoBNbr (a z₀ x : G) : Set G := {y | IsConj a y ∧ IsConj z₀ (x * y)}

@[expose] def twoBBNbr (z₀ x : G) : Set G := {w | IsConj z₀ w ∧ IsConj z₀ (x * w)}

@[expose] def fourANbr (a z₀ x : G) : Set G :=
  {y | IsConj a y ∧ orderOf (x * y) = 4 ∧ IsConj z₀ ((x * y) ^ 2)}

@[expose] def fourBNbr (a x : G) : Set G :=
  {y | IsConj a y ∧ orderOf (x * y) = 4 ∧ IsConj a ((x * y) ^ 2)}

@[expose] def sixANbr (a x : G) : Set G :=
  {y | IsConj a y ∧ orderOf (x * y) = 6 ∧ IsConj a ((x * y) ^ 3)}

end CFSG.Monster.GMS
