module

public import Certificates.Data.Kernel.EvenSporM22.HS08DDefs

public section

namespace CFSG.KC.EvenSporM22

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck
  CFSG.EvenSporadicStandard.M22Std.HS08Check

@[expose] def jInnJ (J : List Tab) : List Tab := J.filter fun l => decide (l ∈ s0Inner)

@[expose] def jOutJ (J : List Tab) : List Tab := J.filter fun l => decide (l ∈ s0Outer)

@[expose] def jOrbJ (J : List Tab) (x : Tab) : List Tab :=
  (jOutJ J).filter fun y => dTabs.any fun d => decide (tmul d x = tmul y d)

@[expose] def x4J (J : List Tab) : Tab := ((jInnJ J).filter fun l => decide (l ≠ idTab)).headD idTab

@[expose] def x6J (J : List Tab) : Tab := (jOutJ J).getD 5 idTab

@[expose] def x10J (J : List Tab) : Tab := (jOutJ J).getD 0 idTab

@[expose] def NormPropJ (J : List Tab) : Prop :=
  (jInnJ J).length = 16 ∧ (jOutJ J).length = 16 ∧
  (∀ l ∈ dTabs, (∀ j ∈ J, tmul l j = tmul j l) → l ∈ J) ∧
  (∀ y ∈ (jInnJ J).filter fun l => decide (l ≠ idTab), ∃ d ∈ dTabs, tmul d (x4J J) = tmul y d) ∧
  x4J J ∈ J ∧ x6J J ∈ J ∧ x10J J ∈ J ∧
  (jOrbJ J (x6J J)).length = 6 ∧ (jOrbJ J (x10J J)).length = 10 ∧
  (∀ y ∈ jOutJ J, y ∈ jOrbJ J (x6J J) ∨ y ∈ jOrbJ J (x10J J)) ∧
  (∀ y ∈ jOrbJ J (x6J J), y ∉ jOrbJ J (x10J J)) ∧
  (∀ d ∈ dTabs, ∀ x ∈ jOrbJ J (x6J J), ∃ y ∈ jOrbJ J (x6J J), tmul d x = tmul y d) ∧
  (∀ d ∈ dTabs, ∀ x ∈ jOrbJ J (x10J J), ∃ y ∈ jOrbJ J (x10J J), tmul d x = tmul y d)

@[expose] def hs08O6 : List Tab := [5, 6, 10, 11, 13, 15].map fun i => (jOutJ jLit).getD i idTab

@[expose] def hs08O10 : List Tab :=
  [0, 1, 2, 3, 4, 7, 8, 9, 12, 14].map fun i => (jOutJ jLit).getD i idTab

@[expose] def hs08DW (a j : Nat) : Tab := tmul (s0Tabs.getD a []) (dReps.getD j [])

@[expose] def HS08Norms (O : List Tab) (g : Tab) : Prop := ∀ z ∈ O, ∃ y ∈ O, tmul g z = tmul y g

instance (O : List Tab) (g : Tab) : Decidable (HS08Norms O g) := by
  unfold HS08Norms
  infer_instance

@[expose] def HS08WitOK (x : Tab) (Ys : List Tab) (R : List (Nat × Nat)) : Prop :=
  ∀ y ∈ Ys, ∃ p ∈ R, p.1 < 256 ∧ p.2 < 15 ∧ tmul (hs08DW p.1 p.2) x = tmul y (hs08DW p.1 p.2)

instance (x : Tab) (Ys : List Tab) (R : List (Nat × Nat)) : Decidable (HS08WitOK x Ys R) := by
  unfold HS08WitOK
  infer_instance

@[expose] def hs08W4 : List (Nat × Nat) :=
  [(0, 0), (6, 1), (1, 1), (0, 3), (1, 0), (5, 1), (3, 1), (0, 10), (3, 0), (7, 1), (0, 1), (4, 3),
   (2, 0), (4, 1), (2, 1)]

@[expose] def hs08W6 : List (Nat × Nat) := [(0, 0), (2, 4), (0, 4), (6, 4), (1, 0), (4, 4)]

@[expose] def hs08W10 : List (Nat × Nat) :=
  [(0, 0), (0, 4), (4, 1), (1, 1), (2, 0), (0, 1), (3, 0), (1, 4), (1, 0), (5, 1)]

@[expose] def hs08CentT : List (Tab × Nat) :=
  [(1, 3), (6, 1), (2, 1)].map fun q => (jLit.getD q.1 idTab, q.2)

@[expose] def HS08CentOK (T : List (Tab × Nat)) : Prop :=
  (∀ q ∈ T, q.1 ∈ jLit ∧ q.1.length = 22 ∧ q.2 < 22) ∧
  ∀ l ∈ dTabs, (∀ q ∈ T, l.getD (q.1.getD q.2 0) 0 = q.1.getD (l.getD q.2 0) 0) → l ∈ jLit

instance (T : List (Tab × Nat)) : Decidable (HS08CentOK T) := by
  unfold HS08CentOK
  infer_instance

end CFSG.KC.EvenSporM22
