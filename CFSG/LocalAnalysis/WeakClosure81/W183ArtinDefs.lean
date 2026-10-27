module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open

@[expose] def ArtinTOrder (p M : ℕ) : Prop :=
  (∃ e : ℕ, 9 < p ^ e ∧ M = ordA 1 (p ^ e)) ∨ M = ordA 2 p ∨ M = ordTwistedA 2 p ∨
    M = ordBC 2 p

@[expose] def ArtinTpOrder (q M : ℕ) : Prop :=
  (∃ f : ℕ, 1 ≤ f ∧ f ≤ 2 ∧ q ^ f ≠ 3 ∧ M = ordA 1 (q ^ f)) ∨ M = ordBC 2 q ∨ M = ordA 3 q ∨
    M = ordTwistedA 3 q ∨ (∃ n : ℕ, 3 ≤ n ∧ M = ordBC n q) ∨ (∃ n : ℕ, 4 ≤ n ∧ M = ordD n q) ∨
    (∃ n : ℕ, 4 ≤ n ∧ M = ordTwistedD n q)

@[expose] def ArtinBig (q M : ℕ) : Prop := ∃ N : ℕ, q ^ N ∣ M ∧ M ^ 2 < (q ^ N) ^ 5

end CFSG.LocalAnalysis.WeakClosure81
