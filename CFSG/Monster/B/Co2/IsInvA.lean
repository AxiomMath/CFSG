module

public import CFSG.Monster.B.Co2.PermArr

public section

namespace CFSG.Monster.B.Co2

open Native

theorem isInvA_iff {n : ℕ} {t r : Array ℕ} :
    Native.isInvA n t r = true ↔ ∀ i < n, (decide (t[i]! < n) && r[t[i]!]! == i) = true := by
  constructor
  · intro h i hi
    have hs := isInvA_spec h hi
    simp [hs.1, hs.2]
  · intro h
    rw [Native.isInvA, allLt_iff]
    exact h

end CFSG.Monster.B.Co2
