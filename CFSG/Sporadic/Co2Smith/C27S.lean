module

public import CFSG.Sporadic.Co2Smith.CCFacts

public section

namespace CFSG.Sporadic.Co2Smith

theorem syl_facts
    (hc : CCFacts) {k : ℕ} (hk : k < 3) :
    ∃ U : Subgroup Cz, U ≤ XC (k + 3) ∧ Nat.card U = Native.ccSylSize[k]! ∧ zCz ∈ U ∧
      ∀ y ∈ U, (∀ u ∈ U, u * y = y * u) → y * y = 1 → y ≠ 1 → y ≠ zCz → invEInv y ≠ 32 :=
  hc.syl k hk

end CFSG.Sporadic.Co2Smith
