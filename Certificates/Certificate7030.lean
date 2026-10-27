module

public import CFSG.Quasithin.H13.LocDblOdd
import Certificates.Kernel.He7030.Final

public section

namespace Certificates

open CFSG.Quasithin.H13.LocDbl in
theorem certificate7030 : 
    SylowNoDouble ↥CFSG.Sporadic.He.J ∧
      OddIndexBound ↥CFSG.Sporadic.He.J [138240, 138240, 21504] ∧
      ∀ X S : Subgroup CFSG.Sporadic.He.J, Nat.card S = 2 ^ 10 → S ≤ X → 5 ∣ Nat.card X →
        ¬ 9 ∣ Nat.card X → False := by
  exact ⟨CFSG.KD.He7030.sylowNoDouble_He_groupK, CFSG.KD.He7030.oddIndexBound_He_groupK,
    CFSG.KD.He7030.overSylow_JK⟩

end Certificates

end
