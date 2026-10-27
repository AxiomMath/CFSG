module

public import CFSG.Sporadic.Ly.Setup
import CFSG.Sporadic.Ly.ThreeBSpec

public section

namespace Certificates

open CFSG.Sporadic.Ly in
theorem certificate5220 : ∃ _ : LySeed, ∃ y : CFSG.Sporadic.Ly.J, orderOf y = 3 ∧
    Nat.card ↥(Subgroup.centralizer ({y} : Set CFSG.Sporadic.Ly.J)) ≤ 174960 :=
  ⟨inferInstance, CFSG.Sporadic.Ly.exists_threeB_element⟩

end Certificates
