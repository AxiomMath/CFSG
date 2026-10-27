module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKDefs

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

@[expose] def NKLeafU3OddOut : Prop :=
  ∀ (p : ℕ), p.Prime → 13 ≤ p → p % 4 = 1 → ∀ (X : Type) [Group X], IsPSU 3 p 1 X →
    ∀ S : Subgroup X, IsSylowTwoOf S ⊤ →
      UOut X (Subgroup.centralizer ((S ⊓ Subgroup.centralizer (S : Set X) : Subgroup X) : Set X))

end CFSG.Quasithin.H13.L829NK
