module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocDef
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocOmega

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4
open CFSG.Quasithin.J4Loc (omegaZ)

@[expose] def burnsideJ4NP_IsHCl (A B : Subgroup J) : Prop :=
  ∃ P : Subgroup J, P ≤ Hj ⊓ Subgroup.centralizer (A : Set J) ∧ IsPGroup 2 ↥P ∧
    (∀ Q : Subgroup J, Q ≤ Hj ⊓ Subgroup.centralizer (A : Set J) → IsPGroup 2 ↥Q → P ≤ Q →
      Q = P) ∧ omegaZ P = B

@[expose] def burnsideJ4NP_Is2A (x : J) : Prop := ∃ g : J, x = g * CFSG.Quasithin.J4Loc.z0 * g⁻¹

end CFSG.ASVolI
