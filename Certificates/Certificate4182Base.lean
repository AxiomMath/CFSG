module

public import CFSG.Sporadic.Schreier.TitsAction

@[expose] public section

open CFSG.Sporadic.Schreier.Tits

open scoped Pointwise

namespace Certificates

def c4182S (x : Equiv.Perm (Fin 1755)) : Prop :=
  x ∈ titsD ∧ x 0 = 0 ∧ x • titsLine 0 = titsLine 0

def c4182Step (x y : Equiv.Perm (Fin 1755)) : Prop :=
  c4182S x ∧ c4182S y ∧
    ∃ g ∈ titsD, (g 0 = 0 ∨ g • titsLine 0 = titsLine 0) ∧ y = g * x * g⁻¹

def c4182Pair (p p' : Equiv.Perm (Fin 1755) × Equiv.Perm (Fin 1755)) : Prop :=
  c4182S p.1 ∧ c4182S p.2 ∧ c4182S p'.1 ∧ c4182S p'.2 ∧
    ∃ g ∈ titsD, (g 0 = 0 ∨ g • titsLine 0 = titsLine 0) ∧ p'.1 = g * p.1 * g⁻¹ ∧
      p'.2 = g * p.2 * g⁻¹

noncomputable def c4182Q : Equiv.Perm (Fin 1755) :=
  titsGen 2 * titsGen 1 * titsGen 1 * titsGen 2 * titsGen 3 * titsGen 0 * (titsGen 3)⁻¹

end Certificates

