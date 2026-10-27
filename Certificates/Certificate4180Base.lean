
module

public import Certificates.Data.TwoF4LieCheck
public import CFSG.Sporadic.Schreier.TitsActionCheckInputs
public import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
public import CFSG.Sporadic.Schreier.TitsAction
public import Mathlib.Logic.Relation

import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4SpecBase

@[expose] public section

open CFSG.Sporadic.Schreier.Tits

open scoped Pointwise

namespace Certificates

@[expose] noncomputable def c4180T : Equiv.Perm (Fin 1755) :=
  titsGen 3 * titsGen 2 * titsGen 3 * titsGen 0 * titsGen 3 * titsGen 2 * (titsGen 3)⁻¹

@[expose] noncomputable def c4180C : Equiv.Perm (Fin 1755) :=
  titsGen 1 * titsGen 2 * (titsGen 1)⁻¹ * titsGen 2 * titsGen 1 * titsGen 2 * titsGen 1 *
    titsGen 2 * titsGen 2 * titsGen 0

@[expose] def c4180Step (x y : Equiv.Perm (Fin 1755)) : Prop :=
  (x ∈ titsA ∧ x 0 = 0 ∧ x • titsLine 0 = titsLine 0) ∧
    (y ∈ titsA ∧ y 0 = 0 ∧ y • titsLine 0 = titsLine 0) ∧
    ∃ g ∈ titsA, (g 0 = 0 ∨ g • titsLine 0 = titsLine 0) ∧ y = g * x * g⁻¹

end Certificates

