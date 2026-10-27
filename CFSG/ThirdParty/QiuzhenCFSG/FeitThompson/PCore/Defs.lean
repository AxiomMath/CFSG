module

public import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Set.Lattice
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# p-core

This file ...
-/

open scoped Pointwise

variable (p : ℕ) (G : Type*) [Group G]

/-- The set of normal `p`-subgroups of `G`. -/
@[expose]
public def CFSG.normalPSubgroups : Set (Subgroup G) :=
  {K : Subgroup G | K.Normal ∧ IsPGroup p K}

/-- The `p`-core of `G`: the supremum of all normal `p`-subgroups. -/
@[expose]
public def CFSG.pCore : Subgroup G :=
  sSup {K : Subgroup G | K.Normal ∧ IsPGroup p K}

/-- The set of normal subgroups of `G` whose order is coprime to `p`. -/
@[expose]
public def CFSG.normalPPrimeSubgroups : Set (Subgroup G) :=
  {K : Subgroup G | K.Normal ∧ Nat.Coprime p (Nat.card K)}

/-- The `p'`-core of `G`: the supremum of all normal subgroups of order coprime to `p`. -/
@[expose]
public def CFSG.pPrimeCore : Subgroup G :=
  sSup {K : Subgroup G | K.Normal ∧ Nat.Coprime p (Nat.card K)}

public instance CFSG.prime_factors_attach_fact_inst (p : (Nat.card G).primeFactors.attach) : Fact (Nat.Prime p.1.1) :=
  ⟨Nat.prime_of_mem_primeFactors p.1.2⟩
