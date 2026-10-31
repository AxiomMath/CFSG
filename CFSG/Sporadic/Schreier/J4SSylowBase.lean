
module

import Mathlib.Tactic.IrreducibleDef
public import CFSG.Sporadic.Schreier.J4SSylowCheckBase
public import CFSG.Sporadic.Schreier.J4SLocalNodesBase
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
public import CFSG.Sporadic.Schreier.J4SSylowData
public meta import CFSG.Sporadic.Schreier.J4SSylowData
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

def ActsBy (g : J) (C : Array ℕ) : Prop := ∀ a, g * η a * g⁻¹ = η (app11 C a)

irreducible_def kgen (i : ℕ) : J := signedWord x y (fiveGenWords[i]!)

def vS : J := η 4

def U : Subgroup J := Subgroup.closure (Set.range fun i : Fin 4 => kgen i)

def S0 : Subgroup J := Subgroup.closure (insert vS (Set.range fun i : Fin 4 => kgen i))

theorem kgen_mem_K (i : ℕ) : kgen i ∈ K := by
  rw [kgen_def]; exact signedWord_mem_K _

theorem kgen_mem_U (i : Fin 4) : kgen i ∈ U := Subgroup.subset_closure ⟨i, rfl⟩

theorem U_le_K : U ≤ K := by
  rw [U, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact kgen_mem_K i

def conjGen : Subgroup J := Subgroup.closure {m | ∃ g ∈ U, m = g * vS * g⁻¹}

theorem vS_mem_S0 : vS ∈ S0 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem kgen_mem_S0 (i : Fin 4) : kgen i ∈ S0 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨i, rfl⟩)

theorem U_le_S0 : U ≤ S0 := by
  rw [U, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact kgen_mem_S0 i

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

end CFSG.Sporadic.J4Schreier
