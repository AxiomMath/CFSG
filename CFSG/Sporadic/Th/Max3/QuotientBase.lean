
module

public import CFSG.Sporadic.Th.Max3.AltNine
public import CFSG.Sporadic.Th.Max3.QuotientInputsBase
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

@[expose] public section

namespace CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Th.Native CFSG.ComponentClassification.PresentationLocal
open scoped commutatorElement

def aPerm : Equiv.Perm (Fin 9) where
  toFun := ![1, 0, 3, 2, 5, 4, 7, 6, 8]
  invFun := ![1, 0, 3, 2, 5, 4, 7, 6, 8]
  left_inv := by decide
  right_inv := by decide

def bPerm : Equiv.Perm (Fin 9) where
  toFun := ![0, 8, 1, 4, 3, 2, 5, 6, 7]
  invFun := ![0, 2, 5, 4, 3, 6, 7, 8, 1]
  left_inv := by decide
  right_inv := by decide

theorem aPerm_eq : aPerm = altRep4 := by decide

theorem aPerm_mem : aPerm ∈ alternatingGroup (Fin 9) := by
  rw [aPerm_eq]
  exact Equiv.Perm.mem_alternatingGroup.2 sign_altRep4

theorem bPerm_mem : bPerm ∈ alternatingGroup (Fin 9) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

namespace AltQuot

end AltQuot

namespace AltQuot

theorem sq_swap_eq_one {G : Type*} [Group G] {a b : G} (h : (a * b) ^ 2 = 1) :
    (b * a) ^ 2 = 1 := by
  have e : (b * a) ^ 2 = b * (a * b) ^ 2 * b⁻¹ := by
    simp only [sq]
    group
  rw [e, h]
  simp

theorem aPerm_eq_prod :
    (⟨aPerm, aPerm_mem⟩ : alternatingGroup (Fin 9)) =
      carmichaelCycle (carmIdx 2) * carmichaelCycle (carmIdx 3) ^ 2 * carmichaelCycle (carmIdx 2) *
        carmichaelCycle (carmIdx 4) * carmichaelCycle (carmIdx 5) ^ 2 *
        carmichaelCycle (carmIdx 4) * carmichaelCycle (carmIdx 6) *
        carmichaelCycle (carmIdx 7) ^ 2 * carmichaelCycle (carmIdx 6) := by
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, Subgroup.coe_pow]
  change aPerm = carmichaelPerm (carmIdx 2) * carmichaelPerm (carmIdx 3) ^ 2 *
    carmichaelPerm (carmIdx 2) * carmichaelPerm (carmIdx 4) * carmichaelPerm (carmIdx 5) ^ 2 *
    carmichaelPerm (carmIdx 4) * carmichaelPerm (carmIdx 6) * carmichaelPerm (carmIdx 7) ^ 2 *
    carmichaelPerm (carmIdx 6)
  decide

theorem bPerm_eq_prod :
    (⟨bPerm, bPerm_mem⟩ : alternatingGroup (Fin 9)) =
      carmichaelCycle (carmIdx 2) ^ 2 * carmichaelCycle (carmIdx 3) *
        carmichaelCycle (carmIdx 4) ^ 2 * carmichaelCycle (carmIdx 3) *
        carmichaelCycle (carmIdx 5) ^ 2 * carmichaelCycle (carmIdx 6) *
        carmichaelCycle (carmIdx 7) ^ 2 * carmichaelCycle (carmIdx 8) := by
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, Subgroup.coe_pow]
  change bPerm = carmichaelPerm (carmIdx 2) ^ 2 * carmichaelPerm (carmIdx 3) *
    carmichaelPerm (carmIdx 4) ^ 2 * carmichaelPerm (carmIdx 3) * carmichaelPerm (carmIdx 5) ^ 2 *
    carmichaelPerm (carmIdx 6) * carmichaelPerm (carmIdx 7) ^ 2 * carmichaelPerm (carmIdx 8)
  decide

end AltQuot

open AltQuot

namespace AltQuot

end AltQuot

end CFSG.Sporadic.Th.Max3
