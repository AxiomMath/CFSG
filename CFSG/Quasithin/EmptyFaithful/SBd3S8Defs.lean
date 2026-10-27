module

public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.NormNum.Ineq

public section

namespace CFSG.Quasithin.SBd3S8

abbrev S8 : Type := Equiv.Perm (Fin 8)

theorem perm_apply_inv_self (g : S8) (x : Fin 8) : g (g⁻¹ x) = x := g.apply_symm_apply x

@[expose] def blk2 (i : Fin 8) : ℕ := i.val / 2

@[expose] def blk4 (i : Fin 8) : ℕ := i.val / 4

@[expose] def PW2 (g : S8) : Prop := ∀ i j : Fin 8, blk2 i = blk2 j ↔ blk2 (g i) = blk2 (g j)

@[expose] def PW4 (g : S8) : Prop := ∀ i j : Fin 8, blk4 i = blk4 j ↔ blk4 (g i) = blk4 (g j)

@[expose] def pw2b (g : S8) : Bool :=
  (List.finRange 8).all fun i => (List.finRange 8).all fun j =>
    decide (blk2 i = blk2 j) == decide (blk2 (g i) = blk2 (g j))

@[expose] def pw4b (g : S8) : Bool :=
  (List.finRange 8).all fun i => (List.finRange 8).all fun j =>
    decide (blk4 i = blk4 j) == decide (blk4 (g i) = blk4 (g j))

theorem pw2b_iff (g : S8) : pw2b g = true ↔ PW2 g := by
  simp only [pw2b, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq,
    decide_eq_decide, PW2]

theorem pw4b_iff (g : S8) : pw4b g = true ↔ PW4 g := by
  simp only [pw4b, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq,
    decide_eq_decide, PW4]

instance : DecidablePred PW2 := fun g => decidable_of_iff (pw2b g = true) (pw2b_iff g)

instance : DecidablePred PW4 := fun g => decidable_of_iff (pw4b g = true) (pw4b_iff g)

@[expose] def W2 : Subgroup S8 where
  carrier := {g | PW2 g}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' := fun {g h} hg hh i j => (hh i j).trans (hg (h i) (h j))
  inv_mem' := fun {g} hg i j => by
    have := hg (g⁻¹ i) (g⁻¹ j)
    rw [perm_apply_inv_self, perm_apply_inv_self] at this
    exact this.symm

@[expose] def W4 : Subgroup S8 where
  carrier := {g | PW4 g}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' := fun {g h} hg hh i j => (hh i j).trans (hg (h i) (h j))
  inv_mem' := fun {g} hg i j => by
    have := hg (g⁻¹ i) (g⁻¹ j)
    rw [perm_apply_inv_self, perm_apply_inv_self] at this
    exact this.symm

@[expose] def Tstd : Subgroup S8 := W2 ⊓ W4

instance : DecidablePred (· ∈ W2) := fun g => inferInstanceAs (Decidable (PW2 g))

instance : DecidablePred (· ∈ W4) := fun g => inferInstanceAs (Decidable (PW4 g))

instance : DecidablePred (· ∈ Tstd) := fun g => inferInstanceAs (Decidable (PW2 g ∧ PW4 g))

@[expose] def xor3 (a b c : Fin 8) : Fin 8 :=
  ⟨(a.val ^^^ b.val ^^^ c.val) % 8, Nat.mod_lt _ (by norm_num)⟩

@[expose] def PAff (g : S8) : Prop := ∀ a b c : Fin 8, g (xor3 a b c) = xor3 (g a) (g b) (g c)

@[expose] def pAffb (g : S8) : Bool :=
  (List.finRange 8).all fun a => (List.finRange 8).all fun b => (List.finRange 8).all fun c =>
    g (xor3 a b c) == xor3 (g a) (g b) (g c)

theorem pAffb_iff (g : S8) : pAffb g = true ↔ PAff g := by
  simp only [pAffb, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq, PAff]

instance : DecidablePred PAff := fun g => decidable_of_iff (pAffb g = true) (pAffb_iff g)

@[expose] def Aff : Subgroup S8 where
  carrier := {g | PAff g}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun {g h} hg hh a b c => by
    show g (h (xor3 a b c)) = xor3 (g (h a)) (g (h b)) (g (h c))
    rw [hh a b c, hg (h a) (h b) (h c)]
  inv_mem' := fun {g} hg a b c => by
    apply g.injective
    show g (g⁻¹ (xor3 a b c)) = g (xor3 (g⁻¹ a) (g⁻¹ b) (g⁻¹ c))
    rw [hg, perm_apply_inv_self, perm_apply_inv_self, perm_apply_inv_self, perm_apply_inv_self]

instance : DecidablePred (· ∈ Aff) := fun g => inferInstanceAs (Decidable (PAff g))

@[expose] def tupleOf (g : S8) : List (Fin 8) := [g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7]

theorem eq_of_tupleOf_eq {g h : S8} (e : tupleOf g = tupleOf h) : g = h := by
  simp only [tupleOf, List.cons.injEq, and_true] at e
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := e
  refine Equiv.ext fun i => ?_
  fin_cases i <;> assumption

@[expose, instance_reducible] def decEqS8 : DecidableEq S8 := fun g h =>
  decidable_of_iff (tupleOf g = tupleOf h) ⟨eq_of_tupleOf_eq, fun e => e ▸ rfl⟩

@[expose] def a1 : S8 := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def a2 : S8 := Equiv.swap 0 1 * Equiv.swap 1 3

@[expose] def a3 : S8 := Equiv.swap 4 5 * Equiv.swap 5 6

@[expose] def a4 : S8 := Equiv.swap 4 5 * Equiv.swap 5 7

@[expose] def v1 : List S8 :=
  [1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2]

@[expose] def v2 : List S8 :=
  [1, Equiv.swap 4 5 * Equiv.swap 6 7, Equiv.swap 4 6 * Equiv.swap 5 7,
    Equiv.swap 4 7 * Equiv.swap 5 6]

@[expose] def Elist : List S8 := (v1.map fun x => v2.map fun y => x * y).flatten

@[expose] def tt0 : S8 := Equiv.swap 0 1

@[expose] def uu0 : S8 := Equiv.swap 0 2 * Equiv.swap 1 3

@[expose] def vv : S8 :=
  Equiv.swap 0 4 * Equiv.swap 1 5 * Equiv.swap 2 6 * Equiv.swap 3 7

@[expose] def gtab (a : Fin 8) : S8 :=
  match a with
  | 0 => 1
  | 1 => tt0
  | 2 => uu0
  | 3 => uu0 * tt0
  | 4 => vv
  | 5 => vv * tt0
  | 6 => vv * uu0
  | 7 => vv * uu0 * tt0

end CFSG.Quasithin.SBd3S8
