
module

public import CFSG.Sporadic.Schreier.J4SCheckBase
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SNative

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.SectionRank CFSG.SectionRank.Native
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

@[expose] def binOf (a : Fin 11 → ZMod 2) : ℕ := ofBits 11 fun j => if h : j < 11 then
  a ⟨j, h⟩ == 1 else false

theorem binOf_lt (a : Fin 11 → ZMod 2) : binOf a < 2 ^ 11 := ofBits_lt _ _

theorem toVecD_binOf (a : Fin 11 → ZMod 2) : toVecD 11 (binOf a) = a := by
  funext j
  rw [binOf, toVecD_ofBits, dite_eq_left j.isLt]
  generalize a j = c
  revert c
  decide

theorem ofFn_eq_map_range {α : Type*} {n : ℕ} (G : ℕ → α) :
    List.ofFn (fun j : Fin n => G j) = (List.range n).map G := by
  rw [List.ofFn_eq_pmap, List.pmap_eq_map]

theorem getElem!_eq_getD' (C : Array ℕ) (j : ℕ) : C[j]! = C[j]?.getD 0 := by
  rw [getElem!_def]
  cases C[j]? <;> rfl

theorem prod_bits_eq (f : ℕ → J)
    (hf : ∀ a b, f (a ^^^ b) = f a * f b) (C : Array ℕ) (a : ℕ) :
    (List.ofFn fun j : Fin 11 => if a.testBit j then f C[j.val]! else 1).prod =
      f (app11 C a) := by
  have hf0 : f 0 = 1 := by
    have := hf 0 0
    rw [Nat.zero_xor] at this
    exact left_eq_mul.mp this
  have key : ∀ (l : List ℕ) (acc : ℕ),
      f (l.foldl (fun acc j => if a.testBit j then acc ^^^ (C[j]?.getD 0) else acc) acc) =
        f acc * (l.map fun j => if a.testBit j then f (C[j]?.getD 0) else 1).prod := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons j l ih =>
      intro acc
      have e : f (if a.testBit j then acc ^^^ (C[j]?.getD 0) else acc) =
          f acc * (if a.testBit j then f (C[j]?.getD 0) else 1) := by
        split_ifs
        · exact hf _ _
        · exact (mul_one _).symm
      rw [List.foldl_cons, ih, e, List.map_cons, List.prod_cons, ← mul_assoc]
  rw [app11, vecMulN, key, hf0, one_mul,
    ofFn_eq_map_range (fun j => if a.testBit j then f C[j]! else 1)]
  refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
  rw [getElem!_eq_getD']

end CFSG.Sporadic.J4Schreier
