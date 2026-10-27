module

public import CFSG.Quasithin.EmptyFaithful.ModCModel7Defs

public section

namespace CFSG.Quasithin.ModC

open Equiv Equiv.Perm CFSG.Quasithin.G6

namespace M7

set_option maxRecDepth 100000

theorem fixed_vectors : ∀ y : PermMod 7, (∑ i, Multiplicative.toAdd y i = 0) →
    (∀ s ∈ gens, permAct 7 s y = y) → y = 1 ∨ y = a ∨ y = b ∨ y = x := by
  decide +kernel

theorem ab_eq : a * x = b := by decide +kernel

theorem x_core : ∑ i, Multiplicative.toAdd x i = 0 := by decide +kernel

theorem x_ne_one : x ≠ 1 := by decide +kernel

theorem x_ne_a : x ≠ a := by decide +kernel

theorem x_fix : ∀ s ∈ gens, permAct 7 s x = x := by decide +kernel

theorem wt_count : (Finset.univ.filter fun u : PermMod 7 =>
    (∑ i, Multiplicative.toAdd u i = 0) ∧ wt u = wt x).card ≤ 7 := by decide +kernel

theorem pigeon_list : ∃ L : List (Perm (Fin 7)), L.length = 8 ∧ (∀ σ ∈ L, sign σ = 1) ∧
    (L.map (fun σ => permAct 7 σ b)).Nodup :=
  ⟨[1, swap 4 0 * swap 5 1, swap 4 0 * swap 5 2, swap 4 0 * swap 5 3, swap 4 1 * swap 5 2,
    swap 4 1 * swap 5 3, swap 4 2 * swap 5 3, swap 4 0 * swap 5 4],
    by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem exists_jj : ∃ j j' : Perm (Fin 7), sign j = 1 ∧ sign j' = 1 ∧ permAct 7 j x = x ∧
    permAct 7 j a ≠ a ∧ permAct 7 j' x = x ∧ ∀ v ∈ [w, a * w],
      permAct 7 j' v ≠ v ∧ permAct 7 j' v ≠ a * v ∧ permAct 7 j' v ≠ a :=
  ⟨swap 3 4 * swap 4 5, swap 1 2 * swap 2 4, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

end M7

end CFSG.Quasithin.ModC
