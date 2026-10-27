module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.A8Model
import CFSG.RankThree.PartTwo.Sec21.FF84S34K

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA.CatB

@[expose] def a8t : Perm (Fin 8) := swap 6 7

@[expose] def a8ys : List (Perm (Fin 8)) :=
  [swap 0 1 * swap 1 2, swap 3 4 * swap 6 7, swap 0 3 * swap 3 4,
    swap 0 1 * swap 1 5, swap 0 1 * swap 1 3, swap 0 2 * swap 2 3]

theorem sign_a8t : sign a8t = -1 := by
  rw [a8t, sign_swap (by decide)]

theorem centralizer_P0 : ∀ z : Perm (Fin 8), z * a8c = a8c * z → z * a8d = a8d * z →
    ∃ i < 3, ∃ j < 3, (z = a8c ^ i * a8d ^ j ∨ z = a8c ^ i * a8d ^ j * a8t) := by
  refine FF84K.cen_sound a8c a8d a8t _ _ _ ?_ ?_ ?_ FF84K.cen_check
  · decide +kernel
  · decide +kernel
  · decide +kernel

@[expose] def tab (x : Perm (Fin 8)) : List (Fin 8) := List.ofFn fun i => x i

@[expose] def comp (a b : List (Fin 8)) : List (Fin 8) := b.map fun j => a.getD j.val 0

@[expose] def sqT (a : List (Fin 8)) : List (Fin 8) := comp a a

theorem tab_getD (x : Perm (Fin 8)) (j : Fin 8) : (tab x).getD j.val 0 = x j := by
  have hj : (j : ℕ) < (tab x).length := by simp [tab]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  simp only [tab, List.getElem_ofFn]

theorem tab_mul (x y : Perm (Fin 8)) : tab (x * y) = comp (tab x) (tab y) := by
  unfold tab comp
  rw [List.map_ofFn]
  congr 1
  funext i
  exact (tab_getD x (y i)).symm

theorem tab_inj {x y : Perm (Fin 8)} (h : tab x = tab y) : x = y := by
  ext j
  rw [← tab_getD x j, ← tab_getD y j, h]

theorem tab_pow_eight (x : Perm (Fin 8)) : tab (x ^ 8) = sqT (sqT (sqT (tab x))) := by
  have : x ^ 8 = (x * x) * (x * x) * ((x * x) * (x * x)) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [this, tab_mul, tab_mul, tab_mul]
  rfl

theorem mem_perms (x : Perm (Fin 8)) : tab x ∈ (List.finRange 8).permutations' := by
  rw [List.mem_permutations']
  refine (List.perm_ext_iff_of_nodup (List.nodup_ofFn.2 x.injective)
    (List.nodup_finRange 8)).2 fun a => ?_
  rw [List.mem_ofFn]
  simp only [List.mem_finRange, iff_true]
  exact ⟨x.symm a, by simp⟩

theorem ys_sign : ∀ y ∈ a8ys, sign y = 1 := by
  intro y hy
  simp only [a8ys, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Perm.sign_mul, Perm.sign_swap]

theorem ys_comm : ∀ y ∈ a8ys, comp (tab y) (tab a8t) = comp (tab a8t) (tab y) := by
  intro y hy
  rw [← tab_mul, ← tab_mul, FF84K.comm_sound a8t a8ys _ _ (by decide +kernel) (by decide +kernel)
    FF84K.comm_check y hy]

theorem exists_two_elt_table : ∀ l ∈ (List.finRange 8).permutations',
    comp l (tab a8t) = comp (tab a8t) l → sqT (sqT (sqT l)) = tab 1 → l ≠ tab 1 →
      l ≠ tab a8t →
      ∃ y ∈ a8ys, sqT (sqT (sqT (comp l (comp (comp (tab y) l) (tab y⁻¹))))) ≠ tab 1 := by
  intro l hl hc h8 h1 ht
  obtain ⟨x, hx⟩ := FF84K.ofFn_surj l hl
  have hx' : tab x = l := hx
  subst hx'
  obtain ⟨y, hy, hne⟩ := FF84K.key_sound a8t a8ys _ _ (by decide +kernel) (by decide +kernel)
    FF84K.key_check x (tab_inj (by rw [tab_mul, tab_mul]; exact hc))
    (tab_inj (by rw [tab_pow_eight]; exact h8)) (fun e => h1 (by rw [e]))
    (fun e => ht (by rw [e]))
  refine ⟨y, hy, fun e => hne (tab_inj ?_)⟩
  rw [tab_pow_eight, tab_mul, tab_mul, tab_mul]
  exact e

theorem exists_two_elt_product :
    ∀ x : Perm (Fin 8), x * a8t = a8t * x → x ^ 8 = 1 → x ≠ 1 → x ≠ a8t →
      ∃ y ∈ a8ys, sign y = 1 ∧ y * a8t = a8t * y ∧ (x * (y * x * y⁻¹)) ^ 8 ≠ 1 := by
  intro x hc h8 h1 ht
  obtain ⟨y, hy, hne⟩ := exists_two_elt_table (tab x) (mem_perms x)
    (by rw [← tab_mul, ← tab_mul, hc])
    (by rw [← tab_pow_eight, h8])
    (fun h => h1 (tab_inj h)) (fun h => ht (tab_inj h))
  refine ⟨y, hy, ys_sign y hy, tab_inj (by rw [tab_mul, tab_mul]; exact ys_comm y hy), ?_⟩
  intro h
  apply hne
  have h' := congrArg tab h
  rwa [tab_pow_eight, tab_mul, tab_mul, tab_mul] at h'

end CFSG.RankThree.PartTwo.Sec21.FF84
