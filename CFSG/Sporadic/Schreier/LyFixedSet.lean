
module

public import CFSG.Sporadic.Ly.Setup
public import CFSG.Sporadic.Schreier.LyWords
public import CFSG.Sporadic.Th.TableSpec
public import Certificates.Data.CFSGNative.LySchreier.Check

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier.Native Matrix
open CFSG.Sporadic.Th (wordG)

@[expose] def xPt (n : ℕ) : Fin 8835156 := ⟨n % 8835156, Nat.mod_lt _ (by norm_num)⟩

theorem xPt_of_lt {n : ℕ} (hn : n < 8835156) : xPt n = ⟨n, hn⟩ := Fin.ext (Nat.mod_eq_of_lt hn)

@[expose] def fixedList : List (Fin 8835156) := fixedIdx.toList.map xPt

theorem evalWord_eq_wordG [LySeed]
    (g : ℕ → J) (w : List ℤ) : evalWord g w = wordG (letterVal g) w :=
  rfl

theorem fixedMask_spec (n : ℕ) (xs : Array ℕ) (hxs : ∀ x ∈ xs.toList, x < n) {i : ℕ}
    (hi : i < n) : (fixedMask n xs)[i]! = true ↔ i ∈ xs.toList := by
  have key : ∀ (L : List ℕ) (m : Array Bool), m.size = n → (∀ x ∈ L, x < n) →
      (L.foldl (fun m x => m.set! x true) m).size = n ∧
      ((L.foldl (fun m x => m.set! x true) m)[i]! = true ↔ m[i]! = true ∨ i ∈ L) := by
    intro L
    induction L with
    | nil => intro m hm _; simp [hm]
    | cons x L ih =>
      intro m hm hL
      rw [List.foldl_cons]
      obtain ⟨h1, h2⟩ := ih (m.set! x true) (by simp [hm])
        (fun y hy => hL y (List.mem_cons_of_mem _ hy))
      refine ⟨h1, ?_⟩
      rw [h2, Array.set!_eq_setIfInBounds, getElem!_pos _ i (by simp [hm, hi]),
        getElem!_pos m i (by simp [hm, hi]), Array.getElem_setIfInBounds (by simp [hm, hi])]
      by_cases hxi : x = i
      · subst hxi; simp
      · simp [hxi, Ne.symm hxi, List.mem_cons]
  have := (key xs.toList (Array.replicate n false) (by simp) hxs).2
  rw [fixedMask, ← Array.foldl_toList, this, getElem!_pos _ i (by simp [hi])]
  simp

end CFSG.Sporadic.LySchreier
