
module

public import CFSG.Sporadic.Schreier.J4SOrbitsBase

public import CFSG.Sporadic.Schreier.J4SConj
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

section BFS

variable {gens : Array (Array ℕ)} {s n : ℕ} {B : Array ℕ × Array ℕ × Array ℕ}

end BFS

theorem xy_gens :
    ∀ g < (#[xColumns, yColumns] : Array (Array ℕ)).size,
    ∃ k ∈ K, ∀ a, k * η a * k⁻¹ = η (app11 (#[xColumns, yColumns] : Array (Array ℕ))[g]! a) := by
  intro g hg
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hg
  obtain rfl | rfl : g = 0 ∨ g = 1 := by omega
  · exact ⟨x, x_mem_K, fun a => x_conj_η a⟩
  · exact ⟨y, y_mem_K, fun a => y_conj_η a⟩

theorem word_conj_η_cols (w : List ℤ) (a : ℕ) :
    signedWord x y w * η a * (signedWord x y w)⁻¹ = η (app11 (wordCols w) a) := by
  refine conj_η_of_cols (fun j => ?_) a
  rw [← η_two_pow, word_conj_η]
  have e : (wordCols w)[j.val]! = app11W w (2 ^ j.val) := by
    rw [wordCols, getElem!_pos _ _ (by simp), Array.getElem_ofFn]
  rw [e]

theorem sgen_conj
    (m : ℕ) (a : ℕ) : sgen m * η a * (sgen m)⁻¹ = η (app11 (sCols m) a) :=
  word_conj_η_cols _ a

end CFSG.Sporadic.J4Schreier
