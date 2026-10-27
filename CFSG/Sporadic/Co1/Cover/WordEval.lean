module

public import CFSG.Sporadic.HS.SmallF2Spec
public import Certificates.Data.CFSGNative.Co1.CoverCheck

public section

namespace CFSG.Sporadic.Co1.Cover

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.CoverNative Matrix

@[expose] def letterElt {M : Type*} [Group M] (g₀ g₁ : M) (l : ℕ × Bool) : M :=
  if l.1 = 0 then (if l.2 then g₀ else g₀⁻¹) else (if l.2 then g₁ else g₁⁻¹)

section Words

variable {M : Type*} [Group M] {d : ℕ} (φ : M →* Matrix (Fin d) (Fin d) (ZMod 2)) (g₀ g₁ : M)
  (r0 r1 r0i r1i : Array ℕ) (h0 : φ g₀ = rowsMatrix d r0) (h1 : φ g₁ = rowsMatrix d r1)
  (h0i : φ g₀⁻¹ = rowsMatrix d r0i) (h1i : φ g₁⁻¹ = rowsMatrix d r1i)

include h0 h1 h0i h1i in
theorem matrix_letterElt (l : ℕ × Bool) :
    φ (letterElt g₀ g₁ l) = rowsMatrix d (letterRows r0 r1 r0i r1i l) := by
  unfold letterElt letterRows
  by_cases h : l.1 = 0 <;> by_cases hs : l.2 <;> simp [h, hs, h0, h1, h0i, h1i]

include h0 h1 h0i h1i in
theorem word_matrix (w : List (ℕ × Bool)) :
    φ ((w.map (letterElt g₀ g₁)).prod) = rowsMatrix d (wordRowsAB d r0 r1 r0i r1i w) := by
  have key : ∀ (w : List (ℕ × Bool)) (acc : Array ℕ),
      rowsMatrix d (w.foldl (fun acc l => mulRows d acc (letterRows r0 r1 r0i r1i l)) acc) =
        rowsMatrix d acc * φ ((w.map (letterElt g₀ g₁)).prod) := by
    intro w
    induction w with
    | nil => intro acc; simp
    | cons l w ih =>
      intro acc
      rw [List.foldl_cons, ih, rowsMatrix_mulRows,
        ← matrix_letterElt φ g₀ g₁ r0 r1 r0i r1i h0 h1 h0i h1i l, List.map_cons, List.prod_cons,
        map_mul, Matrix.mul_assoc]
  rw [wordRowsAB, key, rowsMatrix_idRows, Matrix.one_mul]

end Words

end CFSG.Sporadic.Co1.Cover
