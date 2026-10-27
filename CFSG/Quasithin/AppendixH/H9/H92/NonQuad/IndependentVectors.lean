module

public import CFSG.Quasithin.AppendixH.H9.H92.NonQuad.OrbitSubspace
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {n : ℕ}

structure NilPair (A B : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop where
  sq_left : A * A = 0
  sq_right : B * B = 0
  comm : A * B = B * A

namespace NilPair

variable {A B : Matrix (Fin n) (Fin n) (ZMod 2)} (hp : NilPair A B) (v : Fin n → ZMod 2)

include hp

theorem left_mulVec_left : A *ᵥ (A *ᵥ v) = 0 := by
  rw [Matrix.mulVec_mulVec, hp.sq_left, Matrix.zero_mulVec]

theorem right_mulVec_right : B *ᵥ (B *ᵥ v) = 0 := by
  rw [Matrix.mulVec_mulVec, hp.sq_right, Matrix.zero_mulVec]

theorem right_mulVec_left : B *ᵥ (A *ᵥ v) = (A * B) *ᵥ v := by
  rw [Matrix.mulVec_mulVec, ← hp.comm]

theorem left_mulVec_right : A *ᵥ (B *ᵥ v) = (A * B) *ᵥ v := by
  rw [Matrix.mulVec_mulVec]

theorem left_mulVec_prod : A *ᵥ ((A * B) *ᵥ v) = 0 := by
  rw [Matrix.mulVec_mulVec, ← mul_assoc, hp.sq_left, zero_mul, Matrix.zero_mulVec]

theorem right_mulVec_prod : B *ᵥ ((A * B) *ᵥ v) = 0 := by
  rw [Matrix.mulVec_mulVec, ← mul_assoc, ← hp.comm, mul_assoc, hp.sq_right, mul_zero,
    Matrix.zero_mulVec]

variable {v}

theorem independent (hy : (A * B) *ᵥ v ≠ 0) {a b c : ZMod 2}
    (h : a • (A *ᵥ v) + b • (B *ᵥ v) + c • ((A * B) *ᵥ v) = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hA := congrArg (A *ᵥ ·) h
  have hB := congrArg (B *ᵥ ·) h
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_zero, hp.left_mulVec_left v,
    hp.left_mulVec_right v, hp.left_mulVec_prod v, smul_zero, zero_add, add_zero] at hA
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_zero, hp.right_mulVec_left v,
    hp.right_mulVec_right v, hp.right_mulVec_prod v, smul_zero, zero_add, add_zero] at hB
  have hb : b = 0 := (smul_eq_zero.mp hA).resolve_right hy
  have ha : a = 0 := (smul_eq_zero.mp hB).resolve_right hy
  subst ha hb
  simp only [zero_smul, zero_add] at h
  exact ⟨rfl, rfl, (smul_eq_zero.mp h).resolve_right hy⟩

theorem linearIndependent_three (hy : (A * B) *ᵥ v ≠ 0) :
    LinearIndependent (ZMod 2) ![A *ᵥ v, B *ᵥ v, (A * B) *ᵥ v] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at hc
  obtain ⟨h0, h1, h2⟩ := hp.independent hy hc
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

end NilPair

variable {E : Subgroup (GL (Fin n) (ZMod 2))}
  {𝒩 : Submodule (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2))} {v : Fin n → ZMod 2}
  {A B : Matrix (Fin n) (Fin n) (ZMod 2)}

private theorem span_three_le_nilOrbitSpace (h : SubOneCover E 𝒩) (hA : A ∈ 𝒩) (hB : B ∈ 𝒩) :
    Submodule.span (ZMod 2) (Set.range ![A *ᵥ v, B *ᵥ v, (A * B) *ᵥ v]) ≤ nilOrbitSpace 𝒩 v := by
  refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i => ?_)
  fin_cases i
  · exact mulVec_mem_nilOrbitSpace hA
  · exact mulVec_mem_nilOrbitSpace hB
  · exact mulVec_mem_nilOrbitSpace (h.mul_mem A hA B hB)

theorem three_le_finrank_nilOrbitSpace (h : SubOneCover E 𝒩) (hp : NilPair A B) (hA : A ∈ 𝒩)
    (hB : B ∈ 𝒩) (hy : (A * B) *ᵥ v ≠ 0) :
    3 ≤ Module.finrank (ZMod 2) (nilOrbitSpace 𝒩 v) := by
  have h1 := finrank_span_eq_card (hp.linearIndependent_three hy)
  have h2 := Submodule.finrank_mono (span_three_le_nilOrbitSpace h hA hB (v := v))
  rw [h1] at h2
  simpa using h2

theorem nilOrbitSpace_eq_span_of_finrank_eq_three (h : SubOneCover E 𝒩) (hp : NilPair A B)
    (hA : A ∈ 𝒩) (hB : B ∈ 𝒩) (hy : (A * B) *ᵥ v ≠ 0)
    (hS : Module.finrank (ZMod 2) (nilOrbitSpace 𝒩 v) = 3) :
    nilOrbitSpace 𝒩 v = Submodule.span (ZMod 2) (Set.range ![A *ᵥ v, B *ᵥ v, (A * B) *ᵥ v]) := by
  refine (Submodule.eq_of_le_of_finrank_eq (span_three_le_nilOrbitSpace h hA hB) ?_).symm
  rw [finrank_span_eq_card (hp.linearIndependent_three hy), hS]
  simp

theorem mem_span_prod_of_mulVec_eq_zero (h : SubOneCover E 𝒩) (hp : NilPair A B) (hA : A ∈ 𝒩)
    (hB : B ∈ 𝒩) (hy : (A * B) *ᵥ v ≠ 0) (hS : Module.finrank (ZMod 2) (nilOrbitSpace 𝒩 v) = 3)
    {w : Fin n → ZMod 2} (hw : w ∈ nilOrbitSpan 𝒩 v) (hAw : A *ᵥ w = 0) (hBw : B *ᵥ w = 0) :
    w ∈ Submodule.span (ZMod 2) {(A * B) *ᵥ v} := by
  obtain ⟨s, hs, c, rfl⟩ := mem_nilOrbitSpan.mp hw
  rw [nilOrbitSpace_eq_span_of_finrank_eq_three h hp hA hB hy hS,
    Submodule.mem_span_range_iff_exists_fun] at hs
  obtain ⟨f, rfl⟩ := hs
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.mulVec_add,
    Matrix.mulVec_smul, hp.left_mulVec_left v,
    hp.left_mulVec_right v, hp.left_mulVec_prod v, hp.right_mulVec_left v,
    hp.right_mulVec_right v, hp.right_mulVec_prod v, smul_zero, zero_add, add_zero] at hAw hBw
  have hAw' : c • (A *ᵥ v) + (0 : ZMod 2) • (B *ᵥ v) + f 1 • ((A * B) *ᵥ v) = 0 := by
    rw [zero_smul, add_zero, add_comm]; exact hAw
  have hBw' : (0 : ZMod 2) • (A *ᵥ v) + c • (B *ᵥ v) + f 0 • ((A * B) *ᵥ v) = 0 := by
    rw [zero_smul, zero_add, add_comm]; exact hBw
  obtain ⟨hc, -, hf1⟩ := hp.independent hy hAw'
  obtain ⟨-, -, hf0⟩ := hp.independent hy hBw'
  refine Submodule.mem_span_singleton.mpr ⟨f 2, ?_⟩
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, hc, hf0, hf1, zero_smul, zero_add, add_zero]

end CFSG.ASVolI.ChH
