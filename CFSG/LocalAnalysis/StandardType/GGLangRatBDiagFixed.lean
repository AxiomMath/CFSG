module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.StandardType.LangRat

open scoped MatrixGroups

private theorem langRatB_dunit_prod {L : Type} [Field L] {ν : ℕ} {x y : Fin ν} (hxy : x ≠ y)
    (u : Lˣ) : ∏ j : Fin ν, (if j = x then u else if j = y then u⁻¹ else 1) = 1 := by
  rw [Fintype.prod_eq_mul x y hxy]
  · simp [hxy.symm]
  · intro j hj
    simp [hj.1, hj.2]

theorem langRatB_diag_fixed {L : Type} [Field L] {ν : ℕ} (Φ' : SL(ν, L) ≃* SL(ν, L))
    (a b : ℕ → Fin ν) (hab : ∀ t, a t ≠ b t) (v : ℕ → Lˣ) {r : ℕ}
    (har : a r = a 0) (hbr : b r = b 0) (hvr : v r = v 0)
    (hΦ' : ∀ (t : ℕ) (X : SL(ν, L)),
      (X : Matrix (Fin ν) (Fin ν) L) = Matrix.diagonal (fun j =>
        if j = a t then (v t : L) else if j = b t then (((v t)⁻¹ : Lˣ) : L) else 1) →
      ((Φ' X : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) = Matrix.diagonal (fun j =>
        if j = a (t + 1) then (v (t + 1) : L)
          else if j = b (t + 1) then (((v (t + 1))⁻¹ : Lˣ) : L) else 1))
    {K T : Type} [Group K] [CommGroup T] (Θ : SL(ν, L) →* K) (ε : T →* K) (G : ℕ → T)
    (hG : ∀ (t : ℕ) (X : SL(ν, L)),
      (X : Matrix (Fin ν) (Fin ν) L) = Matrix.diagonal (fun j =>
        if j = a t then (v t : L) else if j = b t then (((v t)⁻¹ : Lˣ) : L) else 1) →
      ε (G t) = Θ X) :
    ∃ D : SL(ν, L), Φ' D = D ∧ Θ D = ε (∏ t ∈ Finset.range r, G t) := by
  let dU : ℕ → Fin ν → Lˣ := fun t j => if j = a t then v t else if j = b t then (v t)⁻¹ else 1
  have hdU : ∀ t, ∏ j, dU t j = 1 := fun t => langRatB_dunit_prod (hab t) (v t)
  have hdUc : ∀ t j, ((dU t j : Lˣ) : L) =
      if j = a t then (v t : L) else if j = b t then (((v t)⁻¹ : Lˣ) : L) else 1 := by
    intro t j
    simp only [dU]
    split_ifs <;> simp
  have hmk : ∀ f : Fin ν → Lˣ, ∏ j, f j = 1 →
      ∃ X : SL(ν, L), (X : Matrix (Fin ν) (Fin ν) L) = Matrix.diagonal (fun j => (f j : L)) := by
    intro f hf
    refine ⟨⟨Matrix.diagonal (fun j => (f j : L)), ?_⟩, rfl⟩
    rw [Matrix.det_diagonal]
    have h := congrArg (fun u : Lˣ => (u : L)) hf
    simpa [Units.coe_prod] using h
  have key : ∀ n : ℕ, ∃ D : SL(ν, L),
      (D : Matrix (Fin ν) (Fin ν) L) =
        Matrix.diagonal (fun j => ((∏ t ∈ Finset.range n, dU t) j : L)) ∧
      Θ D = ε (∏ t ∈ Finset.range n, G t) ∧
      ((Φ' D : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
        Matrix.diagonal (fun j => ((∏ t ∈ Finset.range n, dU (t + 1)) j : L)) := by
    intro n
    induction n with
    | zero => exact ⟨1, by simp, by simp, by simp⟩
    | succ n ih =>
      obtain ⟨D, hD1, hD2, hD3⟩ := ih
      obtain ⟨X, hX⟩ := hmk (dU n) (hdU n)
      have hX' : (X : Matrix (Fin ν) (Fin ν) L) = Matrix.diagonal (fun j =>
          if j = a n then (v n : L) else if j = b n then (((v n)⁻¹ : Lˣ) : L) else 1) := by
        rw [hX]
        congr 1
        funext j
        exact hdUc n j
      have hΦX := hΦ' n X hX'
      have hΦX' : ((Φ' X : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
          Matrix.diagonal (fun j => ((dU (n + 1) j : Lˣ) : L)) := by
        rw [hΦX]
        congr 1
        funext j
        exact (hdUc (n + 1) j).symm
      refine ⟨D * X, ?_, ?_, ?_⟩
      · rw [Matrix.SpecialLinearGroup.coe_mul, hD1, hX, Matrix.diagonal_mul_diagonal,
          Finset.prod_range_succ]
        congr 1
      · rw [map_mul, hD2, Finset.prod_range_succ, map_mul, hG n X hX']
      · rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, hD3, hΦX', Matrix.diagonal_mul_diagonal,
          Finset.prod_range_succ]
        congr 1
  have hshift : ∏ t ∈ Finset.range r, dU (t + 1) = ∏ t ∈ Finset.range r, dU t := by
    have h1 : ∏ t ∈ Finset.range (r + 1), dU t =
        (∏ t ∈ Finset.range r, dU (t + 1)) * dU 0 := Finset.prod_range_succ' _ _
    have h2 : ∏ t ∈ Finset.range (r + 1), dU t = (∏ t ∈ Finset.range r, dU t) * dU r :=
      Finset.prod_range_succ _ _
    have h3 : dU r = dU 0 := by
      funext j
      simp only [dU, har, hbr, hvr]
    rw [h3] at h2
    exact mul_right_cancel (h1.symm.trans h2)
  obtain ⟨D, hD1, hD2, hD3⟩ := key r
  refine ⟨D, Subtype.ext ?_, hD2⟩
  rw [hD3, hD1, hshift]

end CFSG.StandardType.LangRat
