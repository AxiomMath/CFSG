module

public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameInd

public section

open Polynomial Module Matrix

namespace CFSG.StandardType

namespace SpNS

section Decomp

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {B : LinearMap.BilinForm K V} {D : Type} [AddCommGroup D] [Module K D] {c : D →ₗ[K] D}
  {ι κ : Type} [Fintype ι] [DecidableEq ι] {Φ : ((ι → D) × (κ → K)) ≃ₗ[K] V}

@[expose] def frameBlockForm (B : LinearMap.BilinForm K V) (Φ : ((ι → D) × (κ → K)) ≃ₗ[K] V)
    (i : ι) : LinearMap.BilinForm K D :=
  (B.comp (Φ.toLinearMap ∘ₗ LinearMap.inl K (ι → D) (κ → K) ∘ₗ LinearMap.single K (fun _ => D) i)
    (Φ.toLinearMap ∘ₗ LinearMap.inl K (ι → D) (κ → K) ∘ₗ LinearMap.single K (fun _ => D) i))

omit [Fintype ι] in
theorem frameBlockForm_apply (i : ι) (u v : D) :
    frameBlockForm B Φ i u v = B (Φ (Pi.single i u, 0)) (Φ (Pi.single i v, 0)) := rfl

omit [Fintype ι] in
theorem frame_orth_single (hc : ∀ u : D, ∃ u₀, c u₀ - u₀ = u)
    (hΦB : ∀ (k : ι → ℕ) (d d' : ι → D) (w w' : κ → K),
      B (Φ (fun i => (c ^ k i) (d i), w)) (Φ (fun i => (c ^ k i) (d' i), w')) =
        B (Φ (d, w)) (Φ (d', w')))
    (i : ι) (u : D) {d : ι → D} (w : κ → K) (hd : d i = 0) :
    B (Φ (Pi.single i u, 0)) (Φ (d, w)) = 0 := by
  obtain ⟨u₀, rfl⟩ := hc u
  have h1 := hΦB (Pi.single i 1) (Pi.single i u₀) d 0 w
  have e1 : (fun j => (c ^ (Pi.single i 1 : ι → ℕ) j) ((Pi.single i u₀ : ι → D) j)) =
      Pi.single i (c u₀) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.single_eq_of_ne hj]
  have e2 : (fun j => (c ^ (Pi.single i 1 : ι → ℕ) j) (d j)) = d := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [hd]
    · simp [Pi.single_eq_of_ne hj]
  rw [e1, e2] at h1
  have e3 : ((Pi.single i (c u₀ - u₀) : ι → D), (0 : κ → K)) =
      (Pi.single i (c u₀), 0) - (Pi.single i u₀, 0) := by
    rw [Prod.mk_sub_mk, sub_zero, ← Pi.single_sub]
  rw [e3, map_sub, LinearMap.map_sub₂, h1, sub_self]

theorem frame_bilin_eq (hrefl : B.IsRefl) (hc : ∀ u : D, ∃ u₀, c u₀ - u₀ = u)
    (hΦB : ∀ (k : ι → ℕ) (d d' : ι → D) (w w' : κ → K),
      B (Φ (fun i => (c ^ k i) (d i), w)) (Φ (fun i => (c ^ k i) (d' i), w')) =
        B (Φ (d, w)) (Φ (d', w')))
    (d d' : ι → D) (w w' : κ → K) :
    B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, frameBlockForm B Φ i (d i) (d' i) + B (Φ (0, w)) (Φ (0, w')) := by
  have hsplit : ∀ (d : ι → D) (w : κ → K),
      Φ (d, w) = ∑ i, Φ (Pi.single i (d i), 0) + Φ (0, w) := by
    intro d w
    rw [← map_sum, ← map_add]
    congr 1
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_add, Prod.fst_sum, Finset.univ_sum_single, add_zero]
    · rw [Prod.snd_add, Prod.snd_sum]
      simp
  have hblock : ∀ i (u : D), B (Φ (Pi.single i u, 0)) (Φ (d', w')) =
      frameBlockForm B Φ i u (d' i) := by
    intro i u
    have e : Φ (d', w') = Φ (Pi.single i (d' i), 0) + Φ (d' - Pi.single i (d' i), w') := by
      rw [← map_add]
      congr 1
      rw [Prod.mk_add_mk, add_sub_cancel, zero_add]
    rw [e, map_add, frame_orth_single hc hΦB i u w' (by simp), add_zero]
    rfl
  have hzero : B (Φ (0, w)) (Φ (d', w')) = B (Φ (0, w)) (Φ (0, w')) := by
    rw [hsplit d' w', map_add, map_sum]
    have h0 : ∀ j, B (Φ (0, w)) (Φ (Pi.single j (d' j), 0)) = 0 := fun j =>
      hrefl _ _ (frame_orth_single hc hΦB j (d' j) w (Pi.zero_apply j))
    simp only [h0, Finset.sum_const_zero, zero_add]
  rw [hsplit d w, LinearMap.map_add₂, LinearMap.map_sum₂, hzero]
  congr 1
  exact Finset.sum_congr rfl fun i _ => hblock i (d i)

end Decomp

section Plane

variable {K : Type} [Field K] {D : Type} [AddCommGroup D] [Module K D]

theorem transpose_mul_mul_eq_det_smul (M Γ : Matrix (Fin 2) (Fin 2) K) (h00 : Γ 0 0 = 0)
    (h11 : Γ 1 1 = 0) (h10 : Γ 1 0 = -Γ 0 1) : Mᵀ * Γ * M = M.det • Γ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, h00, h11, h10] <;> ring

theorem bilin_apply_det (b : Basis (Fin 2) K D) {β : LinearMap.BilinForm K D} (hβ : β.IsAlt)
    (T : D →ₗ[K] D) (u v : D) : β (T u) (T v) = LinearMap.det T * β u v := by
  have h : β.comp T T = LinearMap.det T • β := by
    apply (LinearMap.BilinForm.toMatrix b).injective
    rw [LinearMap.BilinForm.toMatrix_comp b b, map_smul, ← LinearMap.det_toMatrix b]
    refine transpose_mul_mul_eq_det_smul _ _ ?_ ?_ ?_
    · rw [LinearMap.BilinForm.toMatrix_apply]
      exact hβ.self_eq_zero _
    · rw [LinearMap.BilinForm.toMatrix_apply]
      exact hβ.self_eq_zero _
    · rw [LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.toMatrix_apply]
      exact (hβ.neg_eq _ _).symm
  have h1 := congrArg (fun F : LinearMap.BilinForm K D => F u v) h
  simpa using h1

theorem alt_two_eq_smul (b : Basis (Fin 2) K D) {β β' : LinearMap.BilinForm K D}
    (hβ : β.IsAlt) (hβ' : β'.IsAlt) (h0 : β' (b 0) (b 1) ≠ 0) :
    β = (β (b 0) (b 1) / β' (b 0) (b 1)) • β' := by
  refine LinearMap.BilinForm.ext_basis b fun i j => ?_
  simp only [LinearMap.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j
  · simp [hβ.self_eq_zero, hβ'.self_eq_zero]
  · simp only [Fin.zero_eta, Fin.mk_one]
    field_simp
  · simp only [Fin.mk_one, Fin.zero_eta]
    rw [← hβ.neg_eq (b 0) (b 1), ← hβ'.neg_eq (b 0) (b 1)]
    field_simp
  · simp [hβ.self_eq_zero, hβ'.self_eq_zero]

theorem alt_two_ne_zero (b : Basis (Fin 2) K D) {β : LinearMap.BilinForm K D} (hβ : β.IsAlt)
    (hnd : ∀ u, (∀ v, β u v = 0) → u = 0) : β (b 0) (b 1) ≠ 0 := by
  intro h0
  apply b.ne_zero 0
  refine hnd _ fun v => ?_
  have hv := b.sum_repr v
  rw [← hv, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, smul_eq_mul]
  fin_cases j
  · simp [hβ.self_eq_zero]
  · simp [h0]

end Plane

end SpNS

end CFSG.StandardType
