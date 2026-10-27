module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14ClassNOrth

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.ComponentClassification.OutcomeLocal

theorem s15k_norm_orth_span {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Q : QuadraticForm (ZMod 2) V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ Module.finrank (ZMod 2) V) :
    Submodule.span (ZMod 2) {v : V | Q v = 1} = ⊤ := by
  classical
  haveI : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  by_contra hne
  set S := Submodule.span (ZMod 2) {v : V | Q v = 1} with hS
  set B : LinearMap.BilinForm (ZMod 2) V := QuadraticMap.polarBilin Q with hB
  have hlt : Module.finrank (ZMod 2) S < Module.finrank (ZMod 2) V :=
    Submodule.finrank_lt hne
  have hfr : Module.finrank (ZMod 2) (LinearMap.BilinForm.orthogonal B S) =
      Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) S :=
    LinearMap.BilinForm.finrank_orthogonal hQ S
  have hne' : LinearMap.BilinForm.orthogonal B S ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hfr
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne'
  have hw1 : ∀ v, Q v = 1 → QuadraticMap.polar Q v w = 0 := by
    intro v hv
    have := (LinearMap.BilinForm.mem_orthogonal_iff.1 hw) v (Submodule.subset_span hv)
    simpa [hB, QuadraticMap.polarBilin_apply_apply, LinearMap.BilinForm.IsOrtho] using this
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, QuadraticMap.polar Q x₀ w = 1 := by
    by_contra hcon
    have h0 : ∀ x, QuadraticMap.polar Q x w = 0 := by
      intro x
      rcases zmod2_eq_zero_or_one (QuadraticMap.polar Q x w) with h | h
      · exact h
      · exact absurd ⟨x, h⟩ hcon
    exact hw0 (hQ.2 w (fun x => by simpa [hB, QuadraticMap.polarBilin_apply_apply] using h0 x))
  have hQx₀ : Q x₀ = 0 := by
    rcases zmod2_eq_zero_or_one (Q x₀) with h | h
    · exact h
    · have := hw1 x₀ h
      rw [hx₀] at this
      exact absurd this one_ne_zero
  have hT : ∀ z, QuadraticMap.polar Q z w = 0 → Q z = QuadraticMap.polar Q x₀ z := by
    intro z hz
    have h1 : Q (x₀ + z) = 0 := by
      rcases zmod2_eq_zero_or_one (Q (x₀ + z)) with h | h
      · exact h
      · have := hw1 _ h
        rw [QuadraticMap.polar_add_left, hx₀, hz] at this
        exact absurd this (by decide)
    have h2 := i28_14_N_Q_add Q x₀ z
    rw [h1, hQx₀] at h2
    generalize Q z = a at h2 ⊢
    generalize QuadraticMap.polar Q x₀ z = b at h2 ⊢
    revert a b
    decide
  have hiso : ∀ z z', QuadraticMap.polar Q z w = 0 → QuadraticMap.polar Q z' w = 0 →
      QuadraticMap.polar Q z z' = 0 := by
    intro z z' hz hz'
    have h1 := hT (z + z') (by rw [QuadraticMap.polar_add_left, hz, hz', add_zero])
    have h2 := i28_14_N_Q_add Q z z'
    have h3 : QuadraticMap.polar Q x₀ (z + z') =
        QuadraticMap.polar Q x₀ (z + z') + QuadraticMap.polar Q z z' :=
      calc QuadraticMap.polar Q x₀ (z + z') = Q (z + z') := h1.symm
        _ = Q z + Q z' + QuadraticMap.polar Q z z' := h2
        _ = QuadraticMap.polar Q x₀ z + QuadraticMap.polar Q x₀ z' +
            QuadraticMap.polar Q z z' := by rw [hT z hz, hT z' hz']
        _ = QuadraticMap.polar Q x₀ (z + z') + QuadraticMap.polar Q z z' := by
            rw [QuadraticMap.polar_add_right]
    simpa using h3
  let φ : V →ₗ[ZMod 2] ZMod 2 := B.flip w
  have hφ : ∀ z, φ z = QuadraticMap.polar Q z w := fun z => by
    simp [φ, hB, QuadraticMap.polarBilin_apply_apply]
  have hTle : LinearMap.ker φ ≤ LinearMap.BilinForm.orthogonal B (LinearMap.ker φ) := by
    intro z hz
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    have := hiso n z (by rw [← hφ]; exact hn) (by rw [← hφ]; exact hz)
    simpa [hB, QuadraticMap.polarBilin_apply_apply, LinearMap.BilinForm.IsOrtho] using this
  have hrange : LinearMap.range φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · exact ⟨0, map_zero φ⟩
    · exact ⟨x₀, by rw [hφ, hx₀]⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  rw [hrange, finrank_top, Module.finrank_self] at hrn
  have hle := Submodule.finrank_mono hTle
  have hfr2 := LinearMap.BilinForm.finrank_orthogonal hQ (LinearMap.ker φ)
  omega

theorem s15k_norm_orth_abs {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Q : QuadraticForm (ZMod 2) V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ Module.finrank (ZMod 2) V) {g : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hg : ∀ x ∈ i28_14_N_OG Q, g * x * g⁻¹ ∈ i28_14_N_OG Q) : g ∈ i28_14_N_OG Q := by
  have hW := s15k_norm_orth_span Q hQ h3
  have key := fun {v : V} (hv : Q v = 1) => i28_14_N_orth_key hQ hg hv
  have hB : ∀ x y, QuadraticMap.polar Q ((g : V →ₗ[ZMod 2] V) x) ((g : V →ₗ[ZMod 2] V) y) =
      QuadraticMap.polar Q x y := by
    intro x y
    have hx : x ∈ Submodule.span (ZMod 2) {v : V | Q v = 1} := hW ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem v hv => exact (key hv).2 y
    | zero =>
      rw [map_zero, QuadraticMap.polar_zero_left, QuadraticMap.polar_zero_left]
    | add x x' _ _ h1 h2 =>
      rw [map_add, QuadraticMap.polar_add_left, QuadraticMap.polar_add_left, h1, h2]
    | smul c x _ h1 =>
      rw [map_smul, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left, h1]
  refine i28_14_N_mem_OG.mpr fun x => ?_
  have hx : x ∈ Submodule.span (ZMod 2) {v : V | Q v = 1} := hW ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem v hv => rw [(key hv).1, hv]
  | zero => rw [map_zero, QuadraticMap.map_zero]
  | add x y _ _ h1 h2 =>
    rw [map_add, i28_14_N_Q_add, i28_14_N_Q_add, h1, h2, hB]
  | smul c x _ h1 =>
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · rw [zero_smul, map_zero, QuadraticMap.map_zero]
    · rw [one_smul]
      exact h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
