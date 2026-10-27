module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import CFSG.Mathlib.FieldTheory.Finite.QuadraticZeroMulti
import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.POmegaOuter

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private lemma polar_scale_data {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate)
    (h2 : (2 : K) ≠ 0) {X : V →ₗ[K] V} {μ α : K} (hμ : ∀ v, Q (X v) = μ * Q v)
    (hX2 : ∀ v, X (X v) = α • v) (hα : α ≠ 0) {v₀ : V} (hv₀ : v₀ ≠ 0) :
    (∀ u w, polar Q (X u) w = (μ / α) * polar Q u (X w)) ∧
    (μ / α) * (μ / α) = 1 ∧ ((μ / α = -1) → ∀ v, polar Q v (X v) = 0) := by
  have hpolar : ∀ u w, polar Q (X u) (X w) = μ * polar Q u w := by
    intro u w
    rw [polar, polar, ← map_add, hμ, hμ, hμ]
    ring
  have hscale : ∀ u w, polar Q (X u) w = (μ / α) * polar Q u (X w) := by
    intro u w
    have hw : w = α⁻¹ • X (X w) := by rw [hX2 w, inv_smul_smul₀ hα]
    conv_lhs => rw [hw]
    rw [polar_smul_right, hpolar u (X w)]
    simp only [smul_eq_mul]
    field_simp
  refine ⟨hscale, ?_, ?_⟩
  · set c : K := μ / α with hc
    have h1 : ∀ u w, polar Q u w = (c * c) * polar Q u w := by
      intro u w
      have h := hscale (X u) w
      rw [hX2 u, hscale u (X w), hX2 w, polar_smul_left, polar_smul_right] at h
      simp only [smul_eq_mul] at h
      have h' : α * polar Q u w = α * ((c * c) * polar Q u w) := by
        rw [h]; ring
      exact mul_left_cancel₀ hα h'
    obtain ⟨w, hw⟩ := exists_polar_ne_zero hQ hv₀
    have h4 := h1 v₀ w
    have h5 : (1 - c * c) * polar Q v₀ w = 0 := by
      rw [sub_mul, one_mul]
      exact sub_eq_zero.mpr h4
    have h6 : 1 - c * c = 0 := (mul_eq_zero.mp h5).resolve_right hw
    linear_combination -h6
  · intro hc v
    have h := hscale v v
    rw [polar_comm Q (X v) v, hc, neg_one_mul] at h
    have hzero : (2 : K) * polar Q v (X v) = 0 := by linear_combination h
    exact (mul_eq_zero.mp hzero).resolve_left h2

theorem exists_stable_singular_of_similitudes {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) {A B : V →ₗ[K] V} {μA μB α β ε : K}
    (hμA : ∀ v, Q (A v) = μA * Q v) (hμB : ∀ v, Q (B v) = μB * Q v)
    (hA2 : ∀ v, A (A v) = α • v) (hB2 : ∀ v, B (B v) = β • v) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hAB : ∀ v, A (B v) = ε • B (A v))
    (hdim : 9 ≤ Module.finrank K V ∨ (7 ≤ Module.finrank K V ∧
      ¬ ((∀ u w, polar Q (A u) w = polar Q u (A w)) ∧
        (∀ u w, polar Q (B u) w = polar Q u (B w)) ∧ ∀ v, A (B v) = B (A v)))) :
    ∃ W : Submodule K V, W ≠ ⊥ ∧ (∀ x ∈ W, Q x = 0) ∧ (∀ x ∈ W, A x ∈ W) ∧
      ∀ x ∈ W, B x ∈ W := by
  have hrank : 0 < Module.finrank K V := by
    rcases hdim with h | ⟨h, _⟩ <;> omega
  obtain ⟨v₀, hv₀⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hrank
  have hA_inj : Function.Injective A := by
    intro x y hxy
    have h : A (A x) = A (A y) := by rw [hxy]
    rw [hA2 x, hA2 y] at h
    exact smul_right_injective V hα h
  have hε2 : ε * ε = 1 := by
    have e1 : (β * α) • v₀ = ε • A (B (A (B v₀))) := by
      have h := congrArg A (hAB (B v₀))
      rw [hB2 v₀] at h
      simp only [map_smul] at h
      rw [hA2 v₀, smul_smul] at h
      exact h
    have e2 : A (B (A (B v₀))) = (ε * α * β) • v₀ := by
      have h := hAB (A (B v₀))
      rw [hA2 (B v₀)] at h
      simp only [map_smul] at h
      rw [hB2 v₀] at h
      simp only [smul_smul] at h
      rw [← mul_assoc] at h
      exact h
    have h := e1
    rw [e2, smul_smul] at h
    have hc : β * α = ε * (ε * α * β) := smul_left_injective K hv₀ h
    have hab : α * β ≠ 0 := mul_ne_zero hα hβ
    have h' : 1 * (α * β) = (ε * ε) * (α * β) := by
      rw [one_mul]
      linear_combination hc
    exact (mul_right_cancel₀ hab h').symm
  have hε : ε ≠ 0 := by
    intro h
    rw [h, mul_zero] at hε2
    exact zero_ne_one hε2
  have hεinv : ε⁻¹ = ε := inv_eq_of_mul_eq_one_left hε2
  have hBA : ∀ v, B (A v) = ε • A (B v) := by
    intro v
    have h := hAB v
    calc B (A v) = ε⁻¹ • (ε • B (A v)) := by rw [smul_smul, inv_mul_cancel₀ hε, one_smul]
      _ = ε⁻¹ • A (B v) := by rw [← h]
      _ = ε • A (B v) := by rw [hεinv]
  have hBAB : ∀ v, B (A (B v)) = (ε * β) • A v := by
    intro v
    have h := hAB (B v)
    rw [hB2 v, map_smul] at h
    calc B (A (B v)) = ε⁻¹ • (ε • B (A (B v))) := by rw [smul_smul, inv_mul_cancel₀ hε, one_smul]
      _ = ε⁻¹ • (β • A v) := by rw [← h]
      _ = (ε⁻¹ * β) • A v := by rw [smul_smul]
      _ = (ε * β) • A v := by rw [hεinv]
  have hAB2 : ∀ v, (A.comp B) ((A.comp B) v) = (ε * α * β) • v := by
    intro v
    have h := congrArg A (hBAB v)
    simp only [map_smul] at h
    rw [hA2 v] at h
    simp only [smul_smul] at h
    change A (B (A (B v))) = (ε * α * β) • v
    rw [h]
    congr 1
    ring
  have hμAB : ∀ v, Q ((A.comp B) v) = (μA * μB) * Q v := by
    intro v
    change Q (A (B v)) = (μA * μB) * Q v
    rw [hμA, hμB]
    ring
  obtain ⟨hscaleA, hcA2, hskewA⟩ := polar_scale_data hQ h2 hμA hA2 hα hv₀
  obtain ⟨hscaleB, hcB2, hskewB⟩ := polar_scale_data hQ h2 hμB hB2 hβ hv₀
  obtain ⟨hscaleAB, hcAB2, hskewAB⟩ :=
    polar_scale_data hQ h2 hμAB hAB2 (mul_ne_zero (mul_ne_zero hε hα) hβ) hv₀
  let qA : QuadraticForm K V := (LinearMap.BilinForm.compRight (polarBilin Q) A).toQuadraticMap
  let qB : QuadraticForm K V := (LinearMap.BilinForm.compRight (polarBilin Q) B).toQuadraticMap
  let qAB : QuadraticForm K V :=
    (LinearMap.BilinForm.compRight (polarBilin Q) (A.comp B)).toQuadraticMap
  have hqA : ∀ v, qA v = polar Q v (A v) := by
    intro v
    simp only [qA, LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.BilinForm.compRight_apply,
      QuadraticMap.polarBilin_apply_apply]
  have hqB : ∀ v, qB v = polar Q v (B v) := by
    intro v
    simp only [qB, LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.BilinForm.compRight_apply,
      QuadraticMap.polarBilin_apply_apply]
  have hqAB : ∀ v, qAB v = polar Q v (A (B v)) := by
    intro v
    simp only [qAB, LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.BilinForm.compRight_apply,
      QuadraticMap.polarBilin_apply_apply, LinearMap.comp_apply]
  have hmain : ∃ v : V, v ≠ 0 ∧ Q v = 0 ∧ polar Q v (A v) = 0 ∧ polar Q v (B v) = 0 ∧
      polar Q v (A (B v)) = 0 := by
    rcases hdim with h9 | ⟨h7, hnot⟩
    · have hlt : 2 * 4 < Module.finrank K V := by omega
      obtain ⟨v, hv0, hv⟩ :=
        CFSG.FiniteField.exists_ne_zero_forall_eq_zero_of_quadraticForm
          (fun i : Fin 4 => ![Q, qA, qB, qAB] i) hlt
      refine ⟨v, hv0, ?_, ?_, ?_, ?_⟩
      · simpa using hv 0
      · simpa [hqA] using hv 1
      · simpa [hqB] using hv 2
      · simpa [hqAB] using hv 3
    · have hcA_cases : μA / α = 1 ∨ μA / α = -1 := by
        have h : (μA / α) ^ 2 = 1 := by rwa [pow_two]
        exact sq_eq_one_iff.mp h
      have hcB_cases : μB / β = 1 ∨ μB / β = -1 := by
        have h : (μB / β) ^ 2 = 1 := by rwa [pow_two]
        exact sq_eq_one_iff.mp h
      have hcAB_cases : (μA * μB) / (ε * α * β) = 1 ∨ (μA * μB) / (ε * α * β) = -1 := by
        have h : ((μA * μB) / (ε * α * β)) ^ 2 = 1 := by rwa [pow_two]
        exact sq_eq_one_iff.mp h
      have hselfA : μA / α = 1 → ∀ u w, polar Q (A u) w = polar Q u (A w) := by
        intro hc u w
        rw [hscaleA u w, hc, one_mul]
      have hselfB : μB / β = 1 → ∀ u w, polar Q (B u) w = polar Q u (B w) := by
        intro hc u w
        rw [hscaleB u w, hc, one_mul]
      have hselfAB : (μA * μB) / (ε * α * β) = 1 →
          ∀ u w, polar Q ((A.comp B) u) w = polar Q u ((A.comp B) w) := by
        intro hc u w
        rw [hscaleAB u w, hc, one_mul]
      have hcomm : μA / α = 1 → μB / β = 1 → (μA * μB) / (ε * α * β) = 1 →
          ∀ v, A (B v) = B (A v) := by
        intro hA1 hB1 hAB1 v
        have h : A (B v) - B (A v) = 0 := by
          apply eq_zero_of_polar_eq_zero hQ
          intro w
          rw [polar_sub_left]
          have h1 : polar Q (A (B v)) w = polar Q v (A (B w)) := hselfAB hAB1 v w
          have h2 : polar Q (B (A v)) w = polar Q (A v) (B w) := hselfB hB1 (A v) w
          have h3 : polar Q (A v) (B w) = polar Q v (A (B w)) := hselfA hA1 v (B w)
          rw [h1, h2, h3, sub_self]
        exact sub_eq_zero.mp h
      have hskew_exists : μA / α = -1 ∨ μB / β = -1 ∨ (μA * μB) / (ε * α * β) = -1 := by
        rcases hcA_cases with hA1 | hAm1
        · rcases hcB_cases with hB1 | hBm1
          · rcases hcAB_cases with hAB1 | hABm1
            · exact absurd ⟨hselfA hA1, hselfB hB1, hcomm hA1 hB1 hAB1⟩ hnot
            · exact Or.inr (Or.inr hABm1)
          · exact Or.inr (Or.inl hBm1)
        · exact Or.inl hAm1
      have hlt : 2 * 3 < Module.finrank K V := by omega
      rcases hskew_exists with hAm1 | hBm1 | hABm1
      · obtain ⟨v, hv0, hv⟩ :=
          CFSG.FiniteField.exists_ne_zero_forall_eq_zero_of_quadraticForm
          (fun i : Fin 3 => ![Q, qB, qAB] i) hlt
        refine ⟨v, hv0, ?_, hskewA hAm1 v, ?_, ?_⟩
        · simpa using hv 0
        · simpa [hqB] using hv 1
        · simpa [hqAB] using hv 2
      · obtain ⟨v, hv0, hv⟩ :=
          CFSG.FiniteField.exists_ne_zero_forall_eq_zero_of_quadraticForm
          (fun i : Fin 3 => ![Q, qA, qAB] i) hlt
        refine ⟨v, hv0, ?_, ?_, hskewB hBm1 v, ?_⟩
        · simpa using hv 0
        · simpa [hqA] using hv 1
        · simpa [hqAB] using hv 2
      · obtain ⟨v, hv0, hv⟩ :=
          CFSG.FiniteField.exists_ne_zero_forall_eq_zero_of_quadraticForm
          (fun i : Fin 3 => ![Q, qA, qB] i) hlt
        refine ⟨v, hv0, ?_, ?_, ?_, hskewAB hABm1 v⟩
        · simpa using hv 0
        · simpa [hqA] using hv 1
        · simpa [hqB] using hv 2
  obtain ⟨v, hv0, hQv, hvA, hvB, hvAB⟩ := hmain
  have hpolarA : ∀ u w, polar Q (A u) (A w) = μA * polar Q u w := by
    intro u w
    rw [polar, polar, ← map_add, hμA, hμA, hμA]
    ring
  have hpolarB : ∀ u w, polar Q (B u) (B w) = μB * polar Q u w := by
    intro u w
    rw [polar, polar, ← map_add, hμB, hμB, hμB]
    ring
  have hpolarAB : ∀ u w, polar Q ((A.comp B) u) ((A.comp B) w) = (μA * μB) * polar Q u w := by
    intro u w
    rw [polar, polar, ← map_add, hμAB, hμAB, hμAB]
    ring
  have h00 : polar Q v v = 0 := by rw [polar_self_eq_two_mul, hQv, mul_zero]
  have h01 : polar Q v (A v) = 0 := hvA
  have h02 : polar Q v (B v) = 0 := hvB
  have h03 : polar Q v (A (B v)) = 0 := hvAB
  have h11 : polar Q (A v) (A v) = 0 := by rw [hpolarA, h00, mul_zero]
  have h12 : polar Q (A v) (B v) = 0 := by rw [hscaleA v (B v), h03, mul_zero]
  have h13 : polar Q (A v) (A (B v)) = 0 := by rw [hpolarA, h02, mul_zero]
  have h22 : polar Q (B v) (B v) = 0 := by rw [hpolarB, h00, mul_zero]
  have h23 : polar Q (B v) (A (B v)) = 0 := by
    rw [hscaleB v (A (B v)), hBAB v, polar_smul_right, h01]
    simp
  have h33 : polar Q (A (B v)) (A (B v)) = 0 := by
    change polar Q ((A.comp B) v) ((A.comp B) v) = 0
    rw [hpolarAB, h00, mul_zero]
  have hsymm : ∀ x y : V, polar Q x y = 0 → polar Q y x = 0 := by
    intro x y h
    rwa [polar_comm Q y x]
  let S : Set V := {v, A v, B v, A (B v)}
  have hS0 : ∀ u ∈ S, Q u = 0 := by
    intro u hu
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact hQv
    · rw [hμA]; simp [hQv]
    · rw [hμB]; simp [hQv]
    · change Q ((A.comp B) v) = 0
      rw [hμAB]
      simp [hQv]
  have hSorth : ∀ u ∈ S, ∀ w ∈ S, polar Q u w = 0 := by
    intro u hu w hw
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hw
    rcases hu with rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl
    · exact h00
    · exact h01
    · exact h02
    · exact h03
    · exact hsymm _ _ h01
    · exact h11
    · exact h12
    · exact h13
    · exact hsymm _ _ h02
    · exact hsymm _ _ h12
    · exact h22
    · exact h23
    · exact hsymm _ _ h03
    · exact hsymm _ _ h13
    · exact hsymm _ _ h23
    · exact h33
  refine ⟨Submodule.span K S, ?_, ?_, ?_, ?_⟩
  · intro hbot
    have hmem : v ∈ Submodule.span K S := Submodule.subset_span (by simp [S])
    rw [hbot] at hmem
    exact hv0 (by simpa using hmem)
  · intro x hx
    exact map_eq_zero_of_mem_span (Q := Q) hS0 hSorth hx
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · exact Submodule.subset_span (by simp [S])
        · rw [hA2]; exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [S]))
        · exact Submodule.subset_span (by simp [S])
        · rw [hA2]; exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [S]))
    | zero => simp
    | add y z hy hz ihy ihz => rw [map_add]; exact Submodule.add_mem _ ihy ihz
    | smul a y hy ihy => rw [map_smul]; exact Submodule.smul_mem _ _ ihy
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · exact Submodule.subset_span (by simp [S])
        · rw [hBA]; exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [S]))
        · rw [hB2]; exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [S]))
        · rw [hBAB]; exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [S]))
    | zero => simp
    | add y z hy hz ihy ihz => rw [map_add]; exact Submodule.add_mem _ ihy ihz
    | smul a y hy ihy => rw [map_smul]; exact Submodule.smul_mem _ _ ihy

end CFSG.LocalAnalysis.WeakClosure81.POmegaOuter
