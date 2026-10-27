module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.Classical

open QuadraticMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem quad_smul_add_smul (Q : QuadraticForm K V) {x y : V} (hxy : polar Q x y = 0) (s t : K) :
    Q (s • x + t • y) = s ^ 2 * Q x + t ^ 2 * Q y := by
  rw [QuadraticMap.map_add (⇑Q) (s • x) (t • y), QuadraticMap.map_smul, QuadraticMap.map_smul,
    polar_smul_left, polar_smul_right, hxy]
  simp only [smul_eq_mul, mul_zero, add_zero]
  ring

theorem polar_smul_add_smul (Q : QuadraticForm K V) {x y : V} (hxy : polar Q x y = 0)
    (s t α β : K) :
    polar Q (s • x + t • y) (α • x + β • y) = 2 * (s * α * Q x + t * β * Q y) := by
  rw [polar_add_left, polar_add_right, polar_add_right, polar_smul_left, polar_smul_left,
    polar_smul_right, polar_smul_right, polar_smul_left, polar_smul_left, polar_smul_right,
    polar_smul_right, polar_self, polar_self, hxy, polar_comm Q y x, hxy]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, mul_zero, add_zero, zero_add]
  ring

theorem exists_mul_sq_add_mul_sq_eq [Fintype K] (hK : Fintype.card K % 2 = 1) {b c : K}
    (hb : b ≠ 0) (hc : c ≠ 0) (a : K) : ∃ s t : K, b * s ^ 2 + c * t ^ 2 = a := by
  have hdeg : (Polynomial.C c * Polynomial.X ^ 2 - Polynomial.C a).degree = 2 := by
    rw [Polynomial.degree_sub_C (by rw [Polynomial.degree_C_mul_X_pow 2 hc]; norm_num),
      Polynomial.degree_C_mul_X_pow 2 hc]
    rfl
  obtain ⟨s, t, h⟩ := FiniteField.exists_root_sum_quadratic (R := K)
    (f := Polynomial.C b * Polynomial.X ^ 2) (Polynomial.degree_C_mul_X_pow 2 hb) hdeg hK
  refine ⟨s, t, ?_⟩
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub] at h
  linear_combination h

theorem exists_plane_step [Fintype K] (hK : Fintype.card K % 2 = 1) (Q : QuadraticForm K V)
    {x y : V} (hxy : polar Q x y = 0) (hx : Q x ≠ 0) (hy : Q y ≠ 0) {a : K} (ha : a ≠ 0) :
    ∃ s t α β : K, Q (s • x + t • y) = a ∧ Q (α • x + β • y) ≠ 0 ∧
      polar Q (s • x + t • y) (α • x + β • y) = 0 := by
  obtain ⟨s, t, hst⟩ := exists_mul_sq_add_mul_sq_eq hK hx hy a
  refine ⟨s, t, t * Q y, -(s * Q x), ?_, ?_, ?_⟩
  · rw [quad_smul_add_smul Q hxy]
    linear_combination hst
  · rw [quad_smul_add_smul Q hxy]
    have : (t * Q y) ^ 2 * Q x + (-(s * Q x)) ^ 2 * Q y = Q x * Q y * a := by
      rw [← hst]
      ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero hx hy) ha
  · rw [polar_smul_add_smul Q hxy]
    ring

theorem polar_smul_add_smul_right_eq_zero (Q : QuadraticForm K V) {z x y : V}
    (hx : polar Q z x = 0) (hy : polar Q z y = 0) (s t : K) :
    polar Q z (s • x + t • y) = 0 := by
  rw [polar_add_right, polar_smul_right, polar_smul_right, hx, hy]
  simp

theorem exists_orthogonal_family_quad_eq [Fintype K] (hK : Fintype.card K % 2 = 1)
    (Q : QuadraticForm K V) {d : ℕ} (v₀ : Fin d → V)
    (hv₀ : ∀ i j, i ≠ j → polar Q (v₀ i) (v₀ j) = 0) (hQ₀ : ∀ i, Q (v₀ i) ≠ 0) {a : K}
    (ha : a ≠ 0) (k : ℕ) (hk : k < d) :
    ∃ v : Fin d → V, (∀ i j, i ≠ j → polar Q (v i) (v j) = 0) ∧ (∀ i, Q (v i) ≠ 0) ∧
      ∀ i : Fin d, (i : ℕ) < k → Q (v i) = a := by
  induction k with
  | zero => exact ⟨v₀, hv₀, hQ₀, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨v, hv, hQ, hva⟩ := ih (by omega)
    set i₀ : Fin d := ⟨k, by omega⟩ with hi₀
    set i₁ : Fin d := ⟨k + 1, hk⟩ with hi₁
    have h01 : i₀ ≠ i₁ := by simp [hi₀, hi₁, Fin.ext_iff]
    obtain ⟨s, t, α, β, h1, h2, h3⟩ := exists_plane_step hK Q (hv i₀ i₁ h01) (hQ i₀) (hQ i₁) ha
    set u := s • v i₀ + t • v i₁
    set w := α • v i₀ + β • v i₁
    let v' : Fin d → V := fun i => if i = i₀ then u else if i = i₁ then w else v i
    have hv'0 : v' i₀ = u := by simp [v']
    have hv'1 : v' i₁ = w := by simp [v', h01.symm]
    have hv'o : ∀ i, i ≠ i₀ → i ≠ i₁ → v' i = v i := fun i h0 h1 => by
      simp [v', h0, h1]
    have hou : ∀ i, i ≠ i₀ → i ≠ i₁ → polar Q (v i) u = 0 := fun i h0 h1 =>
      polar_smul_add_smul_right_eq_zero Q (hv i i₀ h0) (hv i i₁ h1) s t
    have how : ∀ i, i ≠ i₀ → i ≠ i₁ → polar Q (v i) w = 0 := fun i h0 h1 =>
      polar_smul_add_smul_right_eq_zero Q (hv i i₀ h0) (hv i i₁ h1) α β
    refine ⟨v', fun i j hij => ?_, fun i => ?_, fun i hi => ?_⟩
    · by_cases hi0 : i = i₀
      · subst hi0
        by_cases hj1 : j = i₁
        · subst hj1
          rw [hv'0, hv'1, h3]
        · rw [hv'0, hv'o j (Ne.symm hij) hj1, polar_comm]
          exact hou j (Ne.symm hij) hj1
      by_cases hi1 : i = i₁
      · subst hi1
        by_cases hj0 : j = i₀
        · subst hj0
          rw [hv'0, hv'1, polar_comm, h3]
        · rw [hv'1, hv'o j hj0 (Ne.symm hij), polar_comm]
          exact how j hj0 (Ne.symm hij)
      rw [hv'o i hi0 hi1]
      by_cases hj0 : j = i₀
      · subst hj0
        rw [hv'0]
        exact hou i hi0 hi1
      by_cases hj1 : j = i₁
      · subst hj1
        rw [hv'1]
        exact how i hi0 hi1
      rw [hv'o j hj0 hj1]
      exact hv i j hij
    · by_cases hi0 : i = i₀
      · subst hi0
        rw [hv'0, h1]
        exact ha
      by_cases hi1 : i = i₁
      · subst hi1
        rw [hv'1]
        exact h2
      rw [hv'o i hi0 hi1]
      exact hQ i
    · by_cases hi0 : i = i₀
      · subst hi0
        rw [hv'0, h1]
      have hik : (i : ℕ) < k := by
        have : (i : ℕ) ≠ k := fun h => hi0 (Fin.ext h)
        omega
      have hi1 : i ≠ i₁ := fun h => by rw [h] at hik; simp [hi₁] at hik
      rw [hv'o i hi0 hi1]
      exact hva i hik

theorem two_ne_zero_of_card_odd [Fintype K] (hK : Fintype.card K % 2 = 1) : (2 : K) ≠ 0 :=
  Ring.two_ne_zero fun h => by
    have := FiniteField.even_card_iff_char_two.mp h
    omega

theorem isSymm_polarBilin (Q : QuadraticForm K V) : (polarBilin Q).IsSymm :=
  LinearMap.isSymm_def.mpr fun x y => by
    simp only [RingHom.id_apply, polarBilin_apply_apply, polar_comm]

theorem nondegenerate_restrict_span {ι : Type*} [Fintype ι] (h2 : (2 : K) ≠ 0)
    (Q : QuadraticForm K V) {f : ι → V} (hf : ∀ i j, i ≠ j → polar Q (f i) (f j) = 0)
    (hQ : ∀ i, Q (f i) ≠ 0) :
    LinearIndependent K f ∧
      (LinearMap.BilinForm.restrict (polarBilin Q)
        (Submodule.span K (Set.range f))).Nondegenerate := by
  have hself : ∀ i, polarBilin Q (f i) (f i) ≠ 0 := fun i => by
    rw [polarBilin_apply_apply, polar_self, nsmul_eq_mul, Nat.cast_ofNat]
    exact mul_ne_zero h2 (hQ i)
  have hli : LinearIndependent K f :=
    LinearMap.BilinForm.linearIndependent_of_iIsOrtho
      (fun i j hij => by
        show polarBilin Q (f i) (f j) = 0
        rw [polarBilin_apply_apply]
        exact hf i j hij) hself
  refine ⟨hli, ?_⟩
  set b := Module.Basis.span hli
  refine (LinearMap.BilinForm.iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self
    (LinearMap.BilinForm.restrict (polarBilin Q) _) b (fun i j hij => ?_)).mpr fun i => ?_
  · show polarBilin Q (b i : V) (b j : V) = 0
    rw [Module.Basis.span_apply, Module.Basis.span_apply, polarBilin_apply_apply]
    exact hf i j hij
  · show polarBilin Q (b i : V) (b i : V) ≠ 0
    rw [Module.Basis.span_apply]
    exact hself i

theorem exists_orthogonal_basis_quad_eq [Finite K] (hK : Odd (Nat.card K))
    [FiniteDimensional K V] {d : ℕ} (hd : Module.finrank K V = d) (hd2 : 2 ≤ d)
    (Q : QuadraticForm K V) (hB : LinearMap.BilinForm.Nondegenerate (polarBilin Q)) {a : K}
    (ha : a ≠ 0) :
    ∃ v : Module.Basis (Fin d) K V, (∀ i j, i ≠ j → polar Q (v i) (v j) = 0) ∧
      (∀ i : Fin d, (i : ℕ) + 1 < d → Q (v i) = a) ∧ Q (v ⟨d - 1, by omega⟩) ≠ 0 := by
  have := Fintype.ofFinite K
  have hK' : Fintype.card K % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hK
  have h2 := two_ne_zero_of_card_odd hK'
  have : Invertible (2 : K) := invertibleOfNonzero h2
  obtain ⟨e, he⟩ := LinearMap.BilinForm.exists_orthogonal_basis (isSymm_polarBilin Q)
  subst hd
  have hv₀ : ∀ i j, i ≠ j → polar Q (e i) (e j) = 0 := fun i j hij => by
    rw [← polarBilin_apply_apply]
    exact he hij
  have hQ₀ : ∀ i, Q (e i) ≠ 0 := fun i hi => by
    have h := LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate he hB i
    rw [polarBilin_apply_apply, polar_self, hi, smul_zero] at h
    exact h rfl
  obtain ⟨v, hv, hQ, hva⟩ := exists_orthogonal_family_quad_eq hK' Q e hv₀ hQ₀ ha
    (Module.finrank K V - 1) (by omega)
  have hli := (nondegenerate_restrict_span h2 Q hv hQ).1
  have : Nonempty (Fin (Module.finrank K V)) := ⟨⟨0, by omega⟩⟩
  let vb := basisOfLinearIndependentOfCardEqFinrank hli (Fintype.card_fin _)
  have hvb : ∀ i, vb i = v i := fun i => by
    simp [vb, coe_basisOfLinearIndependentOfCardEqFinrank]
  refine ⟨vb, fun i j hij => ?_, fun i hi => ?_, ?_⟩
  · rw [hvb, hvb]
    exact hv i j hij
  · rw [hvb]
    exact hva i (by omega)
  · rw [hvb]
    exact hQ _

theorem exists_regular_six_frame [Finite K] (hK : Odd (Nat.card K)) [FiniteDimensional K V]
    (hd : 7 ≤ Module.finrank K V) (Q : QuadraticForm K V)
    (hB : LinearMap.BilinForm.Nondegenerate (polarBilin Q)) :
    ∃ W : Submodule K V, Module.finrank K W = 6 ∧
      (LinearMap.BilinForm.restrict (polarBilin Q) W).Nondegenerate ∧
      (∃ w : Module.Basis (Fin 6) K W,
        (∀ i j, i ≠ j → polar Q (w i) (w j) = 0) ∧ ∀ i, Q (w i) = 1) ∧
      LinearMap.BilinForm.orthogonal (polarBilin Q) W ≠ ⊥ ∧
      (LinearMap.BilinForm.restrict (polarBilin Q)
        (LinearMap.BilinForm.orthogonal (polarBilin Q) W)).Nondegenerate := by
  have := Fintype.ofFinite K
  have hK' : Fintype.card K % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hK
  have h2 := two_ne_zero_of_card_odd hK'
  set d := Module.finrank K V with hd'
  obtain ⟨v, hv, hva, hvd⟩ :=
    exists_orthogonal_basis_quad_eq hK hd'.symm (by omega) Q hB one_ne_zero
  have hQv : ∀ i, Q (v i) ≠ 0 := fun i => by
    by_cases hi : (i : ℕ) + 1 < d
    · rw [hva i hi]
      exact one_ne_zero
    · have : i = ⟨d - 1, by omega⟩ := Fin.ext (by have := i.isLt; simp; omega)
      rw [this]
      exact hvd
  let f₁ : Fin 6 → V := fun j => v ⟨j, by omega⟩
  let f₂ : Fin (d - 6) → V := fun j => v ⟨j + 6, by omega⟩
  have hf₁ : ∀ i j, i ≠ j → polar Q (f₁ i) (f₁ j) = 0 := fun i j hij =>
    hv _ _ fun h => hij (Fin.ext (by simpa using congrArg Fin.val h))
  have hf₂ : ∀ i j, i ≠ j → polar Q (f₂ i) (f₂ j) = 0 := fun i j hij =>
    hv _ _ fun h => hij (Fin.ext (by simpa using congrArg Fin.val h))
  obtain ⟨hli₁, hW⟩ := nondegenerate_restrict_span h2 Q hf₁ fun i => hQv _
  obtain ⟨hli₂, hW'⟩ := nondegenerate_restrict_span h2 Q hf₂ fun i => hQv _
  set W := Submodule.span K (Set.range f₁)
  set W' := Submodule.span K (Set.range f₂)
  have hfin₁ : Module.finrank K W = 6 := by
    rw [finrank_span_eq_card hli₁, Fintype.card_fin]
  have hfin₂ : Module.finrank K W' = d - 6 := by
    rw [finrank_span_eq_card hli₂, Fintype.card_fin]
  have hle : W' ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) W := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    refine Submodule.span_induction (p := fun x _ => polarBilin Q x (f₂ j) = 0) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      rw [polarBilin_apply_apply]
      exact hv _ _ fun h => by have := congrArg Fin.val h; simp at this; omega
    · simp
    · intro x y _ _ hx hy
      rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    · intro c x _ hx
      rw [map_smul, LinearMap.smul_apply, hx, smul_zero]
  have hker : LinearMap.ker (polarBilin Q) = ⊥ :=
    LinearMap.BilinForm.Nondegenerate.ker_eq_bot hB
  have hdim := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := polarBilin Q) W
  rw [hker, inf_bot_eq, finrank_bot, add_zero, hfin₁] at hdim
  have heq : W' = LinearMap.BilinForm.orthogonal (polarBilin Q) W :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  refine ⟨W, hfin₁, hW, ⟨Module.Basis.span hli₁, fun i j hij => ?_, fun i => ?_⟩, ?_, ?_⟩
  · rw [Module.Basis.span_apply, Module.Basis.span_apply]
    exact hf₁ i j hij
  · rw [Module.Basis.span_apply]
    exact hva _ (by simp; omega)
  · rw [← heq]
    intro h
    rw [h, finrank_bot] at hfin₂
    omega
  · rw [← heq]
    exact hW'

end CFSG.RankThree.Classical
