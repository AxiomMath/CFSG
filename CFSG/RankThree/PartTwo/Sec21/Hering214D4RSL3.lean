module

public import CFSG.RankThree.PartTwo.Sec21.Hering214L3Std

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open Matrix

section SL3Four

variable {F : Type*} [Field F]

open Polynomial in
theorem cube_factor {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (d : F) (H : Matrix (Fin 3) (Fin 3) F) :
    (H - d • 1) * (H - (d * ω) • 1) * (H - (d * ω ^ 2) • 1) = H ^ 3 - (d ^ 3) • 1 := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hw : (C ω) ^ 2 + C ω + 1 = 0 := by
    have h := congrArg C hω
    simpa using h
  have hw3 : (C ω) ^ 3 = 1 := by
    have h := congrArg C hω3
    simpa using h
  have hP : (X - C d) * (X - C (d * ω)) * (X - C (d * ω ^ 2)) = X ^ 3 - C (d ^ 3) := by
    simp only [map_mul, map_pow]
    linear_combination (-(C d) * X ^ 2 + (C d) ^ 2 * X) * hw + ((C d) ^ 2 * X - (C d) ^ 3) * hw3
  have h1 := congrArg (Polynomial.aeval H) hP
  rw [map_mul, map_mul] at h1
  simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_X_pow, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one] at h1
  exact h1

theorem cayley_hamilton_three_fin (M : Matrix (Fin 3) (Fin 3) F) :
    ∃ a b : F, M * M * M - a • (M * M) + b • M - M.det • (1 : Matrix (Fin 3) (Fin 3) F) = 0 := by
  refine ⟨M.trace, M 0 0 * M 1 1 - M 0 1 * M 1 0 + (M 0 0 * M 2 2 - M 0 2 * M 2 0) +
    (M 1 1 * M 2 2 - M 1 2 * M 2 1), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.det_fin_three, Matrix.trace_fin_three,
      Matrix.one_apply] <;> ring

theorem noncube_false [CharP F 2] {H : Matrix (Fin 3) (Fin 3) F} {c : F} (hdet : H.det = 1)
    (hH3 : H ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) F)) (hc3 : c ^ 3 = 1)
    (hns : ∀ x : F, H ≠ x • (1 : Matrix (Fin 3) (Fin 3) F))
    (hcube : ¬ ∃ d : F, d ^ 3 = c) : False := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hc0 : c ≠ 0 := by
    rintro rfl
    norm_num at hc3
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hcube ⟨1, one_pow 3⟩
  have hc2 : c ^ 2 + c + 1 = 0 := by
    have h : (c - 1) * (c ^ 2 + c + 1) = 0 := by linear_combination hc3
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hc1)
  have hcc : (c - 1) • (1 : Matrix (Fin 3) (Fin 3) F) = c ^ 2 • (1 : Matrix (Fin 3) (Fin 3) F) := by
    congr 1
    linear_combination -hc2 + c * h2
  obtain ⟨a, b, CH⟩ := cayley_hamilton_three_fin H
  rw [hdet, one_smul] at CH
  have hHHH : H * H * H = c • (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [← hH3, pow_three']
  rw [hHHH] at CH
  have E1 : a • (H * H) - b • H = c ^ 2 • (1 : Matrix (Fin 3) (Fin 3) F) := by
    linear_combination (norm := module) -CH + hcc
  have E2 : a • (c • (1 : Matrix (Fin 3) (Fin 3) F)) - b • (H * H) = c ^ 2 • H := by
    have h := congrArg (fun X => H * X) E1
    simp only [mul_sub, Matrix.mul_smul, mul_one, ← mul_assoc, hHHH] at h
    linear_combination (norm := module) h
  have E3 : (b ^ 2 + a * c ^ 2) • H = (a ^ 2 * c - b * c ^ 2) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    linear_combination (norm := module) (-b) • E1 + (-a) • E2
  have hA : b ^ 2 + a * c ^ 2 = 0 := by
    by_contra hne
    apply hns ((a ^ 2 * c - b * c ^ 2) / (b ^ 2 + a * c ^ 2))
    calc H = (b ^ 2 + a * c ^ 2)⁻¹ • ((b ^ 2 + a * c ^ 2) • H) := by
          rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = (b ^ 2 + a * c ^ 2)⁻¹ • ((a ^ 2 * c - b * c ^ 2) • (1 : Matrix (Fin 3) (Fin 3) F)) := by
          rw [E3]
      _ = _ := by rw [smul_smul, div_eq_inv_mul]
  have hB : a ^ 2 * c - b * c ^ 2 = 0 := by
    rw [hA, zero_smul] at E3
    rcases smul_eq_zero.mp E3.symm with h | h
    · exact h
    · exact absurd h one_ne_zero
  have hb : b = a ^ 2 * c ^ 2 := by linear_combination (-c) * hB - b * hc3
  have hK : a * (a ^ 3 * c + c ^ 2) = 0 := by
    linear_combination hA - (b + a ^ 2 * c ^ 2) * hb - a ^ 4 * c * hc3
  rcases mul_eq_zero.mp hK with ha0 | hK'
  ·
    have hb0 : b = 0 := by rw [hb, ha0]; ring
    have h1 : c ^ 2 • (1 : Matrix (Fin 3) (Fin 3) F) = 0 := by
      rw [← E1, ha0, hb0]
      simp
    rcases smul_eq_zero.mp h1 with h | h
    · exact hc0 ((pow_eq_zero_iff two_ne_zero).mp h)
    · exact one_ne_zero h
  · have hX : a ^ 3 * c - c ^ 2 = 0 := by linear_combination hK' - c ^ 2 * h2
    have ha3 : a ^ 3 = c := by linear_combination (-a ^ 3 + c) * hc3 + c ^ 2 * hX
    exact hcube ⟨a, ha3⟩

theorem two_eigen_of_cube {ω : F} [CharP F 2] (hω : ω ^ 2 + ω + 1 = 0) {d : F} (hd0 : d ≠ 0)
    {H : Matrix (Fin 3) (Fin 3) F} (hH3 : H ^ 3 = (d ^ 3) • (1 : Matrix (Fin 3) (Fin 3) F))
    (hns : ∀ x : F, H ≠ x • (1 : Matrix (Fin 3) (Fin 3) F)) :
    ∃ l m : F, l ≠ m ∧ l ^ 3 = d ^ 3 ∧ m ^ 3 = d ^ 3 ∧
      (H - l • (1 : Matrix (Fin 3) (Fin 3) F)).det = 0 ∧
      (H - m • (1 : Matrix (Fin 3) (Fin 3) F)).det = 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω1 : ω ≠ 1 := by
    intro h1
    apply one_ne_zero (α := F)
    rw [h1] at hω
    linear_combination hω - h2
  have hωz : ω ≠ 0 := by
    intro h0
    apply one_ne_zero (α := F)
    rw [h0] at hω
    linear_combination hω
  have hω2 : ω ^ 2 ≠ 1 := fun h1 => hωz (by linear_combination hω - h1 - h2)
  have hωω2 : ω ≠ ω ^ 2 := fun h1 => one_ne_zero (α := F) (by linear_combination hω + h1 - ω * h2)
  have hω6 : (ω ^ 2) ^ 3 = 1 := by rw [show (ω ^ 2) ^ 3 = (ω ^ 3) ^ 2 by ring, hω3, one_pow]
  have hmul : ∀ x y : F, x ≠ y → d * x ≠ d * y := fun x y hxy h => hxy (mul_left_cancel₀ hd0 h)
  have hdω : d ≠ d * ω := by
    have h := hmul 1 ω (Ne.symm hω1)
    rwa [mul_one] at h
  have hdω2 : d ≠ d * ω ^ 2 := by
    have h := hmul 1 (ω ^ 2) (Ne.symm hω2)
    rwa [mul_one] at h
  have hdωdω2 : d * ω ≠ d * ω ^ 2 := hmul ω (ω ^ 2) hωω2
  have hd3 : (d * ω) ^ 3 = d ^ 3 := by rw [mul_pow, hω3, mul_one]
  have hd3' : (d * ω ^ 2) ^ 3 = d ^ 3 := by rw [mul_pow, hω6, mul_one]
  have hfac : (H - d • (1 : Matrix (Fin 3) (Fin 3) F)) *
      (H - (d * ω) • (1 : Matrix (Fin 3) (Fin 3) F)) *
      (H - (d * ω ^ 2) • (1 : Matrix (Fin 3) (Fin 3) F)) = 0 := by
    rw [cube_factor hω d H, hH3, sub_self]
  have hne : ∀ x : F, H - x • (1 : Matrix (Fin 3) (Fin 3) F) ≠ 0 :=
    fun x h0 => hns x (sub_eq_zero.mp h0)
  have hunit : ∀ x : F, (H - x • (1 : Matrix (Fin 3) (Fin 3) F)).det ≠ 0 →
      IsUnit (H - x • (1 : Matrix (Fin 3) (Fin 3) F)) := fun x hx =>
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hx)
  by_cases e0 : (H - d • (1 : Matrix (Fin 3) (Fin 3) F)).det = 0 <;>
    by_cases e1 : (H - (d * ω) • (1 : Matrix (Fin 3) (Fin 3) F)).det = 0 <;>
    by_cases e2 : (H - (d * ω ^ 2) • (1 : Matrix (Fin 3) (Fin 3) F)).det = 0
  · exact ⟨d, d * ω, hdω, rfl, hd3, e0, e1⟩
  · exact ⟨d, d * ω, hdω, rfl, hd3, e0, e1⟩
  · exact ⟨d, d * ω ^ 2, hdω2, rfl, hd3', e0, e2⟩
  · exfalso
    have h0 : H - d • (1 : Matrix (Fin 3) (Fin 3) F) = 0 := by
      rw [mul_assoc] at hfac
      exact (IsUnit.mul_left_eq_zero ((hunit _ e1).mul (hunit _ e2))).mp hfac
    exact hne d h0
  · exact ⟨d * ω, d * ω ^ 2, hdωdω2, hd3, hd3', e1, e2⟩
  · exfalso
    have h1 : H - (d * ω) • (1 : Matrix (Fin 3) (Fin 3) F) = 0 :=
      (IsUnit.mul_right_eq_zero (hunit _ e0)).mp ((IsUnit.mul_left_eq_zero (hunit _ e2)).mp hfac)
    exact hne _ h1
  · exfalso
    have h3 : H - (d * ω ^ 2) • (1 : Matrix (Fin 3) (Fin 3) F) = 0 :=
      (IsUnit.mul_right_eq_zero ((hunit _ e0).mul (hunit _ e1))).mp hfac
    exact hne _ h3
  · exfalso
    have h3 : H - (d * ω ^ 2) • (1 : Matrix (Fin 3) (Fin 3) F) = 0 :=
      (IsUnit.mul_right_eq_zero ((hunit _ e0).mul (hunit _ e1))).mp hfac
    exact hne _ h3

theorem four_group_of_eigen [CharP F 2] {ω : F} (hω : ω ^ 2 + ω + 1 = 0)
    (h : Matrix.SpecialLinearGroup (Fin 3) F) {l m : F} (hlm : l ≠ m) (hcube : l ^ 3 = m ^ 3)
    {v : Fin 3 → F} (hv0 : v ≠ 0) (hv : (h : Matrix (Fin 3) (Fin 3) F) *ᵥ v = l • v)
    {f : Fin 3 → F} (hf0 : f ≠ 0) (hf : f ᵥ* (h : Matrix (Fin 3) (Fin 3) F) = m • f) :
    ∃ U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F), CFSG.Assembly.IsElemAbelian 2 U ∧
      Nat.card U = 4 ∧ (∀ u ∈ U, h * u * h⁻¹ ∈ U) ∧ ∃ u ∈ U, h * u * h⁻¹ ≠ u := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω1 : ω ≠ 1 := by
    intro h1
    apply one_ne_zero (α := F)
    rw [h1] at hω
    linear_combination hω - h2
  have hωz : ω ≠ 0 := by
    intro h0
    apply one_ne_zero (α := F)
    rw [h0] at hω
    linear_combination hω
  have hω2 : ω ^ 2 ≠ 1 := fun h1 => hωz (by linear_combination hω - h1 - h2)
  have hω2' : 1 + ω = ω ^ 2 := by linear_combination -hω + (ω + 1) * h2
  obtain ⟨H, hH⟩ : ∃ H : Matrix (Fin 3) (Fin 3) F, (h : Matrix (Fin 3) (Fin 3) F) = H := ⟨_, rfl⟩
  rw [hH] at hv hf
  have hm0 : m ≠ 0 := by
    intro hm
    apply hlm
    subst hm
    simpa using hcube
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : F, ρ = l * m⁻¹ := ⟨_, rfl⟩
  have hρm : ρ * m = l := by rw [hρdef, mul_assoc, inv_mul_cancel₀ hm0, mul_one]
  have hρ3 : ρ ^ 3 = 1 := by
    rw [hρdef, mul_pow, inv_pow, hcube, mul_inv_cancel₀ (pow_ne_zero 3 hm0)]
  have hρ1 : ρ ≠ 1 := by
    intro h1
    apply hlm
    rw [← hρm, h1, one_mul]
  have hρq : ρ ^ 2 + ρ + 1 = 0 := by
    have h' : (ρ - 1) * (ρ ^ 2 + ρ + 1) = 0 := by linear_combination hρ3
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hρ1)
  have hρω : ρ = ω ∨ ρ = ω ^ 2 := by
    have h' : (ρ - ω) * (ρ - ω ^ 2) = 0 := by linear_combination hρq - ρ * hω + hω3
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact Or.inl (sub_eq_zero.mp h'')
    · exact Or.inr (sub_eq_zero.mp h'')
  have hfv : f ⬝ᵥ v = 0 := by
    have e1 : f ⬝ᵥ (H *ᵥ v) = l * (f ⬝ᵥ v) := by rw [hv, dotProduct_smul, smul_eq_mul]
    have e2' : f ⬝ᵥ (H *ᵥ v) = m * (f ⬝ᵥ v) := by
      rw [dotProduct_mulVec, hf, smul_dotProduct, smul_eq_mul]
    have h' : (l - m) * (f ⬝ᵥ v) = 0 := by linear_combination e2' - e1
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hlm)
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin 3) (Fin 3) F, N = vecMulVec v f := ⟨_, rfl⟩
  have hHN : H * N = l • N := by
    ext i j
    have hvi : ∑ k, H i k * v k = l * v i := by
      have h' := congrFun hv i
      simpa [Matrix.mulVec, dotProduct] using h'
    simp only [hN, Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
    calc ∑ k, H i k * (v k * f j) = (∑ k, H i k * v k) * f j := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun k _ => by ring)
      _ = l * (v i * f j) := by rw [hvi]; ring
  have hNH : N * H = m • N := by
    ext i j
    have hfj : ∑ k, f k * H k j = m * f j := by
      have h' := congrFun hf j
      simpa [vecMul, dotProduct] using h'
    simp only [hN, Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
    calc ∑ k, v i * f k * H k j = v i * ∑ k, f k * H k j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
      _ = m * (v i * f j) := by rw [hfj]; ring
  have hNN : N * N = 0 := by
    ext i j
    have hs : ∑ k, f k * v k = 0 := by simpa [dotProduct] using hfv
    simp only [hN, Matrix.mul_apply, vecMulVec_apply, Matrix.zero_apply]
    calc ∑ k, v i * f k * (v k * f j) = (v i * f j) * ∑ k, f k * v k := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
      _ = 0 := by rw [hs, mul_zero]
  have hN0 : N ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv0 (funext hcon)
    obtain ⟨j, hj⟩ : ∃ j, f j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hf0 (funext hcon)
    intro hzero
    have hij := congrFun (congrFun hzero i) j
    rw [hN, vecMulVec_apply, Matrix.zero_apply] at hij
    exact mul_ne_zero hi hj hij
  have hdetA : ∀ s : F, (1 + s • N).det = 1 := by
    intro s
    have hrep : (1 + s • N : Matrix (Fin 3) (Fin 3) F) =
        1 + replicateCol Unit (s • v) * replicateRow Unit f := by
      ext i j
      simp [hN, vecMulVec_apply, replicateCol, replicateRow, Matrix.mul_apply, Matrix.one_apply]
      ring
    rw [hrep, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, hfv, smul_zero, add_zero]
  obtain ⟨A, hAdef⟩ : ∃ A : F → Matrix.SpecialLinearGroup (Fin 3) F,
      ∀ s : F, (A s : Matrix (Fin 3) (Fin 3) F) = 1 + s • N :=
    ⟨fun s => ⟨1 + s • N, hdetA s⟩, fun s => rfl⟩
  have hA0 : A 0 = 1 := by
    apply Subtype.ext
    rw [hAdef, Matrix.SpecialLinearGroup.coe_one, zero_smul, add_zero]
  have hAmul : ∀ s t : F, A s * A t = A (s + t) := by
    intro s t
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hAdef, hAdef, hAdef]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hNN,
      smul_zero, add_zero, add_smul]
    abel
  have hAinj : ∀ s t : F, A s = A t → s = t := by
    intro s t hst
    have hc : (1 + s • N : Matrix (Fin 3) (Fin 3) F) = 1 + t • N := by
      rw [← hAdef, ← hAdef, hst]
    have h3 : s • N = t • N := add_left_cancel hc
    have h4 : (s - t) • N = 0 := by rw [sub_smul, h3, sub_self]
    rcases smul_eq_zero.mp h4 with h5 | h5
    · exact sub_eq_zero.mp h5
    · exact absurd h5 hN0
  have haa : A 1 * A 1 = 1 := by rw [hAmul, CharTwo.add_self_eq_zero, hA0]
  have hbb : A ω * A ω = 1 := by rw [hAmul, CharTwo.add_self_eq_zero, hA0]
  have hab : A 1 * A ω = A ω * A 1 := by rw [hAmul, hAmul, add_comm]
  have ha1 : A 1 ≠ 1 := fun e => one_ne_zero (hAinj 1 0 (by rw [hA0]; exact e))
  have hb1 : A ω ≠ 1 := fun e => hωz (hAinj ω 0 (by rw [hA0]; exact e))
  have hne : A 1 ≠ A ω := fun e => hω1 (hAinj 1 ω e).symm
  have hconj : ∀ s : F, h * A s * h⁻¹ = A (s * ρ) := by
    intro s
    rw [mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hAdef, hAdef, hH]
    rw [mul_add, mul_one, Matrix.mul_smul, hHN, add_mul, one_mul, smul_mul_assoc, hNH,
      smul_smul, smul_smul, show s * ρ * m = s * l by rw [mul_assoc, hρm]]
  have hgen1 : A 1 ∈ Subgroup.closure ({A 1, A ω} : Set (Matrix.SpecialLinearGroup (Fin 3) F)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hgen2 : A ω ∈ Subgroup.closure ({A 1, A ω} : Set (Matrix.SpecialLinearGroup (Fin 3) F)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hmem : ∀ t : F, (t = 1 ∨ t = ω ∨ t = ω ^ 2) →
      A t ∈ Subgroup.closure ({A 1, A ω} : Set (Matrix.SpecialLinearGroup (Fin 3) F)) := by
    intro t ht
    rcases ht with h' | h' | h'
    · rw [h']; exact hgen1
    · rw [h']; exact hgen2
    · rw [h', ← hω2', ← hAmul]
      exact Subgroup.mul_mem _ hgen1 hgen2
  have hnorm : ∀ x ∈ ({A 1, A ω} : Set (Matrix.SpecialLinearGroup (Fin 3) F)),
      h * x * h⁻¹ ∈ Subgroup.closure ({A 1, A ω} : Set (Matrix.SpecialLinearGroup (Fin 3) F)) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [hconj 1]
      exact hmem _ (by rw [one_mul]; exact Or.inr hρω)
    · rw [hconj ω]
      apply hmem
      rcases hρω with hr | hr
      · rw [hr]; exact Or.inr (Or.inr (by ring))
      · rw [hr]; exact Or.inl (by linear_combination hω3)
  have hle : Subgroup.closure ({A 1, A ω} : Set (Matrix.SpecialLinearGroup (Fin 3) F)) ≤
      (Subgroup.closure ({A 1, A ω} : Set (Matrix.SpecialLinearGroup (Fin 3) F))).comap
        (MulAut.conj h).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hnorm x hx
  refine ⟨Subgroup.closure ({A 1, A ω} : Set (Matrix.SpecialLinearGroup (Fin 3) F)),
    isElemAbelian_closure_pair haa hbb hab, card_closure_pair haa hbb hab ha1 hb1 hne,
    fun u hu => hle hu, A 1, hgen1, ?_⟩
  intro heq
  rw [hconj 1, one_mul] at heq
  exact hρ1 (hAinj _ _ heq)

end SL3Four

theorem sl3_four_of_pow_three {F : Type*} [Field F] [CharP F 2] {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0)
    (h : Matrix.SpecialLinearGroup (Fin 3) F) (c : F)
    (hc : (h : Matrix (Fin 3) (Fin 3) F) ^ 3 = c • 1)
    (hns : ∀ a : F, (h : Matrix (Fin 3) (Fin 3) F) ≠ a • 1) :
    ∃ U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F), CFSG.Assembly.IsElemAbelian 2 U ∧
      Nat.card U = 4 ∧ (∀ u ∈ U, h * u * h⁻¹ ∈ U) ∧ ∃ u ∈ U, h * u * h⁻¹ ≠ u := by
  have hdet : (h : Matrix (Fin 3) (Fin 3) F).det = 1 := Matrix.SpecialLinearGroup.det_coe h
  have hc3 : c ^ 3 = 1 := by
    have h' := congrArg Matrix.det hc
    rw [Matrix.det_pow, hdet, one_pow, Matrix.det_smul, Matrix.det_one, mul_one] at h'
    simpa using h'.symm
  by_cases hcube : ∃ d : F, d ^ 3 = c
  · obtain ⟨d, hd⟩ := hcube
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [← hd] at hc3
      norm_num at hc3
    obtain ⟨l, m, hlm, hl3, hm3, hdl, hdm⟩ :=
      two_eigen_of_cube (H := (h : Matrix (Fin 3) (Fin 3) F)) hω hd0 (by rw [hd]; exact hc) hns
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdl
    obtain ⟨f, hf0, hf⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdm
    have hv' : (h : Matrix (Fin 3) (Fin 3) F) *ᵥ v = l • v := by
      have h' := hv
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h'
      exact sub_eq_zero.mp h'
    have hf' : f ᵥ* (h : Matrix (Fin 3) (Fin 3) F) = m • f := by
      have h' := hf
      rw [Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_one] at h'
      exact sub_eq_zero.mp h'
    exact four_group_of_eigen hω h hlm (hl3.trans hm3.symm) hv0 hv' hf0 hf'
  · exact (noncube_false (H := (h : Matrix (Fin 3) (Fin 3) F)) hdet hc hc3 hns hcube).elim

end CFSG.RankThree.PartTwo.Sec21.Hering214
