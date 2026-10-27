module

public import CFSG.OddTranspositions.PartThree.Twelve.EightTriangle
public import CFSG.ClassicalGroups.Orthogonal.Derived
import CFSG.OddTranspositions.PartThree.Twelve.EightModel
import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockOrth
import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Additive
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.ClassicalGroups.Unitary CFSG.ClassicalGroups.Orthogonal QuadraticMap

theorem exists_orthogonal_value_one {K : Type} [Field K] [Finite K] [CharP K 2]
    {Q₀ : QuadraticForm K (Fin 4 → K)} {y₀ : Fin 4 → K} (hy₀ : Q₀ y₀ = 1) :
    ∃ z : Fin 4 → K, Q₀ z = 1 ∧ polar Q₀ z y₀ = 0 ∧ z ≠ y₀ := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hy₀0 : y₀ ≠ 0 := fun h => by simp [h] at hy₀
  let φ : (Fin 4 → K) →ₗ[K] K := (polarBilin Q₀).flip y₀
  have hφ : ∀ w, φ w = polar Q₀ w y₀ := fun w => by simp [φ]
  have hker : ¬ LinearMap.ker φ ≤ K ∙ y₀ := by
    intro hle
    have h1 := Submodule.finrank_mono hle
    have h3 := LinearMap.finrank_range_add_finrank_ker φ
    have h4 : Module.finrank K (LinearMap.range φ) ≤ 1 :=
      (Submodule.finrank_le _).trans (by simp)
    rw [finrank_span_singleton hy₀0] at h1
    simp only [Module.finrank_fin_fun] at h3
    omega
  obtain ⟨w, hw, hwy⟩ := SetLike.not_le_iff_exists.1 hker
  have hwy₀ : polar Q₀ w y₀ = 0 := by rw [← hφ]; exact LinearMap.mem_ker.1 hw
  obtain ⟨α, hα⟩ := surjective_frobenius K 2 (1 + Q₀ w)
  rw [frobenius_def] at hα
  have hself : polar Q₀ y₀ y₀ = 0 := by rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  refine ⟨w + α • y₀, ?_, ?_, ?_⟩
  · rw [QuadraticMap.map_add Q₀, QuadraticMap.map_smul, polar_smul_right, hy₀, hwy₀, smul_eq_mul,
      smul_eq_mul]
    linear_combination hα + Q₀ w * h2
  · rw [polar_add_left, polar_smul_left, hwy₀, hself, smul_zero, add_zero]
  · intro h
    apply hwy
    rw [eq_sub_of_add_eq h]
    exact Submodule.sub_mem _ (Submodule.mem_span_singleton_self y₀)
      (Submodule.smul_mem _ α (Submodule.mem_span_singleton_self y₀))

theorem exists_aux_triple {K : Type} [Field K] [CharP K 2] {Q₀ : QuadraticForm K (Fin 4 → K)}
    (hQ₀ : Q₀.polarBilin.Nondegenerate) (hK4 : 4 ≤ Nat.card K) {y₀ z : Fin 4 → K}
    (hy₀ : Q₀ y₀ = 1) (hz : Q₀ z = 1) (hzy₀ : polar Q₀ z y₀ = 0) (hzy₀' : z ≠ y₀) :
    ∃ y₁ y₂ : Fin 4 → K, Q₀ y₁ = 1 ∧ Q₀ y₂ = 1 ∧ polar Q₀ y₀ y₁ ≠ 0 ∧ polar Q₀ y₀ y₂ ≠ 0 ∧
      polar Q₀ z y₁ = 0 ∧ polar Q₀ z y₂ = 0 ∧ polar Q₀ y₁ y₂ = 0 ∧ y₁ ≠ y₂ := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hself : ∀ v, polar Q₀ v v = 0 := fun v => by
    rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  obtain ⟨l, hl0, hl1⟩ := SiegelRT1.exists_ne_zero_ne_one_of_four_le_card hK4
  have hind := PartFour.linearIndependent_pair_of_map_eq_one hz hy₀ hzy₀'
  obtain ⟨y₁, hy₁z, hy₁y₀, hy₁⟩ := PartFour.exists_polar_eq_map_eq_of_polar_eq_zero hQ₀ hind hzy₀
    (by rw [hz, hy₀]) zero_ne_one 1
  have hy₀y₁ : polar Q₀ y₀ y₁ = 1 := by rw [polar_comm]; exact hy₁y₀
  have hzy₁ : polar Q₀ z y₁ = 0 := by rw [polar_comm]; exact hy₁z
  have hy₀z : polar Q₀ y₀ z = 0 := by rw [polar_comm]; exact hzy₀
  have hy₀y₂ : polar Q₀ y₀ (l • y₁ + (1 + l) • z) = l := by
    rw [polar_add_right, polar_smul_right, polar_smul_right, hy₀y₁, hy₀z, smul_eq_mul,
      smul_eq_mul, mul_one, mul_zero, add_zero]
  refine ⟨y₁, l • y₁ + (1 + l) • z, hy₁, ?_, by rw [hy₀y₁]; exact one_ne_zero,
    by rw [hy₀y₂]; exact hl0, hzy₁, ?_, ?_, ?_⟩
  · rw [QuadraticMap.map_add Q₀, QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left,
      polar_smul_right, hy₁, hz, hy₁z, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    linear_combination (l + l ^ 2) * h2
  · rw [polar_add_right, polar_smul_right, polar_smul_right, hzy₁, hself, smul_zero, smul_zero,
      add_zero]
  · rw [polar_add_right, polar_smul_right, polar_smul_right, hself, hy₁z, smul_zero, smul_zero,
      add_zero]
  · intro h
    apply hl1
    rw [← hy₀y₂, ← h, hy₀y₁]

theorem linearIndependent_three_centres {K F : Type} [Field K] [CharP K 2] [Field F]
    {σ : F ≃+* F} {Q₀ : QuadraticForm K (Fin 4 → K)} (hQ₀ : Q₀.polarBilin.Nondegenerate)
    {a : (Fin 4 → K) → (Fin 4 → F)}
    (hA1 : ∀ y, Q₀ y = 1 → a y ≠ 0 ∧ herm σ (a y) (a y) = 0)
    (hA2 : ∀ x, Q₀ x = 1 → ∀ y, Q₀ y = 1 → (herm σ (a x) (a y) = 0 ↔ polar Q₀ x y = 0))
    {y₀ y₁ y₂ : Fin 4 → K} (hy₀ : Q₀ y₀ = 1) (hy₁ : Q₀ y₁ = 1) (hy₂ : Q₀ y₂ = 1)
    (hy₀₁ : polar Q₀ y₀ y₁ ≠ 0) (hy₁₂ : polar Q₀ y₁ y₂ = 0) (hne : y₁ ≠ y₂) :
    LinearIndependent F ![a y₀, a y₁, a y₂] := by
  classical
  have hind := PartFour.linearIndependent_pair_of_map_eq_one hy₁ hy₂ hne
  obtain ⟨t, hty₁, hty₂, ht⟩ := PartFour.exists_polar_eq_map_eq_of_polar_eq_zero hQ₀ hind hy₁₂
    (by rw [hy₁, hy₂]) one_ne_zero 1
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hrel : g 0 • a y₀ + g 1 • a y₁ + g 2 • a y₂ = 0 := by
    simpa [Fin.sum_univ_three] using hg
  have h10 : herm σ (a y₁) (a y₀) ≠ 0 := fun h =>
    hy₀₁ (by rw [polar_comm]; exact (hA2 y₁ hy₁ y₀ hy₀).1 h)
  have h12 : herm σ (a y₁) (a y₂) = 0 := (hA2 y₁ hy₁ y₂ hy₂).2 hy₁₂
  have ht1 : herm σ (a t) (a y₁) ≠ 0 := fun h =>
    one_ne_zero (hty₁.symm.trans ((hA2 t ht y₁ hy₁).1 h))
  have ht2 : herm σ (a t) (a y₂) = 0 := (hA2 t ht y₂ hy₂).2 hty₂
  have e1 := congrArg (herm σ (a y₁)) hrel
  simp only [herm_add_right, herm_smul_right, herm_zero_right, (hA1 y₁ hy₁).2, h12, mul_zero,
    add_zero] at e1
  have hg0 : g 0 = 0 := (mul_eq_zero.1 e1).resolve_right h10
  have et := congrArg (herm σ (a t)) hrel
  simp only [herm_add_right, herm_smul_right, herm_zero_right, ht2, hg0, zero_mul, mul_zero,
    zero_add, add_zero] at et
  have hg1 : g 1 = 0 := (mul_eq_zero.1 et).resolve_right ht1
  simp only [hg0, hg1, zero_smul, zero_add] at hrel
  have hg2 : g 2 = 0 := (smul_eq_zero.1 hrel).resolve_right (hA1 y₂ hy₂).1
  intro i
  fin_cases i
  exacts [hg0, hg1, hg2]

theorem exists_fourth_centre {K F : Type} [Field K] [CharP K 2] [Field F] {σ : F ≃+* F}
    {Q₀ : QuadraticForm K (Fin 4 → K)} (hQ₀ : Q₀.polarBilin.Nondegenerate)
    (hK4 : 4 ≤ Nat.card K) {a : (Fin 4 → K) → (Fin 4 → F)}
    (hA1 : ∀ y, Q₀ y = 1 → a y ≠ 0 ∧ herm σ (a y) (a y) = 0)
    (hA2 : ∀ x, Q₀ x = 1 → ∀ y, Q₀ y = 1 → (herm σ (a x) (a y) = 0 ↔ polar Q₀ x y = 0))
    {y₀ y₁ y₂ z : Fin 4 → K} (hy₀ : Q₀ y₀ = 1) (hy₁ : Q₀ y₁ = 1) (hy₂ : Q₀ y₂ = 1)
    (hz : Q₀ z = 1) (hzy₀ : polar Q₀ z y₀ = 0) (hzy₀' : z ≠ y₀) (hy₀₁ : polar Q₀ y₀ y₁ ≠ 0)
    (hzy₁ : polar Q₀ z y₁ = 0) (hzy₂ : polar Q₀ z y₂ = 0) (hy₁₂ : polar Q₀ y₁ y₂ = 0)
    (hne : y₁ ≠ y₂) :
    ∃ y₃ : Fin 4 → K, Q₀ y₃ = 1 ∧ polar Q₀ y₀ y₃ ≠ 0 ∧ polar Q₀ z y₃ ≠ 0 ∧
      LinearIndependent F ![a y₀, a y₁, a y₂, a y₃] := by
  classical
  obtain ⟨l, hl0, hl1⟩ := SiegelRT1.exists_ne_zero_ne_one_of_four_le_card hK4
  have hy₀z : polar Q₀ y₀ z = 0 := by rw [polar_comm]; exact hzy₀
  have hind := PartFour.linearIndependent_pair_of_map_eq_one hy₀ hz (Ne.symm hzy₀')
  obtain ⟨y₃, hy₃y₀, hy₃z, hy₃⟩ := PartFour.exists_polar_eq_map_eq_of_polar_eq_zero hQ₀ hind hy₀z
    (by rw [hy₀, hz]) (Ne.symm hl1) 1
  have h3 := linearIndependent_three_centres hQ₀ hA1 hA2 hy₀ hy₁ hy₂ hy₀₁ hy₁₂ hne
  refine ⟨y₃, hy₃, by rw [polar_comm, hy₃y₀]; exact one_ne_zero,
    by rw [polar_comm, hy₃z]; exact hl0, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hrel : g 0 • a y₀ + g 1 • a y₁ + g 2 • a y₂ + g 3 • a y₃ = 0 := by
    simpa [Fin.sum_univ_four] using hg
  have hz0 : herm σ (a z) (a y₀) = 0 := (hA2 z hz y₀ hy₀).2 hzy₀
  have hz1 : herm σ (a z) (a y₁) = 0 := (hA2 z hz y₁ hy₁).2 hzy₁
  have hz2 : herm σ (a z) (a y₂) = 0 := (hA2 z hz y₂ hy₂).2 hzy₂
  have hz3 : herm σ (a z) (a y₃) ≠ 0 := fun h =>
    hl0 (by rw [← hy₃z, polar_comm]; exact (hA2 z hz y₃ hy₃).1 h)
  have e := congrArg (herm σ (a z)) hrel
  simp only [herm_add_right, herm_smul_right, herm_zero_right, hz0, hz1, hz2, mul_zero,
    zero_add] at e
  have hg3 : g 3 = 0 := (mul_eq_zero.1 e).resolve_right hz3
  simp only [hg3, zero_smul, add_zero] at hrel
  have h012 := Fintype.linearIndependent_iff.1 h3 ![g 0, g 1, g 2]
    (by simpa [Fin.sum_univ_three] using hrel)
  have hg0 : g 0 = 0 := by simpa using h012 0
  have hg1 : g 1 = 0 := by simpa using h012 1
  have hg2 : g 2 = 0 := by simpa using h012 2
  intro i
  fin_cases i
  exacts [hg0, hg1, hg2, hg3]

theorem exists_norm_one_mul_fixed {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}
    (hinv : ∀ c, σ (σ c) = c) {ζ : F} (hζ : ζ ≠ 0) :
    ∃ μ : F, σ μ * μ = 1 ∧ σ (μ * ζ) = μ * ζ := by
  obtain ⟨μ, hμ⟩ := surjective_frobenius F 2 (σ ζ / ζ)
  rw [frobenius_def] at hμ
  have hσζ : σ ζ ≠ 0 := (map_ne_zero σ).2 hζ
  have hsq : (σ μ * μ) ^ 2 = 1 := by
    rw [mul_pow, ← map_pow, hμ, map_div₀, hinv]
    field_simp
  have hnorm : σ μ * μ = 1 := by
    have h0 : (σ μ * μ + 1) ^ 2 = 0 := by
      have e : (σ μ * μ + 1) ^ 2 = (σ μ * μ) ^ 2 + 1 + (2 : F) * (σ μ * μ) := by ring
      rw [e, hsq, CharTwo.two_eq_zero, zero_mul, add_zero, CharTwo.add_self_eq_zero]
    exact CharTwo.add_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)
  refine ⟨μ, hnorm, frobenius_inj F 2 ?_⟩
  have h1 : σ ζ / ζ * ζ ^ 2 = σ ζ * ζ := by
    field_simp
  simp only [frobenius_def]
  rw [← map_pow, mul_pow, hμ, h1, map_mul, hinv, mul_comm]

theorem exists_fixed_coords_of_herm_fixed {F : Type} [Field F] {σ : F ≃+* F}
    {e : Fin 4 → Fin 4 → F} (hGram : ∀ i j, σ (herm σ (e i) (e j)) = herm σ (e i) (e j))
    (he : (Matrix.of e).det ≠ 0) {v : Fin 4 → F}
    (hv : ∀ i, σ (herm σ (e i) v) = herm σ (e i) v) :
    ∃ c : Fin 4 → F, (∀ i, σ (c i) = c i) ∧ v = ∑ i, c i • e i := by
  classical
  set E : Matrix (Fin 4) (Fin 4) F := Matrix.of e
  have hEu : IsUnit E.det := isUnit_iff_ne_zero.2 he
  set c : Fin 4 → F := Matrix.vecMul v E⁻¹ with hc
  have hsum : ∀ w : Fin 4 → F, ∑ i, w i • e i = Matrix.vecMul w E := by
    intro w
    ext j
    simp [Matrix.vecMul, dotProduct, E, Finset.sum_apply]
  have hv' : v = ∑ i, c i • e i := by
    rw [hsum, hc, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hEu, Matrix.vecMul_one]
  set G : Matrix (Fin 4) (Fin 4) F := Matrix.of fun i k => herm σ (e i) (e k)
  have hherm : ∀ w : Fin 4 → F, ∀ i, herm σ (e i) (∑ k, w k • e k) = (G.mulVec w) i := by
    intro w i
    simp only [herm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, G,
      Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  have hG : G = (σ.toRingHom.mapMatrix E) * E.transpose := by
    ext i k
    simp [G, herm, E, Matrix.mul_apply]
  have hGdet : IsUnit G.det := by
    rw [hG, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 (mul_ne_zero (by simpa using he) he)
  have hGinj : Function.Injective G.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det G).2 hGdet)
  refine ⟨c, fun i => ?_, hv'⟩
  have key : G.mulVec (fun k => σ (c k)) = G.mulVec c := by
    ext i
    have h1 := hv i
    rw [hv', hherm] at h1
    rw [← h1]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, G, Matrix.of_apply, hGram]
  exact congrFun (hGinj key) i

theorem eq_one_of_smul_mem_fixedSpan {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}
    {e : Fin 4 → Fin 4 → F} (he : (Matrix.of e).det ≠ 0) {v : Fin 4 → F} (hv : v ≠ 0) {μ : F}
    (hμ : σ μ * μ = 1)
    (hmem : ∃ c : Fin 4 → F, (∀ i, σ (c i) = c i) ∧ μ • v = ∑ i, c i • e i)
    (hone : ∃ c : Fin 4 → F, (∀ i, σ (c i) = c i) ∧ v = ∑ i, c i • e i) :
    μ = 1 := by
  classical
  obtain ⟨c', hc'fix, hc'⟩ := hmem
  obtain ⟨c, hcfix, hc⟩ := hone
  have hsum : ∀ w : Fin 4 → F, ∑ i, w i • e i = (Matrix.of e).vecMul w := by
    intro w
    ext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
  have hinj : Function.Injective (Matrix.of e).vecMul :=
    Matrix.vecMul_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 he))
  have hcoord : c' = μ • c := by
    apply hinj
    beta_reduce
    rw [← hsum, ← hsum, ← hc', hc, Finset.smul_sum]
    simp [smul_smul]
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra! h
    exact hv (by simp [hc, h])
  have hμfix : σ μ = μ := by
    have h2 := hc'fix i
    rw [hcoord, Pi.smul_apply, smul_eq_mul, map_mul, hcfix i] at h2
    exact mul_right_cancel₀ hi h2
  exact eq_one_of_fix_of_norm hμfix hμ

theorem exists_normalized_centres {K F : Type} [Field K] [Finite K] [CharP K 2] [Field F]
    [Finite F] [CharP F 2] {σ : F ≃+* F} (hinv : ∀ c, σ (σ c) = c)
    {Q₀ : QuadraticForm K (Fin 4 → K)} (hK4 : 4 ≤ Nat.card K) (hQ₀ : Q₀.polarBilin.Nondegenerate)
    {a : (Fin 4 → K) → (Fin 4 → F)}
    (hA1 : ∀ y, Q₀ y = 1 → a y ≠ 0 ∧ herm σ (a y) (a y) = 0)
    (hA2 : ∀ x, Q₀ x = 1 → ∀ y, Q₀ y = 1 → (herm σ (a x) (a y) = 0 ↔ polar Q₀ x y = 0))
    {y₀ : Fin 4 → K} (hy₀ : Q₀ y₀ = 1) :
    ∃ a' : (Fin 4 → K) → (Fin 4 → F),
      (∀ y, Q₀ y = 1 → ∃ μ : F, σ μ * μ = 1 ∧ a' y = μ • a y) ∧
      ∀ y, Q₀ y = 1 → ∀ y', Q₀ y' = 1 → (y = y₀ ∨ polar Q₀ y₀ y ≠ 0) →
        (y' = y₀ ∨ polar Q₀ y₀ y' ≠ 0) → σ (herm σ (a' y) (a' y')) = herm σ (a' y) (a' y') := by
  classical
  have hP : ∀ y, ∃ μ : F, σ μ * μ = 1 ∧ (Q₀ y = 1 → polar Q₀ y₀ y ≠ 0 →
      σ (μ * herm σ (a y₀) (a y)) = μ * herm σ (a y₀) (a y)) ∧ (polar Q₀ y₀ y = 0 → μ = 1) := by
    intro y
    by_cases hy : Q₀ y = 1 ∧ polar Q₀ y₀ y ≠ 0
    · have hζ : herm σ (a y₀) (a y) ≠ 0 := fun h => hy.2 ((hA2 y₀ hy₀ y hy.1).1 h)
      obtain ⟨μ, hμ, hfix⟩ := exists_norm_one_mul_fixed hinv hζ
      exact ⟨μ, hμ, fun _ _ => hfix, fun h => absurd h hy.2⟩
    · exact ⟨1, by simp, fun h1 h2 => absurd ⟨h1, h2⟩ hy, fun _ => rfl⟩
  choose μ hμ hμfix hμ1 using hP
  have hself : polar Q₀ y₀ y₀ = 0 := by rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hμ₀ : μ y₀ = 1 := hμ1 y₀ hself
  have hX : ∀ y, Q₀ y = 1 → (y = y₀ ∨ polar Q₀ y₀ y ≠ 0) →
      σ (herm σ (μ y₀ • a y₀) (μ y • a y)) = herm σ (μ y₀ • a y₀) (μ y • a y) := by
    rintro y hy (h | hyn)
    · rw [h]
      exact herm_self_fixed σ hinv _
    · rw [hμ₀, one_smul, herm_smul_right]
      exact hμfix y hy hyn
  refine ⟨fun y => μ y • a y, fun y _ => ⟨μ y, hμ y, rfl⟩, ?_⟩
  rintro y hy y' hy' (h | hyn) hyy'
  · rw [h]
    exact hX y' hy' hyy'
  rcases hyy' with h | hyn'
  · rw [h, herm_conj σ hinv (μ y₀ • a y₀) (μ y • a y), hinv]
    exact (hX y hy (Or.inr hyn)).symm
  have hζ : herm σ (a y₀) (a y) ≠ 0 := fun h => hyn ((hA2 y₀ hy₀ y hy).1 h)
  have hζ' : herm σ (a y₀) (a y') ≠ 0 := fun h => hyn' ((hA2 y₀ hy₀ y' hy').1 h)
  have f1 := hμfix y hy hyn
  have f2 := hμfix y' hy' hyn'
  have tri := triangle_fixed hinv hK4 hQ₀ hA1 hA2 hy₀ hy hy'
  simp only [triangleProduct] at tri
  rw [herm_conj σ hinv (a y₀) (a y')] at tri
  simp only [map_mul, hinv] at f1 f2 tri
  simp only [herm_smul_left, herm_smul_right, map_mul, hinv]
  have key : herm σ (a y₀) (a y) * herm σ (a y₀) (a y') *
      (μ y * (σ (μ y') * σ (herm σ (a y) (a y'))) -
        σ (μ y) * (μ y' * herm σ (a y) (a y'))) = 0 := by
    linear_combination (-(herm σ (a y₀) (a y') * σ (μ y') * σ (herm σ (a y) (a y')))) * f1 +
      (σ (μ y) * σ (μ y')) * tri + (σ (μ y) * herm σ (a y₀) (a y) * herm σ (a y) (a y')) * f2
  have hk := sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_left (mul_ne_zero hζ hζ'))
  linear_combination hk

open Matrix in
private theorem exists_fixed_smul_of_dot_eq_zero {F : Type} [Field F] (σ : F →+* F)
    (c : Fin 3 → Fin 4 → F) (hc : LinearIndependent F c) (hfix : ∀ k i, σ (c k i) = c k i)
    (ℓ : Fin 4 → F) (hℓ : ∀ k, ∑ i, c k i * ℓ i = 0) :
    ∃ m : Fin 4 → F, (∀ i, σ (m i) = m i) ∧ ∃ ζ : F, ℓ = ζ • m := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin 4, Pi.single j (1 : F) ∉ Submodule.span F (Set.range c) := by
    by_contra! h
    have htop : ⊤ ≤ Submodule.span F (Set.range c) := by
      rw [← (Pi.basisFun F (Fin 4)).span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simpa using h i
    have h3 := Module.finrank_eq_card_basis (Module.Basis.mk hc htop)
    simp at h3
  set M : Matrix (Fin 4) (Fin 4) F := Matrix.of (Fin.snoc c (Pi.single j 1))
  have hM : IsUnit M := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    exact linearIndependent_finSnoc.2 ⟨hc, hj⟩
  have hdet : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M).1 hM).ne_zero
  have hMfix : σ.mapMatrix M = M := by
    ext a b
    refine Fin.lastCases ?_ (fun k => ?_) a
    · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, M, Matrix.of_apply, Fin.snoc_last,
        Pi.single_apply]
      split_ifs <;> simp
    · simp [M, hfix]
  set m : Fin 4 → F := fun i => M.adjugate i (Fin.last 3)
  have hmfix : ∀ i, σ (m i) = m i := by
    intro i
    have := congrFun (congrFun (RingHom.map_adjugate σ M) i) (Fin.last 3)
    rw [hMfix] at this
    simpa [m] using this
  have hMl : M *ᵥ ℓ = Pi.single (Fin.last 3) (ℓ j) := by
    ext a
    refine Fin.lastCases ?_ (fun k => ?_) a
    · rw [Pi.single_eq_same]
      simp only [M, Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.snoc_last]
      simp [Pi.single_apply]
    · rw [Pi.single_eq_of_ne (Fin.castSucc_ne_last k)]
      simpa only [M, Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.snoc_castSucc] using hℓ k
  have key : M.det • ℓ = ℓ j • m := by
    have h1 : M.adjugate *ᵥ (M *ᵥ ℓ) = M.det • ℓ := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [← h1, hMl]
    ext i
    simp [m, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
  refine ⟨m, hmfix, ℓ j / M.det, ?_⟩
  ext i
  have := congrFun key i
  simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
  field_simp
  linear_combination this

theorem exists_norm_one_smul_fixedSpan {K F : Type} [Field K] [CharP K 2] [Field F] [Finite F]
    [CharP F 2] {σ : F ≃+* F} (hinv : ∀ c, σ (σ c) = c) {Q₀ : QuadraticForm K (Fin 4 → K)}
    (hQ₀ : Q₀.polarBilin.Nondegenerate) (hK4 : 4 ≤ Nat.card K) {a : (Fin 4 → K) → (Fin 4 → F)}
    (hA1 : ∀ y, Q₀ y = 1 → a y ≠ 0 ∧ herm σ (a y) (a y) = 0)
    (hA2 : ∀ x, Q₀ x = 1 → ∀ y, Q₀ y = 1 → (herm σ (a x) (a y) = 0 ↔ polar Q₀ x y = 0))
    {y₀ : Fin 4 → K} (hy₀ : Q₀ y₀ = 1)
    (hfix : ∀ y, Q₀ y = 1 → ∀ y', Q₀ y' = 1 → (y = y₀ ∨ polar Q₀ y₀ y ≠ 0) →
      (y' = y₀ ∨ polar Q₀ y₀ y' ≠ 0) → σ (herm σ (a y) (a y')) = herm σ (a y) (a y'))
    {e : Fin 4 → Fin 4 → K} (he : ∀ i, Q₀ (e i) = 1)
    (he₀ : ∀ i, e i = y₀ ∨ polar Q₀ y₀ (e i) ≠ 0)
    (hdet : (Matrix.of fun i => a (e i)).det ≠ 0) {y : Fin 4 → K} (hy : Q₀ y = 1) :
    ∃ μ : F, σ μ * μ = 1 ∧ ∃ c : Fin 4 → F, (∀ i, σ (c i) = c i) ∧
      μ • a y = ∑ i, c i • a (e i) := by
  classical
  have hGram : ∀ i j, σ (herm σ (a (e i)) (a (e j))) = herm σ (a (e i)) (a (e j)) :=
    fun i j => hfix (e i) (he i) (e j) (he j) (he₀ i) (he₀ j)
  have hnear : ∀ u, Q₀ u = 1 → (u = y₀ ∨ polar Q₀ y₀ u ≠ 0) →
      ∃ c : Fin 4 → F, (∀ i, σ (c i) = c i) ∧ a u = ∑ i, c i • a (e i) :=
    fun u hu hu₀ => exists_fixed_coords_of_herm_fixed hGram hdet
      fun i => hfix (e i) (he i) u hu (he₀ i) hu₀
  by_cases hy₀y : y = y₀ ∨ polar Q₀ y₀ y ≠ 0
  · obtain ⟨c, hc, hcy⟩ := hnear y hy hy₀y
    exact ⟨1, by simp, c, hc, by rw [one_smul]; exact hcy⟩
  have hne : y ≠ y₀ := fun h => hy₀y (Or.inl h)
  have hpol : polar Q₀ y₀ y = 0 := not_not.1 fun h => hy₀y (Or.inr h)
  have hyy₀ : polar Q₀ y y₀ = 0 := by rw [polar_comm]; exact hpol
  obtain ⟨y₁, y₂, hy₁, hy₂, hy₀₁, hy₀₂, hyy₁, hyy₂, hy₁₂, hne₁₂⟩ :=
    exists_aux_triple hQ₀ hK4 hy₀ hy hyy₀ hne
  obtain ⟨c₀, hc₀, hc₀y⟩ := hnear y₀ hy₀ (Or.inl rfl)
  obtain ⟨c₁, hc₁, hc₁y⟩ := hnear y₁ hy₁ (Or.inr hy₀₁)
  obtain ⟨c₂, hc₂, hc₂y⟩ := hnear y₂ hy₂ (Or.inr hy₀₂)
  have h3 := linearIndependent_three_centres hQ₀ hA1 hA2 hy₀ hy₁ hy₂ hy₀₁ hy₁₂ hne₁₂
  have hC : LinearIndependent F ![c₀, c₁, c₂] := by
    refine LinearIndependent.of_comp (Fintype.linearCombination F fun i => a (e i)) ?_
    convert h3 using 1
    funext k
    fin_cases k <;> simp [Fintype.linearCombination_apply, hc₀y, hc₁y, hc₂y]
  have hsl : ∀ (f : Fin 4 → Fin 4 → F) (w : Fin 4 → F),
      herm σ (∑ i, f i) w = ∑ i, herm σ (f i) w := by
    intro f w
    simp only [herm, Finset.sum_apply, map_sum, Finset.sum_mul]
    exact Finset.sum_comm
  have hpair : ∀ c : Fin 4 → F, (∀ i, σ (c i) = c i) →
      herm σ (∑ i, c i • a (e i)) (a y) = ∑ i, c i * herm σ (a (e i)) (a y) := by
    intro c hc
    rw [hsl]
    exact Finset.sum_congr rfl fun i _ => by rw [herm_smul_left, hc]
  have e0 : ∑ i, c₀ i * herm σ (a (e i)) (a y) = 0 := by
    rw [← hpair c₀ hc₀, ← hc₀y]
    exact (hA2 y₀ hy₀ y hy).2 hpol
  have e1 : ∑ i, c₁ i * herm σ (a (e i)) (a y) = 0 := by
    rw [← hpair c₁ hc₁, ← hc₁y]
    exact (hA2 y₁ hy₁ y hy).2 (by rw [polar_comm]; exact hyy₁)
  have e2 : ∑ i, c₂ i * herm σ (a (e i)) (a y) = 0 := by
    rw [← hpair c₂ hc₂, ← hc₂y]
    exact (hA2 y₂ hy₂ y hy).2 (by rw [polar_comm]; exact hyy₂)
  have hℓ : ∀ k, ∑ i, (![c₀, c₁, c₂] : Fin 3 → Fin 4 → F) k i * herm σ (a (e i)) (a y) = 0 := by
    intro k
    fin_cases k
    exacts [e0, e1, e2]
  obtain ⟨m, hm, ζ, hζm⟩ := exists_fixed_smul_of_dot_eq_zero (σ : F →+* F) ![c₀, c₁, c₂] hC
    (fun k i => by fin_cases k <;> simp [hc₀, hc₁, hc₂]) (fun i => herm σ (a (e i)) (a y)) hℓ
  have hm' : ∀ i, σ (m i) = m i := fun i => by simpa using hm i
  have hℓi : ∀ i, herm σ (a (e i)) (a y) = ζ * m i := fun i => by simpa using congrFun hζm i
  have hζ : ζ ≠ 0 := by
    rintro rfl
    have hzero : ∀ i, herm σ (a y) (a (e i)) = 0 := fun i =>
      herm_eq_zero_comm σ hinv (by rw [hℓi, zero_mul])
    have hli : LinearIndependent F fun i => a (e i) :=
      Matrix.linearIndependent_rows_iff_isUnit.2
        ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))
    have htop := hli.span_eq_top_of_card_eq_finrank' (by simp)
    apply (hA1 y hy).1
    refine eq_zero_of_herm σ fun v => ?_
    have hle : Submodule.span F (Set.range fun i => a (e i)) ≤ LinearMap.ker (hermL σ (a y)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simpa using hzero i
    have hv : v ∈ Submodule.span F (Set.range fun i => a (e i)) := by
      rw [htop]
      exact Submodule.mem_top
    simpa using hle hv
  obtain ⟨μ, hμ, hμζ⟩ := exists_norm_one_mul_fixed hinv hζ
  obtain ⟨c, hc, hcy⟩ := exists_fixed_coords_of_herm_fixed hGram hdet (v := μ • a y) fun i => by
    rw [herm_smul_right, hℓi, ← mul_assoc, map_mul, hμζ, hm' i]
  exact ⟨μ, hμ, c, hc, hcy⟩

theorem reflect_eq_add_smul_of_mem_fixedSpan {K F : Type} [Field K] [Field F] [CharP F 2]
    {σ : F ≃+* F} {Q₀ : QuadraticForm K (Fin 4 → K)} {a : (Fin 4 → K) → (Fin 4 → F)}
    {e : Fin 4 → Fin 4 → F} (hGram : ∀ i j, σ (herm σ (e i) (e j)) = herm σ (e i) (e j))
    (he : (Matrix.of e).det ≠ 0) (hA1 : ∀ y, Q₀ y = 1 → a y ≠ 0)
    (hmem : ∀ y, Q₀ y = 1 → ∃ c : Fin 4 → F, (∀ i, σ (c i) = c i) ∧ a y = ∑ i, c i • e i)
    {x y : Fin 4 → K} (hx : Q₀ x = 1) (hy : Q₀ y = 1) {μ : F} (hμ : σ μ * μ = 1)
    (hA3 : a (reflect Q₀ x y) = μ • (a y + herm σ (a x) (a y) • a x)) :
    a (reflect Q₀ x y) = a y + herm σ (a x) (a y) • a x := by
  classical
  have hr : Q₀ (reflect Q₀ x y) = 1 := by
    rw [map_of_mem (reflect_mem_orthogonalGroup Q₀ x) y, hy]
  have hsl : ∀ (f : Fin 4 → Fin 4 → F) (w : Fin 4 → F),
      herm σ (∑ i, f i) w = ∑ i, herm σ (f i) w := by
    intro f w
    simp only [herm, Finset.sum_apply, map_sum, Finset.sum_mul]
    exact Finset.sum_comm
  have hsr : ∀ (v : Fin 4 → F) (f : Fin 4 → Fin 4 → F),
      herm σ v (∑ j, f j) = ∑ j, herm σ v (f j) := by
    intro v f
    simp only [herm, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_comm
  have hexp : ∀ u w : Fin 4 → F, herm σ (∑ i, u i • e i) (∑ j, w j • e j) =
      ∑ i, ∑ j, σ (u i) * w j * herm σ (e i) (e j) := by
    intro u w
    rw [hsl]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [herm_smul_left, hsr, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [herm_smul_right]
    ring
  obtain ⟨c, hcfix, hc⟩ := hmem x hx
  obtain ⟨d, hdfix, hd⟩ := hmem y hy
  obtain ⟨r, hrfix, hrc⟩ := hmem _ hr
  have hhfix : σ (herm σ (a x) (a y)) = herm σ (a x) (a y) := by
    rw [hc, hd, hexp]
    simp only [map_sum, map_mul, hcfix, hdfix, hGram]
  set h := herm σ (a x) (a y) with hh
  have hv : a y + h • a x = ∑ i, (d i + h * c i) • e i := by
    rw [hc, hd, Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [add_smul, mul_smul]
  have hne : a y + h • a x ≠ 0 := by
    intro h0
    exact hA1 _ hr (by rw [hA3, h0, smul_zero])
  have hμ1 : μ = 1 := by
    refine eq_one_of_smul_mem_fixedSpan he hne hμ ⟨r, hrfix, by rw [← hA3]; exact hrc⟩
      ⟨fun i => d i + h * c i, fun i => ?_, hv⟩
    rw [map_add, map_mul, hdfix, hcfix, hhfix]
  rw [hA3, hμ1, one_smul]

private theorem exists_norm_one_reflect_of_norm_one_smul {F : Type} [Field F] {σ : F ≃+* F}
    (hinv : ∀ c, σ (σ c) = c) {u₁ u₂ u₃ v₁ v₂ v₃ : Fin 4 → F} {ρ₁ ρ₂ ρ₃ μ : F}
    (h₁ : σ ρ₁ * ρ₁ = 1) (h₂ : σ ρ₂ * ρ₂ = 1) (h₃ : σ ρ₃ * ρ₃ = 1) (hμ : σ μ * μ = 1)
    (hv₁ : v₁ = ρ₁ • u₁) (hv₂ : v₂ = ρ₂ • u₂) (hv₃ : v₃ = ρ₃ • u₃)
    (hu₃ : u₃ = μ • (u₂ + herm σ u₁ u₂ • u₁)) :
    ∃ κ : F, σ κ * κ = 1 ∧ v₃ = κ • (v₂ + herm σ v₁ v₂ • v₁) := by
  refine ⟨ρ₃ * μ * σ ρ₂, ?_, ?_⟩
  · simp only [map_mul, hinv]
    linear_combination (σ μ * μ * (σ ρ₂ * ρ₂)) * h₃ + (σ ρ₂ * ρ₂) * hμ + h₂
  · simp only [hv₁, hv₂, hv₃, hu₃, herm_smul_left, herm_smul_right, smul_add, smul_smul]
    congr 1
    · congr 1
      linear_combination (-(ρ₃ * μ)) * h₂
    · congr 1
      linear_combination (-(ρ₃ * μ * herm σ u₁ u₂ * (σ ρ₁ * ρ₁))) * h₂ -
        (ρ₃ * μ * herm σ u₁ u₂) * h₁

theorem exists_fixedSpan_centres {K F : Type} [Field K] [Finite K] [CharP K 2] [Field F]
    [Finite F] [CharP F 2] {σ : F ≃+* F} (hinv : ∀ c, σ (σ c) = c)
    {Q₀ : QuadraticForm K (Fin 4 → K)} (hK4 : 4 ≤ Nat.card K) (hQ₀ : Q₀.polarBilin.Nondegenerate)
    {a : (Fin 4 → K) → (Fin 4 → F)}
    (hA1 : ∀ y, Q₀ y = 1 → a y ≠ 0 ∧ herm σ (a y) (a y) = 0)
    (hA2 : ∀ x, Q₀ x = 1 → ∀ y, Q₀ y = 1 → (herm σ (a x) (a y) = 0 ↔ polar Q₀ x y = 0))
    (hA3 : ∀ x, Q₀ x = 1 → ∀ y, Q₀ y = 1 → ∃ μ : F, σ μ * μ = 1 ∧
      a (reflect Q₀ x y) = μ • (a y + herm σ (a x) (a y) • a x)) :
    ∃ (e : Fin 4 → Fin 4 → F) (a' : (Fin 4 → K) → (Fin 4 → F)),
      (∀ i j, σ (herm σ (e i) (e j)) = herm σ (e i) (e j)) ∧ (∀ i, herm σ (e i) (e i) = 0) ∧
      (Matrix.of e).det ≠ 0 ∧ (∀ y, Q₀ y = 1 → ∃ μ : F, σ μ * μ = 1 ∧ a' y = μ • a y) ∧
      (∀ y, Q₀ y = 1 → ∃ c : Fin 4 → F, (∀ i, σ (c i) = c i) ∧ a' y = ∑ i, c i • e i) ∧
      ∀ x, Q₀ x = 1 → ∀ y, Q₀ y = 1 →
        a' (reflect Q₀ x y) = a' y + herm σ (a' x) (a' y) • a' x := by
  classical
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Fin 4 → K, Q₀ y₀ = 1 := by
    obtain ⟨v, hv⟩ : ∃ v, Q₀ v ≠ 0 := by
      by_contra! h
      have h0 : (Pi.single 0 1 : Fin 4 → K) = 0 := hQ₀.1 _ fun w => by
        simp [polarBilin_apply_apply, polar, h]
      simpa using congrFun h0 0
    obtain ⟨s, hs⟩ := surjective_frobenius K 2 (Q₀ v)
    rw [frobenius_def] at hs
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact hv (by rw [← hs]; ring)
    exact ⟨s⁻¹ • v, by rw [QuadraticMap.map_smul, ← hs, smul_eq_mul]; field_simp⟩
  have hn : ∀ {l ν : F}, σ l * l = 1 → σ ν * ν = 1 → σ (l * ν) * (l * ν) = 1 := by
    intro l ν h1 h2
    rw [map_mul]
    linear_combination (σ ν * ν) * h1 + h2
  obtain ⟨a', ha'μ, hfix'⟩ := exists_normalized_centres hinv hK4 hQ₀ hA1 hA2 hy₀
  have hA1' : ∀ y, Q₀ y = 1 → a' y ≠ 0 ∧ herm σ (a' y) (a' y) = 0 := by
    intro y hy
    obtain ⟨μ, hμ, hμy⟩ := ha'μ y hy
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      simp at hμ
    rw [hμy]
    exact ⟨smul_ne_zero hμ0 (hA1 y hy).1, by
      rw [herm_smul_left, herm_smul_right, (hA1 y hy).2, mul_zero, mul_zero]⟩
  have hA2' : ∀ x, Q₀ x = 1 → ∀ y, Q₀ y = 1 →
      (herm σ (a' x) (a' y) = 0 ↔ polar Q₀ x y = 0) := by
    intro x hx y hy
    obtain ⟨μ, hμ, hμx⟩ := ha'μ x hx
    obtain ⟨ν, hν, hνy⟩ := ha'μ y hy
    rw [hμx, hνy, herm_smul_left, herm_smul_right, ← hA2 x hx y hy]
    have hμ0 : σ μ ≠ 0 := by
      intro h
      simp [h] at hμ
    have hν0 : ν ≠ 0 := by
      rintro rfl
      simp at hν
    constructor
    · intro h
      exact (mul_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hμ0)).resolve_left hν0
    · intro h
      rw [h, mul_zero, mul_zero]
  obtain ⟨z, hz, hzy₀, hzne⟩ := exists_orthogonal_value_one hy₀
  obtain ⟨y₁, y₂, hy₁, hy₂, hy₀₁, hy₀₂, hzy₁, hzy₂, hy₁₂, hne₁₂⟩ :=
    exists_aux_triple hQ₀ hK4 hy₀ hz hzy₀ hzne
  obtain ⟨y₃, hy₃, hy₀₃, -, hli⟩ := exists_fourth_centre hQ₀ hK4 hA1' hA2' hy₀ hy₁ hy₂ hz hzy₀
    hzne hy₀₁ hzy₁ hzy₂ hy₁₂ hne₁₂
  have heK1 : ∀ i, Q₀ (![y₀, y₁, y₂, y₃] i) = 1 := by
    intro i
    fin_cases i
    exacts [hy₀, hy₁, hy₂, hy₃]
  have heK0 : ∀ i, ![y₀, y₁, y₂, y₃] i = y₀ ∨ polar Q₀ y₀ (![y₀, y₁, y₂, y₃] i) ≠ 0 := by
    intro i
    fin_cases i
    exacts [Or.inl rfl, Or.inr hy₀₁, Or.inr hy₀₂, Or.inr hy₀₃]
  have hli' : LinearIndependent F fun i => a' (![y₀, y₁, y₂, y₃] i) := by
    convert hli using 1
    funext i
    fin_cases i <;> rfl
  have hdet : (Matrix.of fun i => a' (![y₀, y₁, y₂, y₃] i)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1
      ((Matrix.linearIndependent_rows_iff_isUnit
        (A := Matrix.of fun i => a' (![y₀, y₁, y₂, y₃] i))).1 hli')).ne_zero
  have hGram : ∀ i j, σ (herm σ (a' (![y₀, y₁, y₂, y₃] i)) (a' (![y₀, y₁, y₂, y₃] j))) =
      herm σ (a' (![y₀, y₁, y₂, y₃] i)) (a' (![y₀, y₁, y₂, y₃] j)) :=
    fun i j => hfix' _ (heK1 i) _ (heK1 j) (heK0 i) (heK0 j)
  have hlv : ∀ y, ∃ l : F, σ l * l = 1 ∧ (Q₀ y = 1 → ∃ c : Fin 4 → F, (∀ i, σ (c i) = c i) ∧
      l • a' y = ∑ i, c i • a' (![y₀, y₁, y₂, y₃] i)) := by
    intro y
    by_cases hy : Q₀ y = 1
    · obtain ⟨l, hl, hc⟩ :=
        exists_norm_one_smul_fixedSpan hinv hQ₀ hK4 hA1' hA2' hy₀ hfix' heK1 heK0 hdet hy
      exact ⟨l, hl, fun _ => hc⟩
    · exact ⟨1, by simp, fun h => absurd h hy⟩
  choose l hl hlc using hlv
  have hA1'' : ∀ y, Q₀ y = 1 → l y • a' y ≠ 0 := by
    intro y hy
    have hl0 : l y ≠ 0 := by
      intro h
      have := hl y
      rw [h, mul_zero] at this
      exact zero_ne_one this
    exact smul_ne_zero hl0 (hA1' y hy).1
  refine ⟨fun i => a' (![y₀, y₁, y₂, y₃] i), fun y => l y • a' y, hGram,
    fun i => (hA1' _ (heK1 i)).2, hdet, ?_, hlc, ?_⟩
  · intro y hy
    obtain ⟨ν, hν, hy'⟩ := ha'μ y hy
    exact ⟨l y * ν, hn (hl y) hν, by beta_reduce; rw [hy', smul_smul]⟩
  · intro x hx y hy
    have hr : Q₀ (reflect Q₀ x y) = 1 := by
      rw [map_of_mem (reflect_mem_orthogonalGroup Q₀ x) y, hy]
    obtain ⟨μ, hμ, hμr⟩ := hA3 x hx y hy
    obtain ⟨νx, hνx, hx'⟩ := ha'μ x hx
    obtain ⟨νy, hνy, hy'⟩ := ha'μ y hy
    obtain ⟨νr, hνr, hr'⟩ := ha'μ _ hr
    obtain ⟨κ, hκ, hκr⟩ := exists_norm_one_reflect_of_norm_one_smul hinv
      (v₁ := l x • a' x) (v₂ := l y • a' y) (v₃ := l (reflect Q₀ x y) • a' (reflect Q₀ x y))
      (hn (hl x) hνx) (hn (hl y) hνy) (hn (hl (reflect Q₀ x y)) hνr) hμ
      (by rw [hx', smul_smul]) (by rw [hy', smul_smul]) (by rw [hr', smul_smul]) hμr
    exact reflect_eq_add_smul_of_mem_fixedSpan (a := fun y => l y • a' y) hGram hdet hA1'' hlc
      hx hy hκ hκr

end CFSG.OddTranspositions.PartThree

end
