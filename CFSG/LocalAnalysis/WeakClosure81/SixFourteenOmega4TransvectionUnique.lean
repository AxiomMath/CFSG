module

public import CFSG.Quasithin.Vol2.Ch9H11Norm
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenFTransvection
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.Quasithin.Background.HFF
public import CFSG.Quasithin.Background.HSL3Inner
public import CFSG.Quasithin.Background.HSL3NPrime

public section

noncomputable section

open CFSG.Quasithin CFSG.ASVolI.ChH
open CFSG.Quasithin.H13.H11P
open CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix

namespace CFSG.LocalAnalysis.WeakClosure81

local notation "F₄" => GaloisField 2 2
local notation "M₄" => Matrix (Fin 2) (Fin 2) F₄

lemma addMap_linToMulAut_apply (g : M₄ ≃ₗ[F₄] M₄) (X : M₄) :
    addMap (linToMulAut F₄ M₄ g) X = g.toLinearMap X := rfl

lemma mapMatrix_smul_one (σ : F₄ ≃+* F₄) (a : F₄) :
    σ.mapMatrix (a • (1 : M₄)) = σ a • (1 : M₄) := by
  rw [mapMatrix_smul]
  simp

lemma eq_scalar_of_mul_right_eq_id {A B : M₄} (hAB : A * B = 1)
    (h : ∀ X, A * X * B = X) : ∃ α : F₄, A = α • (1 : M₄) := by
  have hBA : B * A = 1 := mul_eq_one_comm.mp hAB
  have hcomm : ∀ X : M₄, A * X = X * A := by
    intro X
    calc A * X = A * X * (B * A) := by rw [hBA, Matrix.mul_one]
      _ = (A * X * B) * A := by simp only [Matrix.mul_assoc]
      _ = X * A := by rw [h]
  have hpair : Pairwise fun i j : Fin 2 => Commute (Matrix.single i j (1 : F₄)) A := by
    intro i j hij
    exact (hcomm (Matrix.single i j 1)).symm
  obtain ⟨α, hα⟩ := Matrix.mem_range_scalar_of_commute_single hpair
  refine ⟨α, ?_⟩
  rw [← hα, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

lemma pow_four_eq_one {c : F₄} (hc : c ≠ 0) (h : c ^ 4 = 1) : c = 1 := by
  letI : Fintype F₄ := Fintype.ofFinite F₄
  have h3 : c ^ 3 = 1 := by
    have h' := FiniteField.pow_card_sub_one_eq_one c hc
    have hcard : Fintype.card F₄ = 4 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
      norm_num
    rw [hcard] at h'
    norm_num at h'
    exact h'
  have : c ^ 3 * c = 1 := by rw [show c ^ 3 * c = c ^ 4 by ring, h]
  rwa [h3, one_mul] at this

lemma involution_matrix_entries (A : M₄) (hAA : A * A = 1) (hdet : Matrix.det A = 1) :
    A 1 1 = A 0 0 ∧ A 0 0 ^ 2 + A 0 1 * A 1 0 = 1 := by
  have e00 := congrFun (congrFun hAA 0) 0
  have e11 := congrFun (congrFun hAA 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e11
  rw [Matrix.det_fin_two, CharTwo.sub_eq_add] at hdet
  have hbc : A 0 0 * A 0 0 + A 0 1 * A 1 0 = A 0 0 * A 1 1 + A 0 1 * A 1 0 := by
    rw [e00, hdet]
  have h1 : A 0 0 ^ 2 = A 0 0 * A 1 1 := by
    rw [pow_two]
    exact add_right_cancel hbc
  have h2' : A 1 1 * A 1 1 + A 0 1 * A 1 0 = 1 := by
    rw [← e11]
    ring
  have hbc2 : A 1 1 * A 1 1 + A 0 1 * A 1 0 = A 0 0 * A 1 1 + A 0 1 * A 1 0 := by
    rw [h2', hdet]
  have h2 : A 1 1 ^ 2 = A 0 0 * A 1 1 := by
    rw [pow_two]
    exact add_right_cancel hbc2
  refine ⟨CharTwo.sq_injective (h1.trans h2.symm).symm, ?_⟩
  simpa [pow_two] using e00

lemma preserve_form_constraints
    (A B : M₄) (c : F₄) (hc : c ≠ 0) (hA : Matrix.det A = 1) (hB : Matrix.det B = 1)
    (h : ∀ X : M₄, c ^ 2 • (A * X * Matrix.transpose B) = X) :
    c = 1 ∧ A = 1 ∧ B = 1 := by
  let A' : M₄ := c ^ 2 • A
  let B' : M₄ := Matrix.transpose B
  have h' : ∀ X : M₄, A' * X * B' = X := by
    intro X
    simpa [A', B', Matrix.smul_mul, Matrix.mul_assoc] using h X
  have hAB' : A' * B' = 1 := by simpa using h' 1
  obtain ⟨α, hα⟩ := eq_scalar_of_mul_right_eq_id hAB' h'
  have hα0 : α ≠ 0 := by
    intro h0
    have hzero : A' = 0 := by rw [hα, h0, zero_smul]
    rw [hzero, Matrix.zero_mul] at hAB'
    exact zero_ne_one hAB'
  have hB' : B' = α⁻¹ • (1 : M₄) := by
    have h1 : (α⁻¹ • (1 : M₄)) * (α • (1 : M₄)) = 1 := by
      rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hα0, one_smul]
    calc B' = 1 * B' := by rw [one_mul]
      _ = ((α⁻¹ • (1 : M₄)) * (α • (1 : M₄))) * B' := by rw [h1, one_mul]
      _ = (α⁻¹ • (1 : M₄)) * ((α • (1 : M₄)) * B') := by rw [Matrix.mul_assoc]
      _ = (α⁻¹ • (1 : M₄)) * (A' * B') := by rw [← hα]
      _ = (α⁻¹ • (1 : M₄)) * 1 := by rw [hAB']
      _ = α⁻¹ • (1 : M₄) := by rw [Matrix.mul_one]
  have hdetB' : Matrix.det B' = 1 := by
    change Matrix.det (Matrix.transpose B) = 1
    rw [Matrix.det_transpose, hB]
  have hsq : (α⁻¹) ^ 2 = 1 := by
    rw [hB', Matrix.det_smul, Matrix.det_one, Fintype.card_fin, pow_two, mul_one] at hdetB'
    rw [pow_two]
    exact hdetB'
  have hαinv1 : α⁻¹ = 1 := eq_one_of_sq_eq_one hsq
  have hα1 : α = 1 := by
    have := congrArg (fun x : F₄ => x⁻¹) hαinv1
    simpa using this
  have hA' : A' = 1 := by rw [hα, hα1, one_smul]
  have hB'1 : B' = 1 := by rw [hB', hαinv1, one_smul]
  have hB1 : B = 1 := by
    have hBt : Matrix.transpose B = 1 := by simpa [B'] using hB'1
    have := congrArg Matrix.transpose hBt
    simpa using this
  have hc4 : c ^ 4 = 1 := by
    have h1 : c ^ 2 • A = 1 := by rw [← hA']
    have hdet : Matrix.det (c ^ 2 • A) = 1 := by rw [h1, Matrix.det_one]
    rw [Matrix.det_smul, hA, Fintype.card_fin, mul_one] at hdet
    have hpow : (c ^ 2) ^ 2 = c ^ 4 := by ring
    rwa [hpow] at hdet
  have hc1 : c = 1 := pow_four_eq_one hc hc4
  have hA1 : A = 1 := by
    have h1 : c ^ 2 • A = 1 := by rw [← hA']
    rw [hc1] at h1
    simpa using h1
  exact ⟨hc1, hA1, hB1⟩

lemma transpose_form_constraints
    (A B : M₄) (c : F₄) (hc : c ≠ 0) (hA : Matrix.det A = 1) (hB : Matrix.det B = 1)
    (h : ∀ X : M₄, c ^ 2 • ((A * B) * X * Matrix.transpose (B * A)) = X) :
    c = 1 ∧ B = A⁻¹ := by
  let A' : M₄ := c ^ 2 • (A * B)
  let B' : M₄ := Matrix.transpose (B * A)
  have h' : ∀ X : M₄, A' * X * B' = X := by
    intro X
    simpa [A', B', Matrix.smul_mul, Matrix.mul_assoc] using h X
  have hAB' : A' * B' = 1 := by simpa using h' 1
  obtain ⟨α, hα⟩ := eq_scalar_of_mul_right_eq_id hAB' h'
  have hα0 : α ≠ 0 := by
    intro h0
    have hzero : A' = 0 := by rw [hα, h0, zero_smul]
    rw [hzero, Matrix.zero_mul] at hAB'
    exact zero_ne_one hAB'
  have hB' : B' = α⁻¹ • (1 : M₄) := by
    have h1 : (α⁻¹ • (1 : M₄)) * (α • (1 : M₄)) = 1 := by
      rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hα0, one_smul]
    calc B' = 1 * B' := by rw [one_mul]
      _ = ((α⁻¹ • (1 : M₄)) * (α • (1 : M₄))) * B' := by rw [h1, one_mul]
      _ = (α⁻¹ • (1 : M₄)) * ((α • (1 : M₄)) * B') := by rw [Matrix.mul_assoc]
      _ = (α⁻¹ • (1 : M₄)) * (A' * B') := by rw [← hα]
      _ = (α⁻¹ • (1 : M₄)) * 1 := by rw [hAB']
      _ = α⁻¹ • (1 : M₄) := by rw [Matrix.mul_one]
  have hdetB' : Matrix.det B' = 1 := by
    change Matrix.det (Matrix.transpose (B * A)) = 1
    rw [Matrix.det_transpose, Matrix.det_mul, hB, hA, one_mul]
  have hsq : (α⁻¹) ^ 2 = 1 := by
    rw [hB', Matrix.det_smul, Matrix.det_one, Fintype.card_fin, pow_two, mul_one] at hdetB'
    rw [pow_two]
    exact hdetB'
  have hαinv1 : α⁻¹ = 1 := eq_one_of_sq_eq_one hsq
  have hα1 : α = 1 := by
    have := congrArg (fun x : F₄ => x⁻¹) hαinv1
    simpa using this
  have hA' : A' = 1 := by rw [hα, hα1, one_smul]
  have hB'1 : B' = 1 := by rw [hB', hαinv1, one_smul]
  have hBAt : Matrix.transpose (B * A) = 1 := by simpa [B'] using hB'1
  have hBA : B * A = 1 := by
    have := congrArg Matrix.transpose hBAt
    simpa using this
  have hAB : A * B = 1 := mul_eq_one_comm.mpr hBA
  have hc2 : c ^ 2 = 1 := by
    have h1 : c ^ 2 • (A * B) = 1 := by
      rw [← hA']
    rw [hAB] at h1
    have h2 : c ^ 2 • (1 : M₄) = (1 : F₄) • (1 : M₄) := by simpa using h1
    exact smul_left_injective F₄ (one_ne_zero : (1 : M₄) ≠ 0) h2
  refine ⟨eq_one_of_sq_eq_one hc2, ?_⟩
  exact (Matrix.inv_eq_left_inv hBA).symm

lemma sigma_eq_id_of_normal_form
    (t : MulAut (VM F₄)) (g : M₄ ≃ₗ[F₄] M₄) (hg : linToMulAut F₄ M₄ g = t)
    (c : F₄) (hc : c ≠ 0) (A B : M₄) (hA : Matrix.det A = 1) (hB : Matrix.det B = 1)
    (σ : F₄ ≃+* F₄)
    (h : (∀ X, addMap t X = c • (A * σ.mapMatrix X * Matrix.transpose B)) ∨
         (∀ X, addMap t X = c • (A * σ.mapMatrix (Matrix.transpose X) *
           Matrix.transpose B))) :
    σ = RingEquiv.refl F₄ := by
  have hlin : ∀ (a : F₄) (X : M₄), addMap t (a • X) = a • addMap t X := by
    intro a X
    rw [← hg, addMap_linToMulAut_apply]
    exact map_smul g.toLinearMap a X
  have hW : A * Matrix.transpose B ≠ 0 := by
    intro h0
    have hdet : Matrix.det (A * Matrix.transpose B) = 1 := by
      rw [Matrix.det_mul, Matrix.det_transpose, hA, hB, mul_one]
    rw [h0, Matrix.det_zero] at hdet
    exact one_ne_zero hdet.symm
  by_contra hσ
  have hex : ∃ a : F₄, σ a ≠ a := by
    by_contra h'
    apply hσ
    apply RingEquiv.ext
    intro a
    by_contra ha
    exact h' ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hex
  have hm1 : σ.mapMatrix (1 : M₄) = 1 := by simp
  rcases h with h | h
  · have h1 := hlin a (1 : M₄)
    rw [h, h] at h1
    rw [mapMatrix_smul_one] at h1
    rw [hm1] at h1
    simp only [Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul] at h1
    rw [smul_smul, smul_smul] at h1
    have h2 := smul_left_injective F₄ hW h1
    rw [mul_comm a c] at h2
    exact ha (mul_left_cancel₀ hc h2)
  · have h1 := hlin a (1 : M₄)
    rw [h, h] at h1
    rw [Matrix.transpose_smul, Matrix.transpose_one, mapMatrix_smul_one, hm1] at h1
    simp only [Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul] at h1
    rw [smul_smul, smul_smul] at h1
    have h2 := smul_left_injective F₄ hW h1
    rw [mul_comm a c] at h2
    exact ha (mul_left_cancel₀ hc h2)

lemma coe_inv_eq_matrix_inv (P : SL₂ F₄) :
    ((P⁻¹ : SL₂ F₄) : M₄) = (P : M₄)⁻¹ := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.inv_def,
    Matrix.SpecialLinearGroup.det_coe]
  simp

lemma exists_smul_or_smul_of_finrank_range_eq_one
    {u : M₄ →ₗ[F₄] M₄} (hu : Module.finrank F₄ (LinearMap.range u) = 1)
    {V W : M₄} (hV : V ∈ LinearMap.range u) (hW : W ∈ LinearMap.range u) :
    (∃ γ : F₄, W = γ • V) ∨ (∃ γ : F₄, V = γ • W) := by
  obtain ⟨z, hz0, hgen⟩ :=
    (finrank_eq_one_iff' (K := F₄) (V := LinearMap.range u)).mp hu
  obtain ⟨c, hc⟩ := hgen ⟨V, hV⟩
  obtain ⟨d, hd⟩ := hgen ⟨W, hW⟩
  have hVz : V = c • (z : M₄) := by
    have := congrArg Subtype.val hc
    simpa using this.symm
  have hWz : W = d • (z : M₄) := by
    have := congrArg Subtype.val hd
    simpa using this.symm
  by_cases hc0 : c = 0
  · right
    refine ⟨0, ?_⟩
    simp [hVz, hc0]
  · left
    have hz : (z : M₄) = c⁻¹ • V := by
      rw [hVz, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    refine ⟨d * c⁻¹, ?_⟩
    rw [hWz, hz, smul_smul]

lemma row_det_eq_zero {V W : M₄}
    (h : (∃ γ : F₄, W = γ • V) ∨ (∃ γ : F₄, V = γ • W)) (i : Fin 2) :
    V i 0 * W i 1 + V i 1 * W i 0 = 0 := by
  rcases h with ⟨γ, hW⟩ | ⟨γ, hV⟩
  · rw [hW]
    simp only [Matrix.smul_apply, smul_eq_mul]
    calc V i 0 * (γ * V i 1) + V i 1 * (γ * V i 0)
        = (γ * (V i 0 * V i 1)) + (γ * (V i 0 * V i 1)) := by ring
      _ = 0 := CharTwo.add_self_eq_zero _
  · rw [hV]
    simp only [Matrix.smul_apply, smul_eq_mul]
    calc (γ * W i 0) * W i 1 + (γ * W i 1) * W i 0
        = (γ * (W i 0 * W i 1)) + (γ * (W i 0 * W i 1)) := by ring
      _ = 0 := CharTwo.add_self_eq_zero _

lemma col_det_eq_zero {V W : M₄}
    (h : (∃ γ : F₄, W = γ • V) ∨ (∃ γ : F₄, V = γ • W)) (j : Fin 2) :
    V 0 j * W 1 j + V 1 j * W 0 j = 0 := by
  rcases h with ⟨γ, hW⟩ | ⟨γ, hV⟩
  · rw [hW]
    simp only [Matrix.smul_apply, smul_eq_mul]
    calc V 0 j * (γ * V 1 j) + V 1 j * (γ * V 0 j)
        = (γ * (V 0 j * V 1 j)) + (γ * (V 0 j * V 1 j)) := by ring
      _ = 0 := CharTwo.add_self_eq_zero _
  · rw [hV]
    simp only [Matrix.smul_apply, smul_eq_mul]
    calc (γ * W 0 j) * W 1 j + (γ * W 1 j) * W 0 j
        = (γ * (W 0 j * W 1 j)) + (γ * (W 0 j * W 1 j)) := by ring
      _ = 0 := CharTwo.add_self_eq_zero _

lemma caseA_impossible (A B : M₄) (hAA : A * A = 1) (hBB : B * B = 1)
    (hdetA : Matrix.det A = 1) (hdetB : Matrix.det B = 1)
    (g : M₄ ≃ₗ[F₄] M₄) (hg : ∀ X : M₄, g X = A * X * Matrix.transpose B)
    (hrank : Module.finrank F₄ (LinearMap.range (g.toLinearMap - LinearMap.id)) = 1) :
    False := by
  obtain ⟨hA11, hAeq⟩ := involution_matrix_entries A hAA hdetA
  obtain ⟨hB11, hBeq⟩ := involution_matrix_entries B hBB hdetB
  let u : M₄ →ₗ[F₄] M₄ := g.toLinearMap - LinearMap.id
  have hu : Module.finrank F₄ (LinearMap.range u) = 1 := by simpa [u] using hrank
  have mem21 : u (Matrix.single 1 0 (1 : F₄)) ∈ LinearMap.range u :=
    LinearMap.mem_range.mpr ⟨_, rfl⟩
  have mem22 : u (Matrix.single 1 1 (1 : F₄)) ∈ LinearMap.range u :=
    LinearMap.mem_range.mpr ⟨_, rfl⟩
  have mem11 : u (Matrix.single 0 0 (1 : F₄)) ∈ LinearMap.range u :=
    LinearMap.mem_range.mpr ⟨_, rfl⟩
  have mem12 : u (Matrix.single 0 1 (1 : F₄)) ∈ LinearMap.range u :=
    LinearMap.mem_range.mpr ⟨_, rfl⟩
  have e21_00 : u (Matrix.single 1 0 (1 : F₄)) 0 0 = A 0 1 * B 0 0 := by
    simp [u, hg, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.transpose_apply]
  have e21_01 : u (Matrix.single 1 0 (1 : F₄)) 0 1 = A 0 1 * B 1 0 := by
    simp [u, hg, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.transpose_apply]
  have e22_00 : u (Matrix.single 1 1 (1 : F₄)) 0 0 = A 0 1 * B 0 1 := by
    simp [u, hg, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.transpose_apply]
  have e22_01 : u (Matrix.single 1 1 (1 : F₄)) 0 1 = A 0 1 * B 1 1 := by
    simp [u, hg, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.transpose_apply]
  have e11_10 : u (Matrix.single 0 0 (1 : F₄)) 1 0 = A 1 0 * B 0 0 := by
    simp [u, hg, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.transpose_apply]
  have e11_11 : u (Matrix.single 0 0 (1 : F₄)) 1 1 = A 1 0 * B 1 0 := by
    simp [u, hg, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.transpose_apply]
  have e12_10 : u (Matrix.single 0 1 (1 : F₄)) 1 0 = A 1 0 * B 0 1 := by
    simp [u, hg, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.transpose_apply]
  have e12_11 : u (Matrix.single 0 1 (1 : F₄)) 1 1 = A 1 0 * B 1 1 := by
    simp [u, hg, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.transpose_apply]
  have e12_00 : u (Matrix.single 0 1 (1 : F₄)) 0 0 = A 0 0 * B 0 1 := by
    simp [u, hg, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.transpose_apply]
  have e22_10 : u (Matrix.single 1 1 (1 : F₄)) 1 0 = A 1 1 * B 0 1 := by
    simp [u, hg, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.transpose_apply]
  have e11_01 : u (Matrix.single 0 0 (1 : F₄)) 0 1 = A 0 0 * B 1 0 := by
    simp [u, hg, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.transpose_apply]
  have e21_11 : u (Matrix.single 1 0 (1 : F₄)) 1 1 = A 1 1 * B 1 0 := by
    simp [u, hg, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.transpose_apply]
  have hb : A 0 1 = 0 := by
    have hdep := exists_smul_or_smul_of_finrank_range_eq_one hu mem21 mem22
    have hdet := row_det_eq_zero hdep 0
    rw [e21_00, e21_01, e22_00, e22_01] at hdet
    have hsq : (A 0 1) ^ 2 = 0 := by
      calc (A 0 1) ^ 2 = (A 0 1) ^ 2 * (B 0 0 ^ 2 + B 0 1 * B 1 0) := by
            rw [hBeq, mul_one]
        _ = (A 0 1 * B 0 0) * (A 0 1 * B 1 1) +
            (A 0 1 * B 1 0) * (A 0 1 * B 0 1) := by
            rw [hB11]
            ring
        _ = 0 := hdet
    exact sq_eq_zero_iff.mp hsq
  have hc : A 1 0 = 0 := by
    have hdep := exists_smul_or_smul_of_finrank_range_eq_one hu mem11 mem12
    have hdet := row_det_eq_zero hdep 1
    rw [e11_10, e11_11, e12_10, e12_11] at hdet
    have hsq : (A 1 0) ^ 2 = 0 := by
      calc (A 1 0) ^ 2 = (A 1 0) ^ 2 * (B 0 0 ^ 2 + B 0 1 * B 1 0) := by
            rw [hBeq, mul_one]
        _ = (A 1 0 * B 0 0) * (A 1 0 * B 1 1) +
            (A 1 0 * B 1 0) * (A 1 0 * B 0 1) := by
            rw [hB11]
            ring
        _ = 0 := hdet
    exact sq_eq_zero_iff.mp hsq
  have hf : B 0 1 = 0 := by
    have hdep := exists_smul_or_smul_of_finrank_range_eq_one hu mem12 mem22
    have hdet := col_det_eq_zero hdep 0
    rw [e12_00, e12_10, e22_00, e22_10] at hdet
    have hsq : (B 0 1) ^ 2 = 0 := by
      calc (B 0 1) ^ 2 = (B 0 1) ^ 2 * (A 0 0 ^ 2 + A 0 1 * A 1 0) := by
            rw [hAeq, mul_one]
        _ = (A 0 0 * B 0 1) * (A 1 1 * B 0 1) +
            (A 1 0 * B 0 1) * (A 0 1 * B 0 1) := by
            rw [hA11]
            ring
        _ = 0 := hdet
    exact sq_eq_zero_iff.mp hsq
  have hh : B 1 0 = 0 := by
    have hdep := exists_smul_or_smul_of_finrank_range_eq_one hu mem11 mem21
    have hdet := col_det_eq_zero hdep 1
    rw [e11_01, e11_11, e21_01, e21_11] at hdet
    have hsq : (B 1 0) ^ 2 = 0 := by
      calc (B 1 0) ^ 2 = (B 1 0) ^ 2 * (A 0 0 ^ 2 + A 0 1 * A 1 0) := by
            rw [hAeq, mul_one]
        _ = (A 0 0 * B 1 0) * (A 1 1 * B 1 0) +
            (A 1 0 * B 1 0) * (A 0 1 * B 1 0) := by
            rw [hA11]
            ring
        _ = 0 := hdet
    exact sq_eq_zero_iff.mp hsq
  have hA00 : A 0 0 = 1 := by
    have h : (A 0 0) ^ 2 = 1 := by
      have h1 := hAeq
      rw [hb, hc, mul_zero, add_zero] at h1
      exact h1
    exact eq_one_of_sq_eq_one h
  have hB00 : B 0 0 = 1 := by
    have h : (B 0 0) ^ 2 = 1 := by
      have h1 := hBeq
      rw [hf, hh, mul_zero, add_zero] at h1
      exact h1
    exact eq_one_of_sq_eq_one h
  have hA : A = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using hA00
    · simpa using hb
    · simpa using hc
    · simpa using hA11.trans hA00
  have hB : B = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using hB00
    · simpa using hf
    · simpa using hh
    · simpa using hB11.trans hB00
  have hg1 : g = 1 := by
    ext X
    rw [hg, hA, hB]
    simp
  have hg1' : g.toLinearMap = (LinearMap.id : M₄ →ₗ[F₄] M₄) := by
    rw [hg1]
    rfl
  rw [hg1'] at hrank
  rw [sub_self, LinearMap.range_zero, finrank_bot] at hrank
  omega

lemma exists_P_eq_rho_trn {t : MulAut (VM F₄)}
    (hx : t ∈ Subgroup.normalizer ((Lm F₄ : Subgroup (MulAut (VM F₄))) : Set (MulAut (VM F₄))))
    (ht : IsFTransvectionOn F₄ M₄ t) :
    ∃ P : SL₂ F₄, t = rho (P, P⁻¹) * trn := by
  classical
  have h2 : (2 : F₄) = 0 := CharP.cast_eq_zero F₄ 2
  have ht2 : t * t = 1 := ht.involutive h2
  obtain ⟨g, hg, hrank, hsq⟩ := ht
  have h4 : 4 ≤ Nat.card F₄ := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨c, hc0, P, Q, σ, hA | hB⟩ := normal_form h4 hx
  ·
    let A : M₄ := (P : M₄)
    let B : M₄ := (Q : M₄)
    have hdetA : Matrix.det A = 1 := Matrix.SpecialLinearGroup.det_coe P
    have hdetB : Matrix.det B = 1 := Matrix.SpecialLinearGroup.det_coe Q
    have hlin : ∀ (a : F₄) (X : M₄), addMap t (a • X) = a • addMap t X := by
      intro a X
      rw [← hg, addMap_linToMulAut_apply]
      exact map_smul g.toLinearMap a X
    have hσ : σ = RingEquiv.refl F₄ := by
      refine sigma_eq_id_of_normal_form t g hg c hc0 A B hdetA hdetB σ ?_
      exact Or.inl (fun X => by simpa [A, B] using hA X)
    have hA' : ∀ X : M₄, addMap t X = c • (A * X * Matrix.transpose B) := by
      intro X
      have := hA X
      rw [hσ] at this
      simpa [A, B, RingEquiv.mapMatrix_refl] using this
    have hmat : ∀ X : M₄,
        A * (A * X * Matrix.transpose B) * Matrix.transpose B =
          (A * A) * X * Matrix.transpose (B * B) := by
      intro X
      rw [Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    have hsq_eq : ∀ X : M₄,
        c ^ 2 • ((A * A) * X * Matrix.transpose (B * B)) = X := by
      intro X
      have h1 := congrArg (fun s : MulAut (VM F₄) => addMap s X) ht2
      rw [addMap_mul, addMap_one] at h1
      calc c ^ 2 • ((A * A) * X * Matrix.transpose (B * B))
          = c • (c • (A * (A * X * Matrix.transpose B) * Matrix.transpose B)) := by
            rw [pow_two, smul_smul, hmat]
        _ = c • addMap t (A * X * Matrix.transpose B) := by rw [hA']
        _ = addMap t (c • (A * X * Matrix.transpose B)) := (hlin c _).symm
        _ = addMap t (addMap t X) := congrArg (addMap t) (hA' X).symm
        _ = X := h1
    have hdetAA : Matrix.det (A * A) = 1 := by rw [Matrix.det_mul, hdetA, mul_one]
    have hdetBB : Matrix.det (B * B) = 1 := by rw [Matrix.det_mul, hdetB, mul_one]
    obtain ⟨hc1, hAA, hBB⟩ :=
      preserve_form_constraints (A * A) (B * B) c hc0 hdetAA hdetBB (by
        simpa only [Matrix.transpose_mul] using hsq_eq)
    have hgA : ∀ X : M₄, g X = A * X * Matrix.transpose B := by
      intro X
      have hgX : g X = addMap t X := by
        rw [← hg, addMap_linToMulAut_apply]
        rfl
      rw [hgX, hA', hc1, one_smul]
    exfalso
    exact caseA_impossible A B hAA hBB hdetA hdetB g hgA hrank
  ·
    let A : M₄ := (P : M₄)
    let B : M₄ := (Q : M₄)
    have hdetA : Matrix.det A = 1 := Matrix.SpecialLinearGroup.det_coe P
    have hdetB : Matrix.det B = 1 := Matrix.SpecialLinearGroup.det_coe Q
    have hlin : ∀ (a : F₄) (X : M₄), addMap t (a • X) = a • addMap t X := by
      intro a X
      rw [← hg, addMap_linToMulAut_apply]
      exact map_smul g.toLinearMap a X
    have hσ : σ = RingEquiv.refl F₄ := by
      refine sigma_eq_id_of_normal_form t g hg c hc0 A B hdetA hdetB σ ?_
      exact Or.inr (fun X => by simpa [A, B] using hB X)
    have hB' : ∀ X : M₄, addMap t X = c • (A * Matrix.transpose X * Matrix.transpose B) := by
      intro X
      have := hB X
      rw [hσ] at this
      simpa [A, B, RingEquiv.mapMatrix_refl] using this
    have hmat : ∀ X : M₄,
        A * Matrix.transpose (A * Matrix.transpose X * Matrix.transpose B) *
          Matrix.transpose B = (A * B) * X * Matrix.transpose (B * A) := by
      intro X
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.transpose_transpose, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    have hsq_eq : ∀ X : M₄,
        c ^ 2 • ((A * B) * X * Matrix.transpose (B * A)) = X := by
      intro X
      have h1 := congrArg (fun s : MulAut (VM F₄) => addMap s X) ht2
      rw [addMap_mul, addMap_one] at h1
      calc c ^ 2 • ((A * B) * X * Matrix.transpose (B * A))
          = c • (c • (A * Matrix.transpose (A * Matrix.transpose X * Matrix.transpose B) *
              Matrix.transpose B)) := by
            rw [pow_two, smul_smul, hmat]
        _ = c • addMap t (A * Matrix.transpose X * Matrix.transpose B) := by rw [hB']
        _ = addMap t (c • (A * Matrix.transpose X * Matrix.transpose B)) := (hlin c _).symm
        _ = addMap t (addMap t X) := congrArg (addMap t) (hB' X).symm
        _ = X := h1
    obtain ⟨hc1, hBA⟩ := transpose_form_constraints A B c hc0 hdetA hdetB hsq_eq
    have hBinv : B = ((P⁻¹ : SL₂ F₄) : M₄) := by
      rw [hBA, ← coe_inv_eq_matrix_inv P]
    refine ⟨P, ?_⟩
    apply eq_of_addMap
    intro X
    rw [hB' X, hc1, one_smul, hBinv]
    simp [A, B, addMap_mul, addMap_rho, addMap_trn]

lemma coe_mul_coe_inv (P : SL₂ F₄) :
    (P : M₄) * ((P⁻¹ : SL₂ F₄) : M₄) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

lemma coe_inv_mul_coe (P : SL₂ F₄) :
    ((P⁻¹ : SL₂ F₄) : M₄) * (P : M₄) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

end CFSG.LocalAnalysis.WeakClosure81

end

end
