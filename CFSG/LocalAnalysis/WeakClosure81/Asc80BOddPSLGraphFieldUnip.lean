module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoFixedField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoDescentField
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankBoundField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoGeneralLinear
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.PSLOuter

open Matrix

section Form

variable {k : Type*} [Field k] {n : ℕ} {σ : k ≃+* k} {Φ : Matrix (Fin n) (Fin n) k}

local notation "h[" x ", " y "]" => (fun i => σ (x i)) ⬝ᵥ (Φ *ᵥ y)

private lemma map_smul_apply (c : k) (M : Matrix (Fin n) (Fin n) k) :
    (c • M).map σ = σ c • M.map σ := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply, map_mul]

private lemma map_map_apply (hσ2 : σ * σ = 1) (M : Matrix (Fin n) (Fin n) k) :
    (M.map σ).map σ = M := by
  rw [Matrix.map_map]
  have : (⇑σ ∘ ⇑σ) = id := by
    funext x
    exact RingEquiv.congr_fun hσ2 x
  rw [this, Matrix.map_id]

private lemma hform_add_right (x y z : Fin n → k) :
    h[x, y + z] = h[x, y] + h[x, z] := by
  simp [Matrix.mulVec_add, dotProduct_add]

private lemma hform_smul_right (c : k) (x y : Fin n → k) :
    h[x, c • y] = c * h[x, y] := by
  simp [Matrix.mulVec_smul, dotProduct_smul]

private lemma hform_add_left (x y z : Fin n → k) :
    h[x + y, z] = h[x, z] + h[y, z] := by
  have hx : (fun i => σ ((x + y) i)) = (fun i => σ (x i)) + fun i => σ (y i) := by
    funext i; simp
  rw [hx, add_dotProduct]

private lemma hform_smul_left (c : k) (x y : Fin n → k) :
    h[c • x, y] = σ c * h[x, y] := by
  have hx : (fun i => σ ((c • x) i)) = σ c • (fun i => σ (x i)) := by
    funext i; simp
  rw [hx, smul_dotProduct, smul_eq_mul]

private lemma hform_sum4 (a b c d : Fin n → k) :
    h[a + b, c + d] = h[a, c] + h[a, d] + h[b, c] + h[b, d] := by
  rw [hform_add_left, hform_add_right, hform_add_right]
  ring

private lemma hform_zero_right (x : Fin n → k) : h[x, (0 : Fin n → k)] = 0 := by
  simp

private lemma map_mulVec_apply (A : Matrix (Fin n) (Fin n) k) (x : Fin n → k) :
    (fun i => σ ((A *ᵥ x) i)) = A.map σ *ᵥ fun i => σ (x i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

private lemma hermitian_entry (hΦh : Φ = (Φ.map σ)ᵀ) (i j : Fin n) :
    Φ i j = σ (Φ j i) := by
  have := congrFun (congrFun hΦh i) j
  simpa [Matrix.transpose_apply, Matrix.map_apply] using this

private lemma hform_comm (hΦh : Φ = (Φ.map σ)ᵀ) (hσ2 : σ * σ = 1) (x y : Fin n → k) :
    h[y, x] = σ (h[x, y]) := by
  have hinv : ∀ c, σ (σ c) = c := fun c => RingEquiv.congr_fun hσ2 c
  have hentry : ∀ i j, σ (Φ i j) = Φ j i := fun i j => (hermitian_entry hΦh j i).symm
  have hterm : ∀ i, σ (σ (x i) * ∑ j, Φ i j * y j) = x i * ∑ j, Φ j i * σ (y j) := by
    intro i
    rw [map_mul, map_sum, hinv]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hentry]
  have hL : (∑ i, σ (y i) * ∑ j, Φ i j * x j) = ∑ j, x j * ∑ i, Φ i j * σ (y i) := by
    calc (∑ i, σ (y i) * ∑ j, Φ i j * x j)
        = ∑ i, ∑ j, σ (y i) * (Φ i j * x j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ j, ∑ i, σ (y i) * (Φ i j * x j) := Finset.sum_comm
      _ = ∑ j, x j * ∑ i, Φ i j * σ (y i) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
  have hR : (∑ i, σ (σ (x i) * ∑ j, Φ i j * y j)) = ∑ i, x i * ∑ j, Φ j i * σ (y j) :=
    Finset.sum_congr rfl (fun i _ => hterm i)
  simp only [dotProduct, mulVec]
  rw [map_sum, hR, hL]


private lemma mulVec_eq_zero_of_isUnit_det (M : Matrix (Fin n) (Fin n) k) (hM : IsUnit M.det)
    {u : Fin n → k} (hu : M *ᵥ u = 0) : u = 0 := by
  have hinj : Function.Injective M.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det M).mpr hM)
  have h := hinj (show M *ᵥ u = M *ᵥ 0 by rw [hu, Matrix.mulVec_zero])
  simpa using h

private lemma hform_nondegenerate (hΦ : IsUnit Φ.det) {x : Fin n → k}
    (hx : ∀ y, h[x, y] = 0) : x = 0 := by
  have hcol : Φᵀ *ᵥ (fun i => σ (x i)) = 0 := by
    funext j
    have hsum : ∑ i, σ (x i) * Φ i j = 0 := by
      have h := hx (Pi.single j 1)
      simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using h
    calc (Φᵀ *ᵥ (fun i => σ (x i))) j
        = ∑ i, Φ i j * σ (x i) := by
          simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      _ = ∑ i, σ (x i) * Φ i j := Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = 0 := hsum
  have hdet : IsUnit (Φᵀ).det := by rwa [Matrix.det_transpose]
  have hu : (fun i => σ (x i)) = 0 := mulVec_eq_zero_of_isUnit_det Φᵀ hdet hcol
  funext i
  exact σ.injective (by simpa using congrFun hu i)

private lemma map_vecMulVec (u v : Fin n → k) :
    (Matrix.vecMulVec u v).map σ = Matrix.vecMulVec (fun i => σ (u i)) (fun j => σ (v j)) := by
  ext i j
  simp [Matrix.vecMulVec_apply, map_mul]

private lemma vecMulVec_mulVec_apply (u v w : Fin n → k) :
    Matrix.vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  rw [Matrix.vecMulVec_mulVec]
  ext i
  simp [MulOpposite.smul_eq_mul_unop, mul_comm]

private lemma hform_adjoint {B : Matrix (Fin n) (Fin n) k} {κ : k}
    (hB2 : B * B = 1) (hBΦ : (B.map σ)ᵀ * Φ * B = κ • Φ) (x y : Fin n → k) :
    h[B *ᵥ x, y] = κ * h[x, B *ᵥ y] := by
  have hT : (B.map σ)ᵀ * Φ = κ • (Φ * B) := by
    have hL : (B.map σ)ᵀ * Φ * B * B = (B.map σ)ᵀ * Φ := by
      simp only [Matrix.mul_assoc, hB2, Matrix.mul_one]
    have h1 : (B.map σ)ᵀ * Φ * B * B = (κ • Φ) * B := by
      rw [hBΦ]
    have h2 : (κ • Φ) * B = κ • (Φ * B) := by rw [Matrix.smul_mul]
    exact hL.symm.trans (h1.trans h2)
  calc h[B *ᵥ x, y]
      = ((B.map σ) *ᵥ fun i => σ (x i)) ᵥ* Φ ⬝ᵥ y := by
          rw [Matrix.dotProduct_mulVec, map_mulVec_apply]
    _ = (fun i => σ (x i)) ᵥ* ((B.map σ)ᵀ * Φ) ⬝ᵥ y := by rw [Matrix.vecMul_mulVec]
    _ = (fun i => σ (x i)) ⬝ᵥ (((B.map σ)ᵀ * Φ) *ᵥ y) := (Matrix.dotProduct_mulVec _ _ _).symm
    _ = (fun i => σ (x i)) ⬝ᵥ ((κ • (Φ * B)) *ᵥ y) := by rw [hT]
    _ = κ * h[x, B *ᵥ y] := by
          rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec, dotProduct_smul, smul_eq_mul]

private lemma hform_isometry {B : Matrix (Fin n) (Fin n) k} {κ : k}
    (hBΦ : (B.map σ)ᵀ * Φ * B = κ • Φ) (x y : Fin n → k) :
    h[B *ᵥ x, B *ᵥ y] = κ * h[x, y] := by
  calc h[B *ᵥ x, B *ᵥ y]
      = ((B.map σ) *ᵥ fun i => σ (x i)) ᵥ* Φ ⬝ᵥ (B *ᵥ y) := by
          rw [Matrix.dotProduct_mulVec, map_mulVec_apply]
    _ = (fun i => σ (x i)) ᵥ* ((B.map σ)ᵀ * Φ) ⬝ᵥ (B *ᵥ y) := by rw [Matrix.vecMul_mulVec]
    _ = (fun i => σ (x i)) ⬝ᵥ (((B.map σ)ᵀ * Φ) *ᵥ (B *ᵥ y)) :=
        (Matrix.dotProduct_mulVec _ _ _).symm
    _ = (fun i => σ (x i)) ⬝ᵥ ((((B.map σ)ᵀ * Φ) * B) *ᵥ y) := by
          rw [Matrix.mulVec_mulVec]
    _ = (fun i => σ (x i)) ⬝ᵥ ((κ • Φ) *ᵥ y) := by rw [hBΦ]
    _ = κ * h[x, y] := by rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]


private lemma mem_ker_sub_one_iff {B : Matrix (Fin n) (Fin n) k} (x : Fin n → k) :
    x ∈ LinearMap.ker (B.mulVecLin - 1) ↔ B *ᵥ x = x := by
  show B.mulVecLin x - x = 0 ↔ B *ᵥ x = x
  rw [Matrix.mulVecLin_apply, sub_eq_zero]

private lemma mem_ker_add_one_iff {B : Matrix (Fin n) (Fin n) k} (x : Fin n → k) :
    x ∈ LinearMap.ker (B.mulVecLin + 1) ↔ B *ᵥ x = -x := by
  show B.mulVecLin x + x = 0 ↔ B *ᵥ x = -x
  rw [Matrix.mulVecLin_apply, add_eq_zero_iff_eq_neg]

private lemma smul_add_mulVec_mem {B : Matrix (Fin n) (Fin n) k} (hB2 : B * B = 1)
    (v : Fin n → k) :
    ((2 : k)⁻¹) • (v + B *ᵥ v) ∈ LinearMap.ker (B.mulVecLin - 1) := by
  rw [mem_ker_sub_one_iff, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_mulVec, hB2,
    Matrix.one_mulVec, add_comm]

private lemma smul_sub_mulVec_mem {B : Matrix (Fin n) (Fin n) k} (hB2 : B * B = 1)
    (v : Fin n → k) :
    ((2 : k)⁻¹) • (v - B *ᵥ v) ∈ LinearMap.ker (B.mulVecLin + 1) := by
  rw [mem_ker_add_one_iff, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hB2,
    Matrix.one_mulVec, smul_sub, smul_sub, neg_sub]

private lemma eq_smul_add_smul {B : Matrix (Fin n) (Fin n) k} (h2 : (2 : k) ≠ 0)
    (v : Fin n → k) :
    ((2 : k)⁻¹) • (v + B *ᵥ v) + ((2 : k)⁻¹) • (v - B *ᵥ v) = v := by
  rw [← smul_add]
  have harg : (v + B *ᵥ v) + (v - B *ᵥ v) = (2 : k) • v := by
    rw [two_smul]; abel
  rw [harg, smul_smul, inv_mul_cancel₀ h2, one_smul]

private lemma sup_ker_eq_top {B : Matrix (Fin n) (Fin n) k} (hB2 : B * B = 1)
    (h2 : (2 : k) ≠ 0) :
    LinearMap.ker (B.mulVecLin - 1) ⊔ LinearMap.ker (B.mulVecLin + 1) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  rw [← eq_smul_add_smul h2 x]
  exact Submodule.add_mem_sup (smul_add_mulVec_mem hB2 x) (smul_sub_mulVec_mem hB2 x)

private lemma inf_ker_eq_bot {B : Matrix (Fin n) (Fin n) k} (h2 : (2 : k) ≠ 0) :
    LinearMap.ker (B.mulVecLin - 1) ⊓ LinearMap.ker (B.mulVecLin + 1) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf, mem_ker_sub_one_iff, mem_ker_add_one_iff] at hx
  have hxeq : x = -x := hx.1.symm.trans hx.2
  have h2x : (2 : k) • x = 0 := by
    have hxx : x + x = 0 := by
      nth_rewrite 2 [hxeq]
      rw [add_neg_cancel]
    rwa [two_smul]
  exact (smul_eq_zero.mp h2x).resolve_left h2

private lemma finrank_ker_add {B : Matrix (Fin n) (Fin n) k} (hB2 : B * B = 1)
    (h2 : (2 : k) ≠ 0) :
    Module.finrank k (LinearMap.ker (B.mulVecLin - 1)) +
      Module.finrank k (LinearMap.ker (B.mulVecLin + 1)) = n := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (B.mulVecLin - 1))
    (LinearMap.ker (B.mulVecLin + 1))
  rw [sup_ker_eq_top hB2 h2, inf_ker_eq_bot h2, finrank_top, finrank_bot,
    Module.finrank_fin_fun, add_zero] at h
  omega

private lemma exists_isotropic_of_finrank [Finite k] (hΦh : Φ = (Φ.map σ)ᵀ) (hσ2 : σ * σ = 1)
    (hσ1 : σ ≠ 1) {W : Submodule k (Fin n → k)} (h2 : 2 ≤ Module.finrank k W) :
    ∃ z ∈ W, z ≠ 0 ∧ h[z, z] = 0 := by
  have hWne : W ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at h2
    omega
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
  by_cases hxx : h[x, x] = 0
  · exact ⟨x, hxW, hx0, hxx⟩
  have hxx0 : h[x, x] ≠ 0 := hxx
  let g : W →ₗ[k] k :=
    { toFun := fun y => h[x, y.1]
      map_add' := fun y z => by
        show h[x, y.1 + z.1] = h[x, y.1] + h[x, z.1]
        rw [hform_add_right]
      map_smul' := fun c y => by
        show h[x, c • y.1] = c • h[x, y.1]
        rw [hform_smul_right, smul_eq_mul] }
  have hgx : g ⟨x, hxW⟩ = h[x, x] := rfl
  have hg0 : g ≠ 0 := by
    intro h0
    have : g ⟨x, hxW⟩ = 0 := by rw [h0]; rfl
    rw [hgx] at this
    exact hxx0 this
  have hker : LinearMap.ker g ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective g := LinearMap.ker_eq_bot.mp hbot
    have hle : Module.finrank k W ≤ Module.finrank k k :=
      LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_self] at hle
    omega
  obtain ⟨y, hyker, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hxy : h[x, y.1] = 0 := LinearMap.mem_ker.mp hyker
  have hy10 : y.1 ≠ 0 := fun h => hy0 (Subtype.ext h)
  by_cases hyy : h[y.1, y.1] = 0
  · exact ⟨y.1, y.2, hy10, hyy⟩
  have hyy0 : h[y.1, y.1] ≠ 0 := hyy
  have hfix1 : σ (h[x, x]) = h[x, x] := by
    rw [← hform_comm hΦh hσ2 x x]
  have hfix2 : σ (h[y.1, y.1]) = h[y.1, y.1] := by
    rw [← hform_comm hΦh hσ2 y.1 y.1]
  have hinvfix : σ ((h[y.1, y.1])⁻¹) = (h[y.1, y.1])⁻¹ := by
    have h1 : σ (h[y.1, y.1]) * σ ((h[y.1, y.1])⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hyy0, map_one]
    rw [hfix2] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hfix : σ (-h[x, x] * (h[y.1, y.1])⁻¹) = -h[x, x] * (h[y.1, y.1])⁻¹ := by
    rw [map_mul, map_neg, hfix1, hinvfix]
  have hne : (-h[x, x] * (h[y.1, y.1])⁻¹) ≠ 0 := by
    refine mul_ne_zero (neg_ne_zero.mpr hxx0) (inv_ne_zero hyy0)
  obtain ⟨b, hb⟩ := CFSG.ComponentClassification.CatalogueBLinearTwoDescent.exists_norm_unit k σ
    (by rw [pow_two]; exact hσ2) hσ1
    (Units.mk0 (-h[x, x] * (h[y.1, y.1])⁻¹) hne) hfix
  have hbval : (b : k) * σ (b : k) = -h[x, x] * (h[y.1, y.1])⁻¹ := hb
  refine ⟨x + (b : k) • y.1, W.add_mem hxW (W.smul_mem _ y.2), ?_, ?_⟩
  · intro hzero
    have hxx' : h[x, x] = 0 := by
      have := congrArg (fun v => h[x, v]) hzero
      rw [hform_zero_right] at this
      rwa [hform_add_right, hform_smul_right, hxy, mul_zero, add_zero] at this
    exact hxx0 hxx'
  · have hexp : h[x + (b : k) • y.1, x + (b : k) • y.1] =
        h[x, x] + (b : k) * σ (b : k) * h[y.1, y.1] := by
      rw [hform_add_left, hform_add_right, hform_add_right, hform_smul_right,
        hform_smul_left, hform_smul_left, hform_smul_right]
      rw [hform_comm hΦh hσ2 x y.1, hxy, map_zero, mul_zero, add_zero, mul_assoc]
      ring_nf
    rw [hexp, hbval]
    field_simp
    ring


private lemma rowMap_dotProduct (u x : Fin n → k) :
    (fun j => ∑ k, σ (u k) * Φ k j) ⬝ᵥ x = h[u, x] := by
  simp only [dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma rowMap_sigma (hΦh : Φ = (Φ.map σ)ᵀ) (hσ2 : σ * σ = 1) (u : Fin n → k) :
    (fun j => σ (∑ k, σ (u k) * Φ k j)) = Φ *ᵥ u := by
  have hinv : ∀ c : k, σ (σ c) = c := fun c => RingEquiv.congr_fun hσ2 c
  funext j
  simp only [map_sum, map_mul, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hinv, ← hermitian_entry hΦh j k]
  ring

private lemma map_transpose_vecMulVec (u y : Fin n → k) :
    ((Matrix.vecMulVec u y).map σ)ᵀ * Φ =
      Matrix.vecMulVec (fun j => σ (y j)) ((fun k => σ (u k)) ᵥ* Φ) := by
  rw [map_vecMulVec, Matrix.transpose_vecMulVec, Matrix.vecMulVec_mul]

private lemma rank_one_construction (hΦ : IsUnit Φ.det) (hΦh : Φ = (Φ.map σ)ᵀ)
    (hσ2 : σ * σ = 1) {a : k} (ha : a ≠ 0) (ha0 : σ a = -a) {z : Fin n → k} (hz : z ≠ 0)
    (hzz : h[z, z] = 0) :
    ∃ N : Matrix (Fin n) (Fin n) k, N ≠ 0 ∧ N * N = 0 ∧
      (N.map σ)ᵀ * Φ + Φ * N = 0 ∧ ∀ x, N *ᵥ x = a • (h[z, x] • z) := by
  have hact : ∀ x : Fin n → k, (a • Matrix.vecMulVec z (fun j => ∑ k, σ (z k) * Φ k j)) *ᵥ x
      = a • (h[z, x] • z) := by
    intro x
    rw [Matrix.smul_mulVec, vecMulVec_mulVec_apply, rowMap_dotProduct]
  refine ⟨a • Matrix.vecMulVec z (fun j => ∑ k, σ (z k) * Φ k j), ?_, ?_, ?_, hact⟩
  · intro hN
    obtain ⟨x, hx⟩ : ∃ x : Fin n → k, h[z, x] ≠ 0 := by
      by_contra h
      push Not at h
      exact hz (hform_nondegenerate hΦ (x := z) h)
    have h1 := hact x
    rw [hN, Matrix.zero_mulVec] at h1
    have h2 : a • (h[z, x] • z) = 0 := h1.symm
    rcases smul_eq_zero.mp h2 with h | h
    · exact ha h
    · rcases smul_eq_zero.mp h with h' | h'
      · exact hx h'
      · exact hz h'
  · have hzsz : (fun j => ∑ k, σ (z k) * Φ k j) ⬝ᵥ z = 0 := by
      rw [rowMap_dotProduct, hzz]
    calc (a • Matrix.vecMulVec z (fun j => ∑ k, σ (z k) * Φ k j)) *
          (a • Matrix.vecMulVec z (fun j => ∑ k, σ (z k) * Φ k j))
        = (a * a) • (Matrix.vecMulVec z (fun j => ∑ k, σ (z k) * Φ k j) *
            Matrix.vecMulVec z (fun j => ∑ k, σ (z k) * Φ k j)) := by
          rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      _ = 0 := by
          rw [Matrix.vecMulVec_mul_vecMulVec, hzsz, zero_smul]
          ext i j
          simp
  · have hskew : ((Matrix.vecMulVec z (fun j => ∑ k, σ (z k) * Φ k j)).map σ)ᵀ * Φ =
        Matrix.vecMulVec (Φ *ᵥ z) (fun j => ∑ k, σ (z k) * Φ k j) := by
      rw [map_transpose_vecMulVec, rowMap_sigma hΦh hσ2]
      rfl
    calc ((a • Matrix.vecMulVec z (fun j => ∑ k, σ (z k) * Φ k j)).map σ)ᵀ * Φ +
          Φ * (a • Matrix.vecMulVec z (fun j => ∑ k, σ (z k) * Φ k j))
        = σ a • (((Matrix.vecMulVec z (fun j => ∑ k, σ (z k) * Φ k j)).map σ)ᵀ * Φ) +
            a • (Φ * Matrix.vecMulVec z (fun j => ∑ k, σ (z k) * Φ k j)) := by
          simp only [map_smul_apply, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul]
      _ = σ a • Matrix.vecMulVec (Φ *ᵥ z) (fun j => ∑ k, σ (z k) * Φ k j) +
            a • Matrix.vecMulVec (Φ *ᵥ z) (fun j => ∑ k, σ (z k) * Φ k j) := by
          rw [hskew, Matrix.mul_vecMulVec]
      _ = (σ a + a) • Matrix.vecMulVec (Φ *ᵥ z) (fun j => ∑ k, σ (z k) * Φ k j) := by
          rw [← add_smul]
      _ = 0 := by rw [ha0, neg_add_cancel, zero_smul]


private lemma mem_ker_add_one_neg_iff {B : Matrix (Fin n) (Fin n) k} (x : Fin n → k) :
    x ∈ LinearMap.ker (B.mulVecLin + 1) ↔ B *ᵥ x = (-1 : k) • x := by
  rw [mem_ker_add_one_iff, show (-1 : k) • x = -x from neg_one_smul k x]

private lemma exists_ker_ne_zero {W : Submodule k (Fin n → k)}
    (hW : 2 ≤ Module.finrank k W) {x : Fin n → k} (hx : ∃ y ∈ W, h[x, y] ≠ 0) :
    ∃ y ∈ W, y ≠ 0 ∧ h[x, y] = 0 := by
  let g : W →ₗ[k] k :=
    { toFun := fun y => h[x, y.1]
      map_add' := fun y z => by
        show h[x, y.1 + z.1] = h[x, y.1] + h[x, z.1]
        rw [hform_add_right]
      map_smul' := fun c y => by
        show h[x, c • y.1] = c • h[x, y.1]
        rw [hform_smul_right, smul_eq_mul] }
  have hg0 : g ≠ 0 := by
    obtain ⟨y, hyW, hy⟩ := hx
    intro h0
    have : g ⟨y, hyW⟩ = 0 := by rw [h0]; rfl
    exact hy this
  have hker : LinearMap.ker g ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective g := LinearMap.ker_eq_bot.mp hbot
    have hle : Module.finrank k W ≤ Module.finrank k k :=
      LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_self] at hle
    omega
  obtain ⟨y, hyker, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨y.1, y.2, fun h => hy0 (Subtype.ext h), LinearMap.mem_ker.mp hyker⟩

private lemma hform_eq_zero_ker_sub_one (h2 : (2 : k) ≠ 0) {B : Matrix (Fin n) (Fin n) k}
    (hB2 : B * B = 1)
    (hBΦ : (B.map σ)ᵀ * Φ * B = (-1 : k) • Φ)
    {x y : Fin n → k} (hx : x ∈ LinearMap.ker (B.mulVecLin - 1))
    (hy : y ∈ LinearMap.ker (B.mulVecLin - 1)) : h[x, y] = 0 := by
  have hBx : B *ᵥ x = x := (mem_ker_sub_one_iff x).mp hx
  have hBy : B *ᵥ y = y := (mem_ker_sub_one_iff y).mp hy
  have hadj : h[B *ᵥ x, y] = (-1 : k) * h[x, B *ᵥ y] := hform_adjoint hB2 hBΦ x y
  rw [hBx, hBy, neg_one_mul] at hadj
  have h2xy : (2 : k) * h[x, y] = 0 := by
    rw [two_mul]
    nth_rewrite 2 [hadj]
    rw [add_neg_cancel]
  exact (mul_eq_zero.mp h2xy).resolve_left h2

private lemma hform_eq_zero_ker_add_one (h2 : (2 : k) ≠ 0) {B : Matrix (Fin n) (Fin n) k}
    (hB2 : B * B = 1)
    (hBΦ : (B.map σ)ᵀ * Φ * B = (-1 : k) • Φ)
    {x y : Fin n → k} (hx : x ∈ LinearMap.ker (B.mulVecLin + 1))
    (hy : y ∈ LinearMap.ker (B.mulVecLin + 1)) : h[x, y] = 0 := by
  have hBx : B *ᵥ x = (-1 : k) • x := (mem_ker_add_one_neg_iff x).mp hx
  have hBy : B *ᵥ y = (-1 : k) • y := (mem_ker_add_one_neg_iff y).mp hy
  have hl : h[(-1 : k) • x, y] = -h[x, y] := by
    rw [hform_smul_left, map_neg, map_one, neg_one_mul]
  have hr : h[x, (-1 : k) • y] = -h[x, y] := by
    rw [hform_smul_right, neg_one_mul]
  have hadj : h[B *ᵥ x, y] = (-1 : k) * h[x, B *ᵥ y] := hform_adjoint hB2 hBΦ x y
  rw [hBx, hBy] at hadj
  have h1 : -h[x, y] = h[x, y] := by
    rw [hl, hr, neg_one_mul, neg_neg] at hadj
    exact hadj
  have h2xy : (2 : k) * h[x, y] = 0 := by
    rw [two_mul]
    nth_rewrite 1 [← h1]
    rw [neg_add_cancel]
  exact (mul_eq_zero.mp h2xy).resolve_left h2

private lemma rank_two_construction (hΦ : IsUnit Φ.det) (hΦh : Φ = (Φ.map σ)ᵀ)
    (hσ2 : σ * σ = 1) {v w : Fin n → k} (hv : v ≠ 0) (hvw : ∀ c : k, w ≠ c • v)
    (hvv : h[v, v] = 0) (hww : h[w, w] = 0) (hvw0 : h[v, w] = 0) :
    ∃ N : Matrix (Fin n) (Fin n) k, N ≠ 0 ∧ N * N = 0 ∧
      (N.map σ)ᵀ * Φ + Φ * N = 0 ∧ ∀ x, N *ᵥ x = h[v, x] • w - h[w, x] • v := by
  have hact : ∀ x : Fin n → k,
      (Matrix.vecMulVec w (fun j => ∑ k, σ (v k) * Φ k j) -
        Matrix.vecMulVec v (fun j => ∑ k, σ (w k) * Φ k j)) *ᵥ x
      = h[v, x] • w - h[w, x] • v := by
    intro x
    rw [Matrix.sub_mulVec, vecMulVec_mulVec_apply, vecMulVec_mulVec_apply, rowMap_dotProduct,
      rowMap_dotProduct]
  have hwv : h[w, v] = 0 := by rw [hform_comm hΦh hσ2, hvw0, map_zero]
  have hA1 : Matrix.vecMulVec w (fun j => ∑ k, σ (v k) * Φ k j) *
      Matrix.vecMulVec v (fun j => ∑ k, σ (w k) * Φ k j) = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec]
    have h : (fun j => ∑ k, σ (v k) * Φ k j) ⬝ᵥ v = 0 := by rw [rowMap_dotProduct, hvv]
    rw [h, zero_smul]
    simp
  have hA2 : Matrix.vecMulVec v (fun j => ∑ k, σ (w k) * Φ k j) *
      Matrix.vecMulVec w (fun j => ∑ k, σ (v k) * Φ k j) = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec]
    have h : (fun j => ∑ k, σ (w k) * Φ k j) ⬝ᵥ w = 0 := by rw [rowMap_dotProduct, hww]
    rw [h, zero_smul]
    simp
  have hA3 : Matrix.vecMulVec w (fun j => ∑ k, σ (v k) * Φ k j) *
      Matrix.vecMulVec w (fun j => ∑ k, σ (v k) * Φ k j) = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec]
    have h : (fun j => ∑ k, σ (v k) * Φ k j) ⬝ᵥ w = 0 := by rw [rowMap_dotProduct, hvw0]
    rw [h, zero_smul]
    simp
  have hA4 : Matrix.vecMulVec v (fun j => ∑ k, σ (w k) * Φ k j) *
      Matrix.vecMulVec v (fun j => ∑ k, σ (w k) * Φ k j) = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec]
    have h : (fun j => ∑ k, σ (w k) * Φ k j) ⬝ᵥ v = 0 := by rw [rowMap_dotProduct, hwv]
    rw [h, zero_smul]
    simp
  have hB1 : ((Matrix.vecMulVec w (fun j => ∑ k, σ (v k) * Φ k j)).map σ)ᵀ * Φ =
      Matrix.vecMulVec (Φ *ᵥ v) (fun j => ∑ k, σ (w k) * Φ k j) := by
    rw [map_transpose_vecMulVec, rowMap_sigma hΦh hσ2]
    rfl
  have hB2 : ((Matrix.vecMulVec v (fun j => ∑ k, σ (w k) * Φ k j)).map σ)ᵀ * Φ =
      Matrix.vecMulVec (Φ *ᵥ w) (fun j => ∑ k, σ (v k) * Φ k j) := by
    rw [map_transpose_vecMulVec, rowMap_sigma hΦh hσ2]
    rfl
  have hC1 : Φ * Matrix.vecMulVec w (fun j => ∑ k, σ (v k) * Φ k j) =
      Matrix.vecMulVec (Φ *ᵥ w) (fun j => ∑ k, σ (v k) * Φ k j) := by
    rw [Matrix.mul_vecMulVec]
  have hC2 : Φ * Matrix.vecMulVec v (fun j => ∑ k, σ (w k) * Φ k j) =
      Matrix.vecMulVec (Φ *ᵥ v) (fun j => ∑ k, σ (w k) * Φ k j) := by
    rw [Matrix.mul_vecMulVec]
  refine ⟨Matrix.vecMulVec w (fun j => ∑ k, σ (v k) * Φ k j) -
    Matrix.vecMulVec v (fun j => ∑ k, σ (w k) * Φ k j), ?_, ?_, ?_, hact⟩
  · intro hN
    have hcol : ∀ x : Fin n → k, h[v, x] • w = h[w, x] • v := by
      intro x
      have h := hact x
      rw [hN, Matrix.zero_mulVec] at h
      exact sub_eq_zero.mp h.symm
    have hvzero : ∀ x : Fin n → k, h[v, x] = 0 := by
      intro x
      by_contra hx
      refine hvw (h[w, x] / h[v, x]) ?_
      rw [div_eq_inv_mul]
      calc w = (h[v, x])⁻¹ • (h[v, x] • w) := by rw [smul_smul, inv_mul_cancel₀ hx, one_smul]
        _ = (h[v, x])⁻¹ • (h[w, x] • v) := by rw [hcol x]
        _ = ((h[v, x])⁻¹ * h[w, x]) • v := by rw [smul_smul]
    exact hv (hform_nondegenerate hΦ (x := v) hvzero)
  · have hsq : (Matrix.vecMulVec w (fun j => ∑ k, σ (v k) * Φ k j) -
        Matrix.vecMulVec v (fun j => ∑ k, σ (w k) * Φ k j)) *
        (Matrix.vecMulVec w (fun j => ∑ k, σ (v k) * Φ k j) -
        Matrix.vecMulVec v (fun j => ∑ k, σ (w k) * Φ k j)) = 0 := by
      rw [sub_mul, mul_sub, mul_sub, sub_sub]
      rw [hA1, hA2, hA3, hA4]
      abel
    exact hsq
  · calc ((Matrix.vecMulVec w (fun j => ∑ k, σ (v k) * Φ k j) -
            Matrix.vecMulVec v (fun j => ∑ k, σ (w k) * Φ k j)).map σ)ᵀ * Φ +
          Φ * (Matrix.vecMulVec w (fun j => ∑ k, σ (v k) * Φ k j) -
            Matrix.vecMulVec v (fun j => ∑ k, σ (w k) * Φ k j))
        = (((Matrix.vecMulVec w (fun j => ∑ k, σ (v k) * Φ k j)).map σ)ᵀ * Φ -
            ((Matrix.vecMulVec v (fun j => ∑ k, σ (w k) * Φ k j)).map σ)ᵀ * Φ) +
          (Φ * Matrix.vecMulVec w (fun j => ∑ k, σ (v k) * Φ k j) -
            Φ * Matrix.vecMulVec v (fun j => ∑ k, σ (w k) * Φ k j)) := by
          rw [Matrix.map_sub σ (fun a b => map_sub σ a b), Matrix.transpose_sub, Matrix.sub_mul,
            Matrix.mul_sub]
      _ = 0 := by
          rw [hB1, hB2, hC1, hC2]
          abel


private lemma smul_smul_swap (a b : k) (x : Fin n → k) : a • (b • x) = b • (a • x) := by
  rw [smul_smul, smul_smul, mul_comm]

private lemma commute_rank_one_self {B N : Matrix (Fin n) (Fin n) k} {a ε : k}
    {z : Fin n → k} (hε : ε = 1 ∨ ε = -1) (hBz : B *ᵥ z = ε • z)
    (hN : ∀ x, N *ᵥ x = a • (h[z, x] • z))
    (hiso : ∀ x y, h[B *ᵥ x, B *ᵥ y] = (1 : k) * h[x, y]) : B * N = N * B := by
  have hεε : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> ring
  have hσε : σ ε = ε := by rcases hε with h | h <;> rw [h] <;> simp
  have hzAx : ∀ x : Fin n → k, h[z, B *ᵥ x] = ε * h[z, x] := by
    intro x
    have h1 : ε * h[z, B *ᵥ x] = h[z, x] := by
      have h2 : h[B *ᵥ z, B *ᵥ x] = (1 : k) * h[z, x] := hiso z x
      rw [hBz, one_mul, hform_smul_left, hσε] at h2
      exact h2
    calc h[z, B *ᵥ x] = ε * (ε * h[z, B *ᵥ x]) := by rw [← mul_assoc, hεε, one_mul]
      _ = ε * h[z, x] := by rw [h1]
  have hmv : ∀ x, (B * N) *ᵥ x = (N * B) *ᵥ x := by
    intro x
    have hs1 : a • (h[z, x] • (ε • z)) = a • (ε • (h[z, x] • z)) := by
      rw [smul_smul_swap (h[z, x]) ε]
    have hs2 : a • (ε • (h[z, x] • z)) = a • ((ε * h[z, x]) • z) := by
      have h : ε • (h[z, x] • z) = (ε * h[z, x]) • z := smul_smul ε (h[z, x]) z
      rw [h]
    calc (B * N) *ᵥ x = B *ᵥ (N *ᵥ x) := (Matrix.mulVec_mulVec ..).symm
      _ = B *ᵥ (a • (h[z, x] • z)) := by rw [hN]
      _ = a • (h[z, x] • (B *ᵥ z)) := by rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
      _ = a • (h[z, x] • (ε • z)) := by rw [hBz]
      _ = a • (ε • (h[z, x] • z)) := hs1
      _ = a • ((ε * h[z, x]) • z) := hs2
      _ = a • (h[z, B *ᵥ x] • z) := by rw [hzAx]
      _ = N *ᵥ (B *ᵥ x) := (hN (B *ᵥ x)).symm
      _ = (N * B) *ᵥ x := Matrix.mulVec_mulVec ..
  ext i j
  have h := congrFun (hmv (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.col_apply] using h

private lemma commute_rank_two {B N : Matrix (Fin n) (Fin n) k} {v w : Fin n → k}
    (hBv : B *ᵥ v = w) (hBw : B *ᵥ w = v)
    (hN : ∀ x, N *ᵥ x = h[v, x] • w - h[w, x] • v)
    (hadj : ∀ x y, h[B *ᵥ x, y] = (-1 : k) * h[x, B *ᵥ y]) : B * N = N * B := by
  have hmv : ∀ x, (B * N) *ᵥ x = (N * B) *ᵥ x := by
    intro x
    have hv1 : h[v, B *ᵥ x] = -h[w, x] := by
      have h1 : h[B *ᵥ v, x] = (-1 : k) * h[v, B *ᵥ x] := hadj v x
      rw [hBv, neg_one_mul] at h1
      rw [h1]; ring
    have hw1 : h[w, B *ᵥ x] = -h[v, x] := by
      have h1 : h[B *ᵥ w, x] = (-1 : k) * h[w, B *ᵥ x] := hadj w x
      rw [hBw, neg_one_mul] at h1
      rw [h1]; ring
    calc (B * N) *ᵥ x = B *ᵥ (N *ᵥ x) := (Matrix.mulVec_mulVec ..).symm
      _ = B *ᵥ (h[v, x] • w - h[w, x] • v) := by rw [hN]
      _ = h[v, x] • (B *ᵥ w) - h[w, x] • (B *ᵥ v) := by
          rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul]
      _ = h[v, x] • v - h[w, x] • w := by rw [hBw, hBv]
      _ = h[v, B *ᵥ x] • w - h[w, B *ᵥ x] • v := by
          rw [hv1, hw1, neg_smul, neg_smul]; abel
      _ = N *ᵥ (B *ᵥ x) := (hN (B *ᵥ x)).symm
      _ = (N * B) *ᵥ x := Matrix.mulVec_mulVec ..
  ext i j
  have h := congrFun (hmv (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.col_apply] using h

private lemma matrix_ne_zero_of_isUnit_det {k : Type*} [Field k] {n : ℕ}
    [instN : Nonempty (Fin n)] {Φ : Matrix (Fin n) (Fin n) k} (hΦ : IsUnit Φ.det) : Φ ≠ 0 := by
  intro h
  rw [h, Matrix.det_zero] at hΦ
  exact hΦ.ne_zero rfl

private lemma isSquare_of_mul_sigma_eq_sq {K : Type*} [Field K] [instF : Fintype K]
    (hk : ringChar K ≠ 2) (σ : K ≃+* K) (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1) {μ κ : K}
    (hμ : μ ≠ 0) (hκfix : σ κ = κ) (hκ2 : μ * σ μ = κ ^ 2) : IsSquare μ := by
  have hμ2 : μ ^ (Fintype.card K / 2) = 1 :=
    CFSG.ProperTwoGeneratedCore.Lemma37.pow_card_div_two_eq_one_of_mul_apply_eq_sq hk σ hσ1 hσ2
      hμ hκfix hκ2
  exact (FiniteField.isSquare_iff hk hμ).mpr hμ2

private theorem exists_sq_zero_unitary_hermitian [instF : Fintype k] [instN : Nonempty (Fin n)]
    (hk : ringChar k ≠ 2) (hn : 3 ≤ n)
    (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) (hΦ : IsUnit Φ.det) (hΦh : Φ = (Φ.map σ)ᵀ)
    {A : Matrix (Fin n) (Fin n) k} {μ κ : k} (hμ : μ ≠ 0) (hA2 : A * A = μ • 1)
    (hAΦ : (A.map σ)ᵀ * Φ * A = κ • Φ) :
    ∃ N : Matrix (Fin n) (Fin n) k, N ≠ 0 ∧ N * N = 0 ∧ A * N = N * A ∧
      (N.map σ)ᵀ * Φ + Φ * N = 0 := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have hinv : ∀ x : k, σ (σ x) = x := fun x => RingEquiv.congr_fun hσ2 x
  have hΦne : Φ ≠ 0 := matrix_ne_zero_of_isUnit_det hΦ
  have hT : (A.map σ)ᵀ * Φ = (κ * μ⁻¹) • (Φ * A) := by
    have hAinv : A * (μ⁻¹ • A) = 1 := by
      rw [Matrix.mul_smul, hA2, smul_smul, inv_mul_cancel₀ hμ, one_smul]
    have hL : (A.map σ)ᵀ * Φ * A * (μ⁻¹ • A) = (A.map σ)ᵀ * Φ := by
      simp only [Matrix.mul_assoc, hAinv, Matrix.mul_one]
    have hmul : (A.map σ)ᵀ * Φ * A * (μ⁻¹ • A) = (κ • Φ) * (μ⁻¹ • A) := by rw [hAΦ]
    have hR : (κ • Φ) * (μ⁻¹ • A) = (κ * μ⁻¹) • (Φ * A) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    exact hL.symm.trans (hmul.trans hR)
  have hAadj : ∀ x y : Fin n → k, h[A *ᵥ x, y] = (κ * μ⁻¹) * h[x, A *ᵥ y] := by
    intro x y
    calc h[A *ᵥ x, y]
        = ((A.map σ) *ᵥ fun i => σ (x i)) ᵥ* Φ ⬝ᵥ y := by
          rw [Matrix.dotProduct_mulVec, map_mulVec_apply]
      _ = (fun i => σ (x i)) ᵥ* ((A.map σ)ᵀ * Φ) ⬝ᵥ y := by rw [Matrix.vecMul_mulVec]
      _ = (fun i => σ (x i)) ⬝ᵥ (((A.map σ)ᵀ * Φ) *ᵥ y) := (Matrix.dotProduct_mulVec _ _ _).symm
      _ = (fun i => σ (x i)) ⬝ᵥ (((κ * μ⁻¹) • (Φ * A)) *ᵥ y) := by rw [hT]
      _ = (κ * μ⁻¹) * h[x, A *ᵥ y] := by
          rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec, dotProduct_smul, smul_eq_mul]
  have hκfix : σ κ = κ := by
    have hmap := congrArg (fun M : Matrix (Fin n) (Fin n) k => M.map σ) hAΦ
    have hL1 : ((A.map σ)ᵀ).map σ = Aᵀ := by
      rw [transpose_map (M := A.map σ), map_map_apply hσ2]
    have hL : ((A.map σ)ᵀ * Φ * A).map σ = Aᵀ * Φ.map σ * A.map σ := by
      rw [Matrix.map_mul, Matrix.map_mul, hL1]
    have hR : (κ • Φ).map σ = σ κ • Φ.map σ := map_smul_apply κ Φ
    rw [hL, hR] at hmap
    have htr := congrArg (fun M : Matrix (Fin n) (Fin n) k => Mᵀ) hmap
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_smul, ← hΦh, ← Matrix.mul_assoc] at htr
    have hκeq : κ • Φ = σ κ • Φ := hAΦ.symm.trans htr
    have h0 : (κ - σ κ) • Φ = 0 := by rw [sub_smul, hκeq, sub_self]
    have hzero : κ - σ κ = 0 := by
      rcases smul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hΦne
    linear_combination -hzero
  have hNκ : σ (κ * μ⁻¹) * (κ * μ⁻¹) = 1 := by
    obtain ⟨y, hy0⟩ : ∃ y : Fin n → k, y ≠ 0 := by
      refine ⟨Pi.single ⟨0, by omega⟩ 1, fun h => ?_⟩
      have h1 := congrFun h ⟨0, by omega⟩
      simp at h1
    have hsurj : ∀ v : Fin n → k, ∃ x, A *ᵥ x = v := by
      intro v
      refine ⟨μ⁻¹ • (A *ᵥ v), ?_⟩
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hA2, Matrix.smul_mulVec, Matrix.one_mulVec,
        smul_smul, inv_mul_cancel₀ hμ, one_smul]
    obtain ⟨x, hx⟩ : ∃ x : Fin n → k, h[y, A *ᵥ x] ≠ 0 := by
      by_contra h
      push Not at h
      have hv : ∀ v : Fin n → k, h[y, v] = 0 := by
        intro v
        obtain ⟨x, rfl⟩ := hsurj v
        exact h x
      exact hy0 (hform_nondegenerate (σ := σ) hΦ (x := y) hv)
    have hkey : h[y, A *ᵥ x] = σ (κ * μ⁻¹) * (κ * μ⁻¹) * h[y, A *ᵥ x] := by
      calc h[y, A *ᵥ x] = σ (h[A *ᵥ x, y]) := hform_comm hΦh hσ2 (A *ᵥ x) y
        _ = σ ((κ * μ⁻¹) * h[x, A *ᵥ y]) := by rw [hAadj x y]
        _ = σ (κ * μ⁻¹) * σ (h[x, A *ᵥ y]) := by rw [map_mul]
        _ = σ (κ * μ⁻¹) * h[A *ᵥ y, x] := by rw [← hform_comm hΦh hσ2 x (A *ᵥ y)]
        _ = σ (κ * μ⁻¹) * ((κ * μ⁻¹) * h[y, A *ᵥ x]) := by rw [hAadj y x]
        _ = σ (κ * μ⁻¹) * (κ * μ⁻¹) * h[y, A *ᵥ x] := by ring
    have hz : (σ (κ * μ⁻¹) * (κ * μ⁻¹) - 1) * h[y, A *ᵥ x] = 0 := by
      rw [sub_mul, one_mul, ← hkey, sub_self]
    have := (mul_eq_zero.mp hz).resolve_right hx
    linear_combination this
  have hmuσ : σ μ ≠ 0 := (map_ne_zero σ).mpr hμ
  have hκ0 : κ ≠ 0 := by
    intro h
    have := hNκ
    rw [h, zero_mul, map_zero, zero_mul] at this
    exact zero_ne_one this
  have hκ2 : μ * σ μ = κ ^ 2 := by
    have hinvμ : σ (μ⁻¹) = (σ μ)⁻¹ := by
      have h1 : σ μ * σ (μ⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ hμ, map_one]
      exact eq_inv_of_mul_eq_one_right h1
    have hN' : σ κ * (σ μ)⁻¹ * (κ * μ⁻¹) = 1 := by
      rw [← hinvμ, ← map_mul]
      exact hNκ
    have hmul := congrArg (fun t : k => t * (σ μ * μ)) hN'
    field_simp at hmul
    rw [hκfix] at hmul
    rw [pow_two]
    rw [hmul]
    ring
  have hμsq : IsSquare μ :=
    isSquare_of_mul_sigma_eq_sq (instF := instF) hk σ hσ1 hσ2 hμ hκfix hκ2
  obtain ⟨m, hm⟩ := hμsq
  have hm' : m * m = μ := by rw [hm]
  have hm0 : m ≠ 0 := by
    intro h
    have h1 : (0 : k) = μ := by rw [← hm', h, mul_zero]
    exact hμ h1.symm
  obtain ⟨A₁, hA₁def, hA1sq, hA1Φ⟩ : ∃ A₁ : Matrix (Fin n) (Fin n) k, A₁ = m⁻¹ • A ∧
      A₁ * A₁ = 1 ∧ (A₁.map σ)ᵀ * Φ * A₁ = (σ m⁻¹ * m⁻¹ * κ) • Φ := by
    refine ⟨m⁻¹ • A, rfl, ?_, ?_⟩
    · calc (m⁻¹ • A) * (m⁻¹ • A) = (m⁻¹ * m⁻¹) • (A * A) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        _ = (m⁻¹ * m⁻¹ * μ) • (1 : Matrix (Fin n) (Fin n) k) := by rw [hA2, smul_smul]
        _ = 1 := by
            have h1 : m⁻¹ * m⁻¹ * (m * m) = 1 := by field_simp
            rw [hm'] at h1
            rw [h1, one_smul]
    · calc ((m⁻¹ • A).map σ)ᵀ * Φ * (m⁻¹ • A)
          = (σ m⁻¹ • (A.map σ)ᵀ) * Φ * (m⁻¹ • A) := by
              rw [map_smul_apply, Matrix.transpose_smul]
        _ = σ m⁻¹ • ((A.map σ)ᵀ * Φ * (m⁻¹ • A)) := by
              rw [Matrix.smul_mul, Matrix.smul_mul]
        _ = σ m⁻¹ • (m⁻¹ • ((A.map σ)ᵀ * Φ * A)) := by rw [Matrix.mul_smul]
        _ = (σ m⁻¹ * m⁻¹) • ((A.map σ)ᵀ * Φ * A) := by rw [smul_smul]
        _ = (σ m⁻¹ * m⁻¹ * κ) • Φ := by rw [hAΦ, smul_smul]
  have hAeq : A = m • A₁ := by
    rw [hA₁def, smul_smul, mul_inv_cancel₀ hm0, one_smul]
  have hσm : σ m⁻¹ * σ m = 1 := by rw [← map_mul, inv_mul_cancel₀ hm0, map_one]
  have hk1sq : (σ m⁻¹ * m⁻¹ * κ) ^ 2 = 1 := by
    have ht : m * σ m ≠ 0 := mul_ne_zero hm0 ((map_ne_zero σ).mpr hm0)
    have h1 : (m * σ m) ^ 2 = κ ^ 2 := by
      rw [mul_pow, pow_two m, hm', ← map_pow, pow_two m, hm', hκ2]
    have h2 : (σ m⁻¹ * m⁻¹ * κ) * (m * σ m) = κ := by
      calc σ m⁻¹ * m⁻¹ * κ * (m * σ m) = (σ m⁻¹ * σ m) * (m⁻¹ * m) * κ := by ring
        _ = κ := by rw [hσm, inv_mul_cancel₀ hm0, one_mul, one_mul]
    have hκ0' : κ ≠ 0 := by
      intro h
      rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at h1
      rw [pow_two] at h1
      exact ht (mul_self_eq_zero.mp h1)
    have h3 : (σ m⁻¹ * m⁻¹ * κ) ^ 2 * (m * σ m) ^ 2 = 1 * (m * σ m) ^ 2 := by
      rw [← mul_pow, h2, h1, one_mul]
    exact mul_right_cancel₀ (pow_ne_zero 2 ht) h3
  have hk1pm : (σ m⁻¹ * m⁻¹ * κ) = 1 ∨ (σ m⁻¹ * m⁻¹ * κ) = -1 := by
    have h := hk1sq
    rw [pow_two] at h
    have h' : (σ m⁻¹ * m⁻¹ * κ - 1) * (σ m⁻¹ * m⁻¹ * κ + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h1
    · left; linear_combination h1
    · right; linear_combination h1
  let Vp : Submodule k (Fin n → k) := LinearMap.ker (A₁.mulVecLin - 1)
  let Vm : Submodule k (Fin n → k) := LinearMap.ker (A₁.mulVecLin + 1)
  have hVp : ∀ x, x ∈ Vp ↔ A₁ *ᵥ x = x := fun x => mem_ker_sub_one_iff x
  have hVm : ∀ x, x ∈ Vm ↔ A₁ *ᵥ x = (-1 : k) • x := fun x => mem_ker_add_one_neg_iff x
  have hVsup : Vp ⊔ Vm = ⊤ := sup_ker_eq_top hA1sq h2
  have hVinf : Vp ⊓ Vm = ⊥ := inf_ker_eq_bot h2
  have hVfin : Module.finrank k Vp + Module.finrank k Vm = n := finrank_ker_add hA1sq h2
  have hVsum : Vp ≠ ⊥ ∨ Vm ≠ ⊥ := by
    by_contra h
    push Not at h
    rw [h.1, h.2, bot_sup_eq] at hVsup
    have : n = 0 := by
      rw [← hVfin, h.1, h.2]
      simp
    omega
  rcases hk1pm with hk1 | hk1
  ·
    have hA1Φ1 : (A₁.map σ)ᵀ * Φ * A₁ = (1 : k) • Φ := by rw [← hk1]; exact hA1Φ
    have hiso : ∀ x y, h[A₁ *ᵥ x, A₁ *ᵥ y] = (1 : k) * h[x, y] := by
      intro x y
      rw [hform_isometry hA1Φ, hk1]
    obtain ⟨a, ha0, ha⟩ : ∃ a : k, a ≠ 0 ∧ σ a = -a := by
      obtain ⟨d, hd⟩ : ∃ d : k, σ d ≠ d := by
        by_contra h
        push Not at h
        exact hσ1 (RingEquiv.ext h)
      exact ⟨d - σ d, sub_ne_zero.mpr (Ne.symm hd), by rw [map_sub, hinv]; ring⟩
    have hbig : 2 ≤ Module.finrank k Vp ∨ 2 ≤ Module.finrank k Vm := by omega
    rcases hbig with hbig | hbig
    · obtain ⟨z, hzV, hz0, hzz⟩ :=
        exists_isotropic_of_finrank hΦh hσ2 hσ1 hbig
      obtain ⟨N, hN0, hN2, hNsk, hNact⟩ :=
        rank_one_construction hΦ hΦh hσ2 ha0 ha hz0 hzz
      have hBz : A₁ *ᵥ z = (1 : k) • z := by rw [(hVp z).mp hzV, one_smul]
      have hcomm : A₁ * N = N * A₁ := commute_rank_one_self (Or.inl rfl) hBz hNact hiso
      refine ⟨N, hN0, hN2, ?_, hNsk⟩
      calc A * N = (m • A₁) * N := by rw [hAeq]
        _ = m • (A₁ * N) := Matrix.smul_mul ..
        _ = m • (N * A₁) := by rw [hcomm]
        _ = N * (m • A₁) := (Matrix.mul_smul ..).symm
        _ = N * A := by rw [hAeq]
    · obtain ⟨z, hzV, hz0, hzz⟩ :=
        exists_isotropic_of_finrank hΦh hσ2 hσ1 hbig
      obtain ⟨N, hN0, hN2, hNsk, hNact⟩ :=
        rank_one_construction hΦ hΦh hσ2 ha0 ha hz0 hzz
      have hBz : A₁ *ᵥ z = (-1 : k) • z := (hVm z).mp hzV
      have hcomm : A₁ * N = N * A₁ := commute_rank_one_self (Or.inr rfl) hBz hNact hiso
      refine ⟨N, hN0, hN2, ?_, hNsk⟩
      calc A * N = (m • A₁) * N := by rw [hAeq]
        _ = m • (A₁ * N) := Matrix.smul_mul ..
        _ = m • (N * A₁) := by rw [hcomm]
        _ = N * (m • A₁) := (Matrix.mul_smul ..).symm
        _ = N * A := by rw [hAeq]
  ·
    have hA1Φm : (A₁.map σ)ᵀ * Φ * A₁ = (-1 : k) • Φ := by rw [← hk1]; exact hA1Φ
    have hadj : ∀ x y, h[A₁ *ᵥ x, y] = (-1 : k) * h[x, A₁ *ᵥ y] := by
      intro x y
      rw [hform_adjoint hA1sq hA1Φ, hk1]
    have hVp_iso : ∀ x ∈ Vp, ∀ y ∈ Vp, h[x, y] = 0 :=
      fun x hx y hy => hform_eq_zero_ker_sub_one h2 hA1sq hA1Φm hx hy
    have hVm_iso : ∀ x ∈ Vm, ∀ y ∈ Vm, h[x, y] = 0 :=
      fun x hx y hy => hform_eq_zero_ker_add_one h2 hA1sq hA1Φm hx hy
    have hnz : ∃ y : Fin n → k, y ≠ 0 := by
      refine ⟨Pi.single ⟨0, by omega⟩ 1, fun h => ?_⟩
      have h1 := congrFun h ⟨0, by omega⟩
      simp at h1
    have hVp_ne : Vp ≠ ⊥ := by
      intro hbot
      obtain ⟨y, hy0⟩ := hnz
      have htop : Vm = ⊤ := by rw [← hVsup, hbot, bot_sup_eq]
      have hzero : ∀ x : Fin n → k, h[y, x] = 0 := by
        intro x
        exact hVm_iso y (htop ▸ Submodule.mem_top) x (htop ▸ Submodule.mem_top)
      exact hy0 (hform_nondegenerate (σ := σ) hΦ (x := y) hzero)
    have hVm_ne : Vm ≠ ⊥ := by
      intro hbot
      obtain ⟨y, hy0⟩ := hnz
      have htop : Vp = ⊤ := by rw [← hVsup, hbot, sup_bot_eq]
      have hzero : ∀ x : Fin n → k, h[y, x] = 0 := by
        intro x
        exact hVp_iso y (htop ▸ Submodule.mem_top) x (htop ▸ Submodule.mem_top)
      exact hy0 (hform_nondegenerate (σ := σ) hΦ (x := y) hzero)
    obtain ⟨p₀, hp₀V, hp₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVp_ne
    obtain ⟨q₀, hq₀V, hq₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVm_ne
    have hpair : ∃ p ∈ Vp, p ≠ 0 ∧ ∃ q ∈ Vm, q ≠ 0 ∧ h[p, q] = 0 := by
      rcases Nat.lt_or_ge (Module.finrank k Vp) 2 with hlt | hge
      ·
        have hVm2 : 2 ≤ Module.finrank k Vm := by omega
        have hfun : ∃ y ∈ Vm, h[p₀, y] ≠ 0 := by
          by_contra h
          push Not at h
          have hv : ∀ v : Fin n → k, h[p₀, v] = 0 := by
            intro v
            have hvmem : v ∈ Vp ⊔ Vm := by rw [hVsup]; exact Submodule.mem_top
            rw [Submodule.mem_sup] at hvmem
            obtain ⟨vp, hvp, vm, hvm, hsum⟩ := hvmem
            rw [← hsum, hform_add_right, hVp_iso p₀ hp₀V vp hvp, h vm hvm, add_zero]
          exact hp₀0 (hform_nondegenerate (σ := σ) hΦ (x := p₀) hv)
        obtain ⟨q, hqV, hq0, hpq⟩ := exists_ker_ne_zero hVm2 hfun
        exact ⟨p₀, hp₀V, hp₀0, q, hqV, hq0, hpq⟩
      ·
        have hfun : ∃ y ∈ Vp, h[q₀, y] ≠ 0 := by
          by_contra h
          push Not at h
          have hv : ∀ v : Fin n → k, h[q₀, v] = 0 := by
            intro v
            have hvmem : v ∈ Vp ⊔ Vm := by rw [hVsup]; exact Submodule.mem_top
            rw [Submodule.mem_sup] at hvmem
            obtain ⟨vp, hvp, vm, hvm, hsum⟩ := hvmem
            rw [← hsum, hform_add_right, h vp hvp, hVm_iso q₀ hq₀V vm hvm, add_zero]
          exact hq₀0 (hform_nondegenerate (σ := σ) hΦ (x := q₀) hv)
        obtain ⟨p, hpV, hp0, hqp⟩ := exists_ker_ne_zero hge hfun
        have hpq : h[p, q₀] = 0 := by rw [hform_comm hΦh hσ2, hqp, map_zero]
        exact ⟨p, hpV, hp0, q₀, hq₀V, hq₀0, hpq⟩
    obtain ⟨p, hpV, hp0, q, hqV, hq0, hpq⟩ := hpair
    have hA1p : A₁ *ᵥ p = p := (hVp p).mp hpV
    have hA1q : A₁ *ᵥ q = (-1 : k) • q := (hVm q).mp hqV
    have hqneg : A₁ *ᵥ q = -q := by rw [hA1q, neg_one_smul]
    have hqp : h[q, p] = 0 := by rw [hform_comm hΦh hσ2, hpq, map_zero]
    have hA1v : A₁ *ᵥ (p + q) = p - q := by
      rw [Matrix.mulVec_add, hA1p, hqneg]
      abel
    have hA1w : A₁ *ᵥ (p - q) = p + q := by
      rw [Matrix.mulVec_sub, hA1p, hqneg]
      abel
    have hpp : h[p, p] = 0 := hVp_iso p hpV p hpV
    have hqq : h[q, q] = 0 := hVm_iso q hqV q hqV
    have hvv : h[p + q, p + q] = 0 := by
      rw [hform_sum4, hpp, hpq, hqp, hqq]
      ring
    have hsub : p - q = p + (-1 : k) • q := by rw [neg_one_smul, sub_eq_add_neg]
    have hpsm : h[p, (-1 : k) • q] = (-1 : k) * h[p, q] := hform_smul_right (-1) p q
    have hqsm : h[q, (-1 : k) • q] = (-1 : k) * h[q, q] := hform_smul_right (-1) q q
    have hqpsm : h[(-1 : k) • q, p] = σ (-1) * h[q, p] := hform_smul_left (-1) q p
    have hqqsm : h[(-1 : k) • q, (-1 : k) • q] = σ (-1) * ((-1 : k) * h[q, q]) := by
      rw [hform_smul_left, hform_smul_right]
    have hvw : h[p + q, p - q] = 0 := by
      rw [hsub, hform_sum4, hpsm, hqsm, hpp, hpq, hqp, hqq]
      ring
    have hww : h[p - q, p - q] = 0 := by
      rw [hsub, hform_sum4, hpsm, hqpsm, hqqsm, hpp, hpq, hqp, hqq]
      ring
    have hvne : p + q ≠ 0 := by
      intro h
      have hw0 : p - q = 0 := by rw [← hA1v, h, Matrix.mulVec_zero]
      have h2p : (2 : k) • p = 0 := by
        have h4 : (2 : k) • p = (p + q) + (p - q) := by rw [two_smul]; abel
        rw [h4, h, hw0, add_zero]
      exact hp0 ((smul_eq_zero.mp h2p).resolve_left h2)
    have hwspan : ∀ c : k, p - q ≠ c • (p + q) := by
      intro c hc
      have h1 : p + q = c • (p - q) := by
        calc p + q = A₁ *ᵥ (p - q) := hA1w.symm
          _ = A₁ *ᵥ (c • (p + q)) := by rw [hc]
          _ = c • (A₁ *ᵥ (p + q)) := by rw [Matrix.mulVec_smul]
          _ = c • (p - q) := by rw [hA1v]
      have hcz : (c ^ 2 - 1) • (p + q) = 0 := by
        have h3 : p + q = c ^ 2 • (p + q) := h1.trans (by rw [hc, smul_smul, pow_two])
        rw [sub_smul, one_smul, ← h3, sub_self]
      have hc2 : c ^ 2 = 1 := by
        rcases smul_eq_zero.mp hcz with h | h
        · linear_combination h
        · exact absurd h hvne
      have hcp : c = 1 ∨ c = -1 := by
        rw [pow_two] at hc2
        have h' : (c - 1) * (c + 1) = 0 := by linear_combination hc2
        rcases mul_eq_zero.mp h' with h1 | h1
        · left; linear_combination h1
        · right; linear_combination h1
      rcases hcp with h1 | h1
      · rw [h1, one_smul] at hc
        have hzero : (2 : k) • q = 0 := by
          have h3 : p - q - (p + q) = 0 := by rw [hc, sub_self]
          rwa [show p - q - (p + q) = -((2 : k) • q) from by rw [two_smul]; abel, neg_eq_zero]
            at h3
        exact hq0 ((smul_eq_zero.mp hzero).resolve_left h2)
      · rw [h1] at hc
        have hzero : (2 : k) • p = 0 := by
          have h3 : (p + q) + (p - q) = 0 := by
            rw [hc]; simp only [neg_one_smul]; abel
          rwa [show (p + q) + (p - q) = (2 : k) • p from by rw [two_smul]; abel] at h3
        exact hp0 ((smul_eq_zero.mp hzero).resolve_left h2)
    obtain ⟨N, hN0, hN2, hNsk, hNact⟩ :=
      rank_two_construction hΦ hΦh hσ2 hvne hwspan hvv hww hvw
    have hcomm : A₁ * N = N * A₁ := commute_rank_two hA1v hA1w hNact hadj
    refine ⟨N, hN0, hN2, ?_, hNsk⟩
    calc A * N = (m • A₁) * N := by rw [hAeq]
      _ = m • (A₁ * N) := Matrix.smul_mul ..
      _ = m • (N * A₁) := by rw [hcomm]
      _ = N * (m • A₁) := (Matrix.mul_smul ..).symm
      _ = N * A := by rw [hAeq]

end Form

theorem exists_sq_zero_commute_unitary {k : Type*} [Field k] [Finite k] (hk : ringChar k ≠ 2)
    {n : ℕ} (hn : 3 ≤ n) {σ : k ≃+* k} (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1)
    {A Φ : Matrix (Fin n) (Fin n) k} {μ c κ : k} (hΦ : IsUnit Φ.det) (hμ : μ ≠ 0)
    (hA2 : A * A = μ • 1) (hΦc : Φ = c • (Φ.map σ)ᵀ) (hAΦ : (A.map σ)ᵀ * Φ * A = κ • Φ) :
    ∃ N : Matrix (Fin n) (Fin n) k, N ≠ 0 ∧ N * N = 0 ∧ A * N = N * A ∧
      (N.map σ)ᵀ * Φ + Φ * N = 0 := by
  classical
  have hinv : ∀ x : k, σ (σ x) = x := fun x => RingEquiv.congr_fun hσ2 x
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσ1
  have hΦne : Φ ≠ 0 := matrix_ne_zero_of_isUnit_det (instN := ⟨⟨0, by omega⟩⟩) hΦ
  have hc0 : c ≠ 0 := by
    intro h
    apply hΦne
    rw [hΦc, h, zero_smul]
  have hΦσ : (Φ.map σ)ᵀ = c⁻¹ • Φ := by
    have h1 : c⁻¹ • Φ = c⁻¹ • (c • (Φ.map σ)ᵀ) :=
      congrArg (fun M : Matrix (Fin n) (Fin n) k => c⁻¹ • M) hΦc
    rw [smul_smul, inv_mul_cancel₀ hc0, one_smul] at h1
    exact h1.symm
  have hcc : c * σ c = 1 := by
    have h1 : Φ.map σ = σ c • Φᵀ := by
      calc Φ.map σ = (c • (Φ.map σ)ᵀ).map σ := by rw [← hΦc]
        _ = σ c • ((Φ.map σ)ᵀ).map σ := by rw [map_smul_apply]
        _ = σ c • ((Φ.map σ).map σ)ᵀ := by rw [transpose_map]
        _ = σ c • Φᵀ := by rw [map_map_apply hσ2]
    have h2 : (Φ.map σ)ᵀ = σ c • Φ := by
      have h3 := congrArg (fun M : Matrix (Fin n) (Fin n) k => Mᵀ) h1
      rwa [Matrix.transpose_smul, Matrix.transpose_transpose] at h3
    have h3 : σ c • Φ = c⁻¹ • Φ := h2.symm.trans hΦσ
    have h4 : (σ c - c⁻¹) • Φ = 0 := by rw [sub_smul, h3, sub_self]
    have h5 : σ c - c⁻¹ = 0 := by
      rcases smul_eq_zero.mp h4 with h | h
      · exact h
      · exact absurd h hΦne
    have h6 : σ c = c⁻¹ := sub_eq_zero.mp h5
    rw [h6, mul_inv_cancel₀ hc0]
  obtain ⟨b, hb0, hbσ⟩ :=
    CFSG.ComponentClassification.CatalogueBLinearTwoFixed.exists_scalar_hilbert90 k σ hord c hcc
  have hb0' : b⁻¹ ≠ 0 := inv_ne_zero hb0
  have hσb : σ b⁻¹ = c * b⁻¹ := by
    have h1 : σ b * σ b⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hb0, map_one]
    have h2 : σ b⁻¹ = (σ b)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2, hbσ, mul_inv, inv_inv]
  have hΦ₁ : b⁻¹ • Φ = ((b⁻¹ • Φ).map σ)ᵀ := by
    rw [map_smul_apply, Matrix.transpose_smul, hΦσ, hσb, smul_smul]
    have hcoe : c * b⁻¹ * c⁻¹ = b⁻¹ := by field_simp
    rw [hcoe]
  have hdet : IsUnit (b⁻¹ • Φ).det := by
    rw [Matrix.det_smul, Fintype.card_fin]
    exact IsUnit.mul (isUnit_iff_ne_zero.mpr (pow_ne_zero n hb0')) hΦ
  have hAΦν : (A.map σ)ᵀ * (b⁻¹ • Φ) * A = κ • (b⁻¹ • Φ) := by
    calc (A.map σ)ᵀ * (b⁻¹ • Φ) * A = b⁻¹ • ((A.map σ)ᵀ * Φ * A) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = b⁻¹ • (κ • Φ) := by rw [hAΦ]
      _ = κ • (b⁻¹ • Φ) := by rw [smul_smul, smul_smul]; congr 1; ring
  obtain ⟨N, hN0, hN2, hNcomm, hNsk⟩ :=
    exists_sq_zero_unitary_hermitian (Φ := b⁻¹ • Φ) (A := A) (μ := μ) (κ := κ)
      (instF := Fintype.ofFinite k) (instN := ⟨⟨0, by omega⟩⟩) hk hn hσ2 hσ1 hdet hΦ₁ hμ hA2
      hAΦν
  refine ⟨N, hN0, hN2, hNcomm, ?_⟩
  have hs1 : (N.map σ)ᵀ * (b⁻¹ • Φ) = b⁻¹ • ((N.map σ)ᵀ * Φ) := Matrix.mul_smul ..
  have hs2 : (b⁻¹ • Φ) * N = b⁻¹ • (Φ * N) := Matrix.smul_mul ..
  rw [hs1, hs2, ← smul_add] at hNsk
  exact (smul_eq_zero.mp hNsk).resolve_left hb0'

end CFSG.LocalAnalysis.WeakClosure81.PSLOuter

end

