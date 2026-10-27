module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpCent
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotBlocks
public import CFSG.Sporadic.Suz.Setup
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBInvolution
public import CFSG.Sporadic.Suz.W64Spec

public section

namespace CFSG.StandardType.SpRootTv

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.Open (StatedSp)
open CFSG.ComponentClassification.Burgoyne.Sp
open CFSG.SeitzReduction.SymplecticPilot
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (formJ)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)

section Matrix

variable {K : Type} [Field K] {m : ℕ}

theorem gram_of_mem (g : StatedSp m K) :
    (mat m K g)ᵀ * formJ m K * mat m K g = formJ m K :=
  mem_statedSp_iff.mp g.2

theorem mat_transvSp (w : Fin m ⊕ Fin m → K) :
    mat m K (transvSp w 1) = 1 + transvN w := by
  rw [mat_apply, coe_transvSp, one_smul]

theorem transvN_mul_eq (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
    (hM : Mᵀ * formJ m K * M = formJ m K) (w : Fin m ⊕ Fin m → K) :
    transvN (M *ᵥ w) * M = M * transvN w := by
  unfold transvN
  rw [Matrix.vecMulVec_mul, Matrix.mul_vecMulVec, Matrix.vecMul_vecMul]
  congr 1
  rw [← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hM]

theorem conj_transvSp (g : StatedSp m K) (w : Fin m ⊕ Fin m → K) :
    g * transvSp w 1 * g⁻¹ = transvSp (mat m K g *ᵥ w) 1 := by
  rw [mul_inv_eq_iff_eq_mul]
  apply mat_injective
  rw [map_mul, map_mul, mat_transvSp, mat_transvSp, mul_add, add_mul, mul_one, one_mul,
    transvN_mul_eq (mat m K g) (gram_of_mem g) w]

theorem vecMul_formJ_dotProduct (w y : Fin m ⊕ Fin m → K) :
    (w ᵥ* formJ m K) ⬝ᵥ y = form w y := by
  rw [form, Matrix.dotProduct_mulVec]
  rfl

theorem transvSp_mul_self [CharP K 2] (w : Fin m ⊕ Fin m → K) :
    transvSp w 1 * transvSp w 1 = 1 := by
  apply mat_injective
  have h2 : transvN w + transvN w = 0 := by
    rw [← two_smul K (transvN w), show (2 : K) = 0 from by exact_mod_cast CharP.cast_eq_zero K 2,
      zero_smul]
  have e : (1 + transvN w) * (1 + transvN w) =
      1 + (transvN w + transvN w) + transvN w * transvN w := by
    noncomm_ring
  rw [map_mul, mat_transvSp, map_one, e, h2, (transvN_conds w).2.2]
  simp

theorem transvSp_comm [CharP K 2] {w w' : Fin m ⊕ Fin m → K} (h : form w w' = 0) :
    transvSp w 1 * transvSp w' 1 = transvSp w' 1 * transvSp w 1 := by
  apply mat_injective
  have h' : form w' w = 0 := by rw [form_antisymm, h, neg_zero]
  have hN : ∀ x y : Fin m ⊕ Fin m → K, form x y = 0 → transvN x * transvN y = 0 := by
    intro x y hxy
    unfold transvN
    rw [Matrix.vecMulVec_mul_vecMulVec, vecMul_formJ_dotProduct, hxy, zero_smul]
    simp
  have h1 := hN w w' h
  have h2 := hN w' w h'
  have e1 : (1 + transvN w) * (1 + transvN w') =
      1 + transvN w + transvN w' + transvN w * transvN w' := by
    noncomm_ring
  have e2 : (1 + transvN w') * (1 + transvN w) =
      1 + transvN w + transvN w' + transvN w' * transvN w := by
    noncomm_ring
  rw [map_mul, map_mul, mat_transvSp, mat_transvSp, e1, e2, h1, h2, add_zero]

theorem transvSp_ne_one [CharP K 2] {w : Fin m ⊕ Fin m → K} (hw : w ≠ 0) :
    transvSp w 1 ≠ 1 := by
  intro h
  have hN : transvN w = 0 := by
    have h' := congrArg (mat m K) h
    rw [mat_transvSp, map_one] at h'
    simpa using h'
  obtain ⟨y, hy⟩ : ∃ y, form w y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hw
    funext a
    have h1 := form_single_right w (par a)
    rw [par_par, hcon (Pi.single (par a) 1)] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_right (sgn_ne_zero _)
  have hNy : transvN w *ᵥ y = 0 := by rw [hN, Matrix.zero_mulVec]
  rw [transvN_mulVec] at hNy
  rcases smul_eq_zero.mp hNy with h0 | h0
  · apply hy
    rw [pairedSympForm_eq] at h0
    exact h0
  · exact hw h0

theorem par_mem_coords {n : ℕ} {k : Fin n} {t : Fin n ⊕ Fin n} (ht : t ∈ coords k) :
    par t ∈ coords k := by
  rcases mem_coords.mp ht with rfl | rfl
  · exact mem_coords.mpr (Or.inr rfl)
  · exact mem_coords.mpr (Or.inl rfl)

theorem transvSp_mem_complSp {n : ℕ} (k : Fin n) (w : Fin n ⊕ Fin n → K)
    (hw : ∀ r ∈ coords k, w r = 0) :
    transvSp w 1 ∈ complSp K k := by
  rw [mem_complSp]
  intro r t hrt
  rw [mat_transvSp, Matrix.add_apply, Matrix.one_apply]
  have hcase : r ∈ coords k ∨ t ∈ coords k := by
    by_contra hc
    push Not at hc
    exact hrt ⟨hc.1, hc.2⟩
  have hN0 : transvN w r t = 0 := by
    unfold transvN
    rw [Matrix.vecMulVec_apply]
    rcases hcase with hr | ht
    · rw [hw r hr, zero_mul]
    · have h1 : (w ᵥ* formJ n K) t = w (par t) * sgn K (par t) := by
        rw [← form_single_right w t]
        rw [← vecMul_formJ_dotProduct, dotProduct_single, mul_one]
      rw [h1, hw (par t) (par_mem_coords ht), zero_mul, mul_zero]
  rw [hN0, add_zero]

end Matrix

section Group

theorem conj_mem_closure {H : Type*} [Group H] {A : Subgroup H} {S : Set H}
    (hS : ∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ ∈ S) {a : H} (ha : a ∈ A) {x : H}
    (hx : x ∈ Subgroup.closure S) : a * x * a⁻¹ ∈ Subgroup.closure S := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (hS a ha x hx)
  | one => rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  | mul x y _ _ ihx ihy =>
      have e : a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ihx =>
      have e : a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ihx

theorem le_normalizer_closure {H : Type*} [Group H] {A : Subgroup H} {S : Set H}
    (hS : ∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ ∈ S) :
    A ≤ Subgroup.normalizer ((Subgroup.closure S : Subgroup H) : Set H) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact conj_mem_closure hS ha
  · intro hh
    have h' := conj_mem_closure hS (A.inv_mem ha) hh
    have e : a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h := by group
    rw [e] at h'
    exact h'

theorem isPGroup_two_closure {H : Type*} [Group H] {S : Set H} (hsq : ∀ s ∈ S, s * s = 1)
    (hcomm : ∀ s ∈ S, ∀ s' ∈ S, s * s' = s' * s) : IsPGroup 2 (Subgroup.closure S) := by
  have hc1 : Subgroup.closure S ≤ Subgroup.centralizer S := by
    rw [Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    exact hcomm h hh s hs
  have hc2 : S ⊆ (Subgroup.centralizer ((Subgroup.closure S : Subgroup H) : Set H) : Set H) := by
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_centralizer_iff.mp (hc1 hh) s hs).symm
  have hc3 : Subgroup.closure S ≤
      Subgroup.centralizer ((Subgroup.closure S : Subgroup H) : Set H) :=
    (Subgroup.closure_le _).mpr hc2
  have hcomm' : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x :=
    fun x hx y hy => (Subgroup.mem_centralizer_iff.mp (hc3 hx) y hy).symm
  have hsq' : ∀ x ∈ Subgroup.closure S, x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hsq x hx
    | one => simp
    | mul x y hx hy ihx ihy =>
        have hxy : x * y = y * x := hcomm' x hx y hy
        calc x * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [← hxy]
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [ihx, ihy, one_mul]
    | inv x hx ihx =>
        have e : x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        rw [e, ihx, inv_one]
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one, pow_two]
  exact Subtype.ext (hsq' g.1 g.2)

end Group

end CFSG.StandardType.SpRootTv
