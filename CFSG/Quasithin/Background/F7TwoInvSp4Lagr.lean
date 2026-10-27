module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpInner

public section

namespace CFSG.Quasithin.F7Two

open Matrix Module Submodule CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem fromBlocks_one_mulVec_single_inl (C : Matrix (Fin 2) (Fin 2) K) (i : Fin 2) :
    (fromBlocks 1 C 0 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ Pi.single (Sum.inl i) 1 =
      Pi.single (Sum.inl i) 1 := by
  rw [mulVec_single_one]
  ext y
  rcases y with k | k <;> simp [col_apply, Pi.single_apply, one_apply]

omit [CharP K 2] in
theorem fromBlocks_one_mulVec_single_inr (C : Matrix (Fin 2) (Fin 2) K) (j : Fin 2) :
    (fromBlocks 1 C 0 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ Pi.single (Sum.inr j) 1 =
      Pi.single (Sum.inr j) 1 + ∑ i, C i j • (Pi.single (Sum.inl i) 1 : Fin 2 ⊕ Fin 2 → K) := by
  rw [mulVec_single_one]
  ext y
  rcases y with k | k
  · fin_cases k <;> simp [col_apply]
  · simp [col_apply, Pi.single_apply, one_apply]

theorem exists_conj_eq_ut {g : StatedSp 2 K} (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    ∃ (h : StatedSp 2 K) (C : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C), C ≠ 0 ∧
      h * g * h⁻¹ = upperUnipotentSp 2 K hC := by
  have hWiso := isTotallyIsotropic_displacement hg2
  obtain ⟨b, hb, hbW⟩ := exists_completeIsotropicFlag SymplecticFlag.pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate (finrank_standard (r := 2) (K := K)) hWiso
  obtain ⟨h, hh⟩ := exists_statedSp_mulVec_basis (b := Pi.basisFun K (Fin 2 ⊕ Fin 2))
    (b' := b) toMatrix_pairedSympForm hb
  have hB : ∀ x y, pairedSympForm K 2 (b x) (b y) = (fromBlocks 0 1 (-1) 0 :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) x y := fun x y => by
    have := congrFun₂ hb x y
    rwa [LinearMap.BilinForm.toMatrix_apply] at this
  have hfix : ∀ i, spMat g *ᵥ b (Sum.inl i) = b (Sum.inl i) := by
    intro i
    have hortho : b (Sum.inl i) ∈ (pairedSympForm K 2).orthogonal (displacement g) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro y hy
      rw [hbW] at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨_, ⟨j, -, rfl⟩, rfl⟩ := hy
        show pairedSympForm K 2 _ _ = 0
        rw [hB]
        simp
      | zero => simp
      | add x y _ _ hx hy =>
        show pairedSympForm K 2 _ _ = 0
        rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
      | smul c y _ hy =>
        show pairedSympForm K 2 _ _ = 0
        rw [map_smul, LinearMap.smul_apply, hy, smul_zero]
    exact sub_eq_zero.mp (displacement_eq_zero_of_mem_orthogonal hg2 hortho)
  set C : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j =>
    b.repr (spMat g *ᵥ b (Sum.inr j) - b (Sum.inr j)) (Sum.inl i) with hCdef
  have hw : ∀ j, spMat g *ᵥ b (Sum.inr j) = b (Sum.inr j) + ∑ i, C i j • b (Sum.inl i) := by
    intro j
    set w := spMat g *ᵥ b (Sum.inr j) - b (Sum.inr j) with hwdef
    have hwW : w ∈ displacement g := mem_displacement.mpr ⟨b (Sum.inr j), rfl⟩
    have hsupp : ∀ k, b.repr w (Sum.inr k) = 0 := by
      intro k
      by_contra hne
      rw [hbW, Basis.mem_span_image] at hwW
      obtain ⟨i, -, hi⟩ := hwW (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hne))
      exact Sum.inl_ne_inr hi
    have hexp : w = ∑ i, C i j • b (Sum.inl i) := by
      have hC' : ∀ i, C i j = b.repr w (Sum.inl i) := fun i => rfl
      simp only [hC']
      conv_lhs => rw [← b.sum_repr w]
      rw [Fintype.sum_sum_type]
      simp [hsupp]
    rw [← hexp, hwdef]
    abel
  have hhx : ∀ x, spMat h *ᵥ Pi.single x 1 = b x := fun x => by simpa using hh x
  have hgh : spMat g * spMat h = spMat h * (fromBlocks 1 C 0 1 :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    refine Matrix.ext_of_mulVec_single fun x => ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec, hhx]
    rcases x with i | j
    · rw [fromBlocks_one_mulVec_single_inl, hhx, hfix]
    · rw [fromBlocks_one_mulVec_single_inr, mulVec_add, hhx, hw, mulVec_sum]
      exact congrArg _ (Finset.sum_congr rfl fun i _ => by rw [mulVec_smul, hhx])
  set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := fromBlocks 1 C 0 1 with hM
  have hN : spMat (h⁻¹ * g * h) = M := by
    have h1 : spMat (h⁻¹ : StatedSp 2 K) * spMat h = 1 := by
      change (((h⁻¹ * h : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1
      rw [inv_mul_cancel]
      rfl
    calc spMat (h⁻¹ * g * h) = spMat h⁻¹ * (spMat g * spMat h) := by
          change spMat h⁻¹ * spMat g * spMat h = _
          rw [Matrix.mul_assoc]
      _ = spMat h⁻¹ * (spMat h * M) := by rw [hgh]
      _ = M := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hsymm : Cᵀ = C := by
    have hmem := mem_statedSp_iff.1 (h⁻¹ * g * h).2
    change (spMat (h⁻¹ * g * h))ᵀ * fromBlocks 0 1 (-1) 0 * spMat (h⁻¹ * g * h) = _ at hmem
    rw [hN, hM, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply] at hmem
    simp at hmem
    exact (neg_add_eq_zero.mp hmem).symm
  have hut : h⁻¹ * g * h = upperUnipotentSp 2 K hsymm :=
    statedSp_ext (by rw [coe_upperUnipotentSp]; exact hN)
  refine ⟨h⁻¹, C, hsymm, ?_, by rw [inv_inv]; exact hut⟩
  intro hC0
  apply hg1
  have h1 : h⁻¹ * g * h = 1 := statedSp_ext (by
    change spMat (h⁻¹ * g * h) = 1
    rw [hN, hM, hC0, fromBlocks_one])
  calc g = h * (h⁻¹ * g * h) * h⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem isUnit_det_or_exists_conj_eq_single [Finite K] {C : Matrix (Fin 2) (Fin 2) K}
    (hC : Cᵀ = C) (hC0 : C ≠ 0) :
    IsUnit C.det ∨ ∃ A : GL (Fin 2) K,
      (A : Matrix (Fin 2) (Fin 2) K) * C * (A : Matrix (Fin 2) (Fin 2) K)ᵀ = single 0 0 1 := by
  by_cases hdet : C.det = 0
  · right
    have h10 : C 1 0 = C 0 1 := by simpa using congrFun₂ hC 0 1
    have hdet' : C 0 0 * C 1 1 = C 0 1 * C 0 1 := by
      rw [det_fin_two, h10] at hdet
      linear_combination hdet
    have hsq : ∀ x : K, ∃ s, x = s * s := fun x =>
      FiniteField.isSquare_of_char_two (ringChar.eq K 2) x
    by_cases ha : C 0 0 = 0
    · have hb : C 0 1 = 0 := by
        rw [ha, zero_mul] at hdet'
        exact mul_self_eq_zero.mp hdet'.symm
      obtain ⟨s, hs⟩ := hsq (C 1 1)
      have hs0 : s ≠ 0 := by
        rintro rfl
        apply hC0
        ext i j
        fin_cases i <;> fin_cases j <;> simp [ha, hb, h10, hs]
      have hCeq : C = !![0, 0; 0, s * s] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [ha, hb, h10, hs]
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, s⁻¹; 1, 0]
        (by simp [det_fin_two, hs0]), ?_⟩
      change !![0, s⁻¹; 1, 0] * C * (!![0, s⁻¹; 1, 0])ᵀ = _
      rw [hCeq]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hs0]
    · obtain ⟨s, hs⟩ := hsq (C 0 0)
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact ha (by simpa using hs)
      have hCeq : C = !![s * s, C 0 1; C 0 1, C 1 1] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h10, hs]
      have hd : C 1 1 * (s * s) = C 0 1 * C 0 1 := by rw [← hs]; linear_combination hdet'
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![s⁻¹, 0; -(C 0 1 * s⁻¹ * s⁻¹), 1] (by simp [det_fin_two, hs0]), ?_⟩
      change !![s⁻¹, 0; -(C 0 1 * s⁻¹ * s⁻¹), 1] * C *
        (!![s⁻¹, 0; -(C 0 1 * s⁻¹ * s⁻¹), 1])ᵀ = _
      rw [hCeq]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hs0] <;> field_simp
      all_goals first | ring1 | linear_combination hd
  · exact Or.inl (isUnit_iff_ne_zero.mpr hdet)

end CFSG.Quasithin.F7Two
