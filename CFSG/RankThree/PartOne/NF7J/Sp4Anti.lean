module

public import CFSG.RankThree.PartOne.NF7J.Sp4Oct

public section

namespace CFSG.RankThree.PartOne.NF7J

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.N143 CFSG.RankThree.PartOne.HESS

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem antidiag_of_inv {ζ : Kˣ} (hζ2 : ζ ^ 2 ≠ 1) {X : Matrix.SpecialLinearGroup (Fin 2) K}
    (h : X * hmat ζ = (hmat ζ)⁻¹ * X) : e2 X 0 0 = 0 ∧ e2 X 1 1 = 0 := by
  have hz : (ζ : K) ≠ 0 := ζ.ne_zero
  have hne : (ζ : K) - (ζ : K)⁻¹ ≠ 0 := by
    intro h0
    apply hζ2
    have : (ζ : K) ^ 2 = 1 := by
      field_simp at h0
      linear_combination h0
    exact Units.ext (by simpa using this)
  have h00 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) K => e2 M 0 0) h
  have h11 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) K => e2 M 1 1) h
  simp only [e2_mul, e2_inv_00, e2_inv_01, e2_inv_10, e2_inv_11, e2_hmat_00, e2_hmat_01, e2_hmat_10,
    e2_hmat_11, mul_zero, add_zero, neg_zero, zero_mul] at h00 h11
  constructor
  · have : e2 X 0 0 * ((ζ : K) - (ζ : K)⁻¹) = 0 := by linear_combination h00
    rcases mul_eq_zero.1 this with h' | h'
    · exact h'
    · exact absurd h' hne
  · have : e2 X 1 1 * ((ζ : K) - (ζ : K)⁻¹) = 0 := by linear_combination -h11
    rcases mul_eq_zero.1 this with h' | h'
    · exact h'
    · exact absurd h' hne

omit [Finite K] in
theorem anti_unit {X : Matrix.SpecialLinearGroup (Fin 2) K} (h00 : e2 X 0 0 = 0) (h11 : e2 X 1 1 = 0) :
    e2 X 0 1 ≠ 0 ∧ e2 X 1 0 = (e2 X 0 1)⁻¹ := by
  have hdet := e2_det X
  rw [h00, h11] at hdet
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hprod : e2 X 0 1 * e2 X 1 0 = 1 := by linear_combination -hdet - h2
  have hne : e2 X 0 1 ≠ 0 := fun h0 => by rw [h0, zero_mul] at hprod; exact zero_ne_one hprod
  exact ⟨hne, by field_simp; linear_combination hprod⟩

omit [Finite K] in
theorem spBlock_anti {X : Matrix.SpecialLinearGroup (Fin 2) K} (h00 : e2 X 0 0 = 0)
    (h11 : e2 X 1 1 = 0) : ∃ u : Kˣ, spBlock X = spDiag K (u, 1) * wEl 1 := by
  obtain ⟨hne, hX10⟩ := anti_unit h00 h11
  refine ⟨Units.mk0 _ hne, ?_⟩
  apply Subtype.ext
  apply Units.ext
  simp only [coe_spBlock, Subgroup.coe_mul, Units.val_mul, coe_spDiag, diagU_val, coe_wEl]
  ext i j
  have e00 : ((X : Matrix (Fin 2) (Fin 2) K)) 0 0 = 0 := h00
  have e11 : ((X : Matrix (Fin 2) (Fin 2) K)) 1 1 = 0 := h11
  have e10 : ((X : Matrix (Fin 2) (Fin 2) K)) 1 0 = (((X : Matrix (Fin 2) (Fin 2) K)) 0 1)⁻¹ := hX10
  fin_cases i <;> fin_cases j <;>
    simp [blk22, Pm, dvec4, f2, Matrix.mul_apply, Matrix.diagonal_apply, e00, e11, e10]

omit [Finite K] in
theorem spBlock'_anti {X : Matrix.SpecialLinearGroup (Fin 2) K} (h00 : e2 X 0 0 = 0)
    (h11 : e2 X 1 1 = 0) : ∃ u : Kˣ, spBlock' X = spDiag K (u, u⁻¹) * wEl 0 := by
  obtain ⟨hne, hX10⟩ := anti_unit h00 h11
  refine ⟨Units.mk0 _ hne, ?_⟩
  apply Subtype.ext
  apply Units.ext
  simp only [coe_spBlock', Subgroup.coe_mul, Units.val_mul, coe_spDiag, diagU_val, coe_wEl]
  ext i j
  have e00 : ((X : Matrix (Fin 2) (Fin 2) K)) 0 0 = 0 := h00
  have e11 : ((X : Matrix (Fin 2) (Fin 2) K)) 1 1 = 0 := h11
  have e10 : ((X : Matrix (Fin 2) (Fin 2) K)) 1 0 = (((X : Matrix (Fin 2) (Fin 2) K)) 0 1)⁻¹ := hX10
  fin_cases i <;> fin_cases j <;>
    simp [blk4, Pm, dvec4, f2, Matrix.mul_apply, Matrix.diagonal_apply, e00, e11, e10]

omit [Finite K] in
theorem conj_spDiag_wEl_octEl (i : Fin 2) (a b : Kˣ) (j : Fin 8) (s : K) :
    ∃ s' : K, (spDiag K (a, b) * wEl i) * octEl j s * (spDiag K (a, b) * wEl i)⁻¹ =
      octEl (wperm i j) s' := by
  refine ⟨(octChar (wperm i j) a b : K) * s, ?_⟩
  rw [_root_.mul_inv_rev]
  calc spDiag K (a, b) * wEl i * octEl j s * ((wEl i)⁻¹ * (spDiag K (a, b))⁻¹)
      = spDiag K (a, b) * (wEl i * octEl j s * (wEl i)⁻¹) * (spDiag K (a, b))⁻¹ := by group
    _ = octEl (wperm i j) ((octChar (wperm i j) a b : K) * s) := by
      rw [wEl_conj_octEl, spDiag_conj_octEl]

theorem conj_octSub_eq (t : ↥(spRev K)) {σ : Fin 8 → Fin 8} {j : Fin 8}
    (h : ∀ s : K, ∃ s' : K, t * octEl j s * t⁻¹ = octEl (σ j) s') :
    (octSub K j).map (MulAut.conj t).toMonoidHom = octSub K (σ j) := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨s, rfl⟩ := mem_octSub_iff.1 hg
    obtain ⟨s', hs'⟩ := h s
    show t * octEl j s * t⁻¹ ∈ _
    rw [hs']
    exact octEl_mem _ _
  · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective, octSub_card, octSub_card]

end CFSG.RankThree.PartOne.NF7J
