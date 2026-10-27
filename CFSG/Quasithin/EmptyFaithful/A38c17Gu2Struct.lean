module

public import CFSG.Quasithin.EmptyFaithful.A38c17Gu2Hyp
public import CFSG.Quasithin.EmptyFaithful.A38c17Gu2Norm
public import CFSG.Adapters.SpecialLinearPerfect

public section

namespace CFSG.Quasithin.A38c17

open Matrix CFSG.LieType.Steinberg CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] [CharP K p]

theorem GU_two_entries {F : Type} [Field F] {σ : F ≃+* F} {m : Matrix (Fin 2) (Fin 2) F}
    (h : conjTr σ m * antidiag 2 * m = antidiag 2) :
    m.det * σ (m 0 0) = m 0 0 ∧ m.det * σ (m 1 1) = m 1 1 ∧
      m.det * σ (m 0 1) = -m 0 1 ∧ m.det * σ (m 1 0) = -m 1 0 := by
  rw [antidiag_two] at h
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [Matrix.det_fin_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination m 0 0 * e01 - m 0 1 * e00
  · linear_combination m 1 1 * e10 - m 1 0 * e11
  · linear_combination m 0 0 * e11 - m 0 1 * e10
  · linear_combination m 1 1 * e00 - m 1 0 * e01

theorem GU_two_norm_det {F : Type} [Field F] {σ : F ≃+* F} {m : Matrix (Fin 2) (Fin 2) F}
    (h : conjTr σ m * antidiag 2 * m = antidiag 2) : σ m.det * m.det = 1 := by
  have hdet := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have h1 : (conjTr σ m).det = σ m.det := by
    rw [conjTr, Matrix.det_transpose]
    exact (RingHom.map_det σ.toRingHom m).symm
  rw [h1] at hdet
  have hJ := det_antidiag_ne_zero (F := F) 2
  refine mul_right_cancel₀ hJ ?_
  rw [one_mul]
  linear_combination hdet

theorem exists_hypMat_eq_smul {ζ l : K} (hζ0 : ζ ≠ 0) (hζ : unitaryInvolution K p 1 ζ = -ζ)
    {m : Matrix (Fin 2) (Fin 2) K}
    (h00 : unitaryInvolution K p 1 (l * m 0 0) = l * m 0 0)
    (h11 : unitaryInvolution K p 1 (l * m 1 1) = l * m 1 1)
    (h01 : unitaryInvolution K p 1 (l * m 0 1) = -(l * m 0 1))
    (h10 : unitaryInvolution K p 1 (l * m 1 0) = -(l * m 1 0)) :
    ∃ B : Matrix (Fin 2) (Fin 2) (fixedSubfield K p 1), hypMat ζ B = l • m := by
  have hb : l * m 0 1 / ζ ∈ fixedSubfield K p 1 := by
    rw [mem_fixedSubfield, map_div₀, h01, hζ, neg_div_neg_eq]
  have hc : l * m 1 0 * ζ ∈ fixedSubfield K p 1 := by
    rw [mem_fixedSubfield, map_mul, h10, hζ, neg_mul_neg]
  refine ⟨!![⟨l * m 0 0, h00⟩, ⟨l * m 0 1 / ζ, hb⟩; ⟨l * m 1 0 * ζ, hc⟩, ⟨l * m 1 1, h11⟩], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hypMat] <;> field_simp

theorem GU_two_le_range_sup_center {ζ : K} (hζ0 : ζ ≠ 0) (hζ : unitaryInvolution K p 1 ζ = -ζ)
    (hK : Nat.card K = p ^ 2) :
    GU (unitaryInvolution K p 1) 2 ≤ (hypEmbedGL hζ0).range ⊔ Subgroup.center (GL (Fin 2) K) := by
  intro g hg
  set m : Matrix (Fin 2) (Fin 2) K := (g : Matrix (Fin 2) (Fin 2) K) with hm
  have hg' : conjTr (unitaryInvolution K p 1) m * antidiag 2 * m = antidiag 2 := mem_GU.1 hg
  obtain ⟨e00, e11, e01, e10⟩ := GU_two_entries hg'
  have hnorm := GU_two_norm_det hg'
  have hΔ0 : m.det ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hnorm
    exact zero_ne_one hnorm
  obtain ⟨l, hl0, hl⟩ := exists_eq_mul_of_norm_eq_one hK hnorm
  obtain ⟨B, hB⟩ := exists_hypMat_eq_smul (l := l) (m := m) hζ0 hζ
    (by rw [map_mul, hl]; linear_combination l * e00)
    (by rw [map_mul, hl]; linear_combination l * e11)
    (by rw [map_mul, hl]; linear_combination l * e01)
    (by rw [map_mul, hl]; linear_combination l * e10)
  have hdetB : ((B.det : fixedSubfield K p 1) : K) = l ^ 2 * m.det := by
    rw [← det_hypMat hζ0 B, hB, Matrix.det_smul, Fintype.card_fin]
  have hB0 : B.det ≠ 0 := by
    intro h0
    rw [h0] at hdetB
    exact mul_ne_zero (pow_ne_zero 2 hl0) hΔ0 (by simpa using hdetB.symm)
  let B' : GL (Fin 2) (fixedSubfield K p 1) := GeneralLinearGroup.mkOfDetNeZero B hB0
  have hB' : ((hypEmbedGL hζ0 B' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = l • m := hB
  have hgeq : g = GeneralLinearGroup.scalar (Fin 2) (Units.mk0 l⁻¹ (inv_ne_zero hl0)) *
      hypEmbedGL hζ0 B' := by
    apply Units.ext
    rw [Units.val_mul, hB', GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  have hcen : GeneralLinearGroup.scalar (Fin 2) (Units.mk0 l⁻¹ (inv_ne_zero hl0)) ∈
      Subgroup.center (GL (Fin 2) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  rw [hgeq, sup_comm]
  exact Subgroup.mul_mem_sup hcen ⟨B', rfl⟩

theorem hypEmbedGL_range_le_GU_sup_center {ζ : K} (hζ0 : ζ ≠ 0)
    (hζ : unitaryInvolution K p 1 ζ = -ζ) (hK : Nat.card K = p ^ 2) :
    (hypEmbedGL hζ0).range ≤ GU (unitaryInvolution K p 1) 2 ⊔ Subgroup.center (GL (Fin 2) K) := by
  rintro _ ⟨B, rfl⟩
  have hBdet : (B : Matrix (Fin 2) (Fin 2) (fixedSubfield K p 1)).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det (B : Matrix (Fin 2) (Fin 2) (fixedSubfield K p 1))).1
      B.isUnit
    exact this.ne_zero
  obtain ⟨y, hy⟩ := exists_norm_eq_fixedSubfield hK
    (((B : Matrix (Fin 2) (Fin 2) (fixedSubfield K p 1)).det)⁻¹)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hy
    exact (inv_ne_zero hBdet) (Subtype.ext hy.symm)
  have hμ : unitaryInvolution K p 1 (Units.mk0 y hy0 : K) * (Units.mk0 y hy0 : K) *
      (((B : Matrix (Fin 2) (Fin 2) (fixedSubfield K p 1)).det : fixedSubfield K p 1) : K) = 1 := by
    rw [Units.val_mk0, hy, ← Subfield.coe_mul, inv_mul_cancel₀ hBdet, Subfield.coe_one]
  have hmem := scalar_mul_hypEmbedGL_mem_GU hζ0 hζ B (Units.mk0 y hy0) hμ
  have hcen : (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 y hy0))⁻¹ ∈
      Subgroup.center (GL (Fin 2) K) := by
    refine Subgroup.inv_mem _ ?_
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  have : hypEmbedGL hζ0 B = (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 y hy0))⁻¹ *
      (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 y hy0) * hypEmbedGL hζ0 B) := by
    rw [inv_mul_cancel_left]
  rw [this, sup_comm]
  exact Subgroup.mul_mem_sup hcen hmem

theorem SU_two_commutator_eq {ζ : K} (hζ0 : ζ ≠ 0) (hζ : unitaryInvolution K p 1 ζ = -ζ)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hK : Nat.card K = p ^ 2) :
    ⁅SU (unitaryInvolution K p 1) 2, SU (unitaryInvolution K p 1) 2⁆ =
      SU (unitaryInvolution K p 1) 2 := by
  have hK' : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one]; exact hK
  have hF : Nat.card (fixedSubfield K p 1) = p := by
    simpa using card_fixedSubfield hK'
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield K p 1)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _ (by
      have := (Fact.out : p.Prime).two_le
      rw [hF]
      omega)
  have : Group.IsPerfect ↥(SU (unitaryInvolution K p 1) 2) :=
    Group.IsPerfect.ofSurjective (f := (hypEquiv hζ0 hζ).toMonoidHom) (hypEquiv hζ0 hζ).surjective
  exact Subgroup.isPerfect_iff.mp this

theorem commutator_le_SU {H : Subgroup (GL (Fin 2) K)}
    (hH : H ≤ GU (unitaryInvolution K p 1) 2) :
    ⁅H, H⁆ ≤ SU (unitaryInvolution K p 1) 2 := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  rw [mem_SU_iff_mem_GU_and_det]
  refine ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (hH hg) (hH hh)) (inv_mem (hH hg))) (inv_mem (hH hh))
  · have h1 : Matrix.GeneralLinearGroup.det ⁅g, h⁆ = (1 : Kˣ) := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
    exact congrArg (fun x : Kˣ => (x : K)) h1

end CFSG.Quasithin.A38c17
