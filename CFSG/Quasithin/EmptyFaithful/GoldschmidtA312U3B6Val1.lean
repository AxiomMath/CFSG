module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3B6Aux
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.SubgroupLists2.SpectralBounds

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.RankThree.SubgroupLists
open scoped MatrixGroups

section Elements

variable {F : Type} [Field F]

@[expose] def xSL2 (l : F) : SL(2, F) := ⟨!![0, -1; 1, l], by simp [Matrix.det_fin_two]⟩

@[expose] noncomputable def xPSL2 (l : F) : ProjectiveSpecialLinearGroup (Fin 2) F :=
  QuotientGroup.mk' (Subgroup.center SL(2, F)) (xSL2 l)

@[expose] def wSL2 (i : F) (hi : i * i = -1) : SL(2, F) :=
  ⟨!![0, i; i, 0], by simp [Matrix.det_fin_two, hi]⟩

theorem xSL2_pow_five {l : F} (hl : l ^ 2 + l - 1 = 0) : xSL2 l ^ 5 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow]
  change (!![0, -1; 1, l] : Matrix (Fin 2) (Fin 2) F) ^ 5 = 1
  simp only [pow_succ, pow_zero, one_mul, Matrix.mul_fin_two, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination (1 - l) * hl
  · linear_combination (-(l ^ 2 - l - 1)) * hl
  · linear_combination (l ^ 2 - l - 1) * hl
  · linear_combination (l ^ 3 - l ^ 2 - 2 * l + 1) * hl

theorem xSL2_not_mem_center (l : F) : xSL2 l ∉ Subgroup.center SL(2, F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  rintro ⟨r, -, hr⟩
  have h := congrFun (congrFun hr 0) 1
  simp [xSL2] at h

theorem xPSL2_pow_five {l : F} (hl : l ^ 2 + l - 1 = 0) : xPSL2 l ^ 5 = 1 := by
  rw [xPSL2, ← map_pow, xSL2_pow_five hl, map_one]

theorem xPSL2_ne_one (l : F) : xPSL2 l ≠ 1 := by
  intro h
  exact xSL2_not_mem_center l ((QuotientGroup.eq_one_iff _).mp h)

theorem wSL2_mul_xSL2 (i l : F) (hi : i * i = -1) :
    wSL2 i hi * xSL2 l = (xSL2 l)⁻¹ * wSL2 i hi := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  change (!![0, i; i, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, -1; 1, l] =
    Matrix.adjugate (!![0, -1; 1, l]) * !![0, i; i, 0]
  rw [Matrix.adjugate_fin_two]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem xPSL2_conj (i l : F) (hi : i * i = -1) :
    QuotientGroup.mk' (Subgroup.center SL(2, F)) (wSL2 i hi) * xPSL2 l *
        (QuotientGroup.mk' (Subgroup.center SL(2, F)) (wSL2 i hi))⁻¹ = (xPSL2 l)⁻¹ := by
  have h : QuotientGroup.mk' (Subgroup.center SL(2, F))
      (wSL2 i hi * xSL2 l * (wSL2 i hi)⁻¹) =
        QuotientGroup.mk' (Subgroup.center SL(2, F)) (xSL2 l)⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul.mpr (wSL2_mul_xSL2 i l hi)]
  simpa [map_mul, map_inv, xPSL2] using h

end Elements

section Field

variable {F : Type} [Field F] [Finite F]

theorem charP_three_of_card_nine (hF : Nat.card F = 9) : CharP F 3 :=
  CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow (n := 2) Nat.prime_three
    (by rw [hF]; norm_num)

theorem exists_sq_neg_one_card_nine (hF : Nat.card F = 9) : ∃ i : F, i * i = -1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 9 := by rw [← Nat.card_eq_fintype_card, hF]
  have := charP_three_of_card_nine hF
  have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F 3]; norm_num
  have h1 : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  obtain ⟨i, hi⟩ := (FiniteField.isSquare_iff hchar h1).mpr (by rw [hcard]; norm_num)
  exact ⟨i, hi.symm⟩

theorem sq_add_sub_one_eq_zero (hF : Nat.card F = 9) {i : F} (hi : i * i = -1) :
    (1 - i) ^ 2 + (1 - i) - 1 = 0 := by
  have h3 : (3 : F) = 0 := by exact_mod_cast (charP_three_of_card_nine hF).cast_eq_zero
  linear_combination hi - i * h3

theorem aut_apply_of_ne_one (hF : Nat.card F = 9) {l : F} (hl : l ^ 2 + l - 1 = 0)
    {σ : F ≃+* F} (hσ : σ ≠ 1) : σ l = -l - 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := charP_three_of_card_nine hF
  have h3 : (3 : F) = 0 := by exact_mod_cast (charP_three_of_card_nine hF).cast_eq_zero
  have hl3 : l ^ 3 = -l - 1 := by linear_combination (l - 1) * hl + l * h3
  have hne : -l - 1 ≠ l := by
    intro h
    have hl1 : l = 1 := by linear_combination h + l * h3
    have h01 : (1 : F) = 0 := by rw [hl1] at hl; linear_combination hl
    exact one_ne_zero h01
  have hcard : Nat.card (F ≃+* F) = 2 := card_ringEquiv_eq Nat.prime_three
    (by rw [hF]; norm_num)
  have : Finite (F ≃+* F) := Finite.of_injective (fun e : F ≃+* F => (e : F → F)) (by
    intro e f h
    ext x
    exact congrFun h x)
  have h1 : frobeniusEquiv F 3 l = -l - 1 := by rw [frobeniusEquiv_def, hl3]
  have hφ : frobeniusEquiv F 3 ≠ 1 := by
    intro h
    have h2 : frobeniusEquiv F 3 l = l := by rw [h]; rfl
    exact hne (h1 ▸ h2)
  rw [eq_of_ne_one_of_card_le_two' hcard.le hσ hφ]
  exact h1

theorem aut_sq_ne (hF : Nat.card F = 9) {l : F} (hl : l ^ 2 + l - 1 = 0) {σ : F ≃+* F}
    (hσ : σ ≠ 1) : (σ l) ^ 2 ≠ l ^ 2 := by
  rw [aut_apply_of_ne_one hF hl hσ]
  intro h
  have h3 : (3 : F) = 0 := by exact_mod_cast (charP_three_of_card_nine hF).cast_eq_zero
  have hl1 : l = 1 := by linear_combination (-1) * h + l * h3
  have h01 : (1 : F) = 0 := by rw [hl1] at hl; linear_combination hl
  exact one_ne_zero h01

end Field

end CFSG.Quasithin.A312U3
