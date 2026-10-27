module

public import CFSG.RankThree.SubgroupLists.ThreeSquareExclusion
public import CFSG.RankThree.SubgroupLists.LinearThreeFamily
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFour

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups

theorem false_of_mulEquiv_three_square {K : Type*} [Field K] [Finite K] (h3 : (3 : K) ≠ 0)
    {H : Subgroup (GL (Fin 3) K)} (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1) {S : Type*} [Group S]
    (e : (H ⧸ Subgroup.center H) ≃* S) {e₁ e₂ g h : S} (he₁ : e₁ ^ 3 = 1) (he₂ : e₂ ^ 3 = 1)
    (he₁₂ : e₁ * e₂ = e₂ * e₁) (he₁1 : e₁ ≠ 1) (hg₁ : g * e₁ * g⁻¹ = e₁)
    (hg₂ : g * e₂ * g⁻¹ = e₂⁻¹) (hh₁ : h * e₁ * h⁻¹ = e₁) (hh₂ : h * e₂ * h⁻¹ = e₂ * e₁) :
    False :=
  false_of_three_square h3 hdet hZ3 (e₁ := e.symm e₁) (e₂ := e.symm e₂) (g := e.symm g)
    (h := e.symm h) (by rw [← map_pow, he₁, map_one]) (by rw [← map_pow, he₂, map_one])
    (by rw [← map_mul, ← map_mul, he₁₂]) (fun h1 => he₁1 (e.symm.injective (by rw [h1, map_one])))
    (by rw [← map_inv, ← map_mul, ← map_mul, hg₁])
    (by rw [← map_inv, ← map_mul, ← map_mul, hg₂, map_inv])
    (by rw [← map_inv, ← map_mul, ← map_mul, hh₁])
    (by rw [← map_inv, ← map_mul, ← map_mul, hh₂, map_mul])

section Linear

variable {F : Type} [Field F]

@[expose] def transvection23 (F : Type) [Field F] : SL(3, F) :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def transvection23Inv (F : Type) [Field F] : SL(3, F) :=
  ⟨!![1, 0, 0; 0, 1, -1; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def transvection12 (F : Type) [Field F] : SL(3, F) :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def negOuterSL3 (F : Type) [Field F] : SL(3, F) :=
  ⟨diagonal ![-1, 1, -1], by simp [det_diagonal, Fin.prod_univ_three]⟩

theorem transvection13_pow_three (h3 : (3 : F) = 0) : transvection13 F ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  change (!![1, 0, 1; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  linear_combination h3

theorem transvection23_pow_three (h3 : (3 : F) = 0) : transvection23 F ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  change (!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  linear_combination h3

theorem transvection13_mul_transvection23 :
    transvection13 F * transvection23 F = transvection23 F * transvection13 F := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change (!![1, 0, 1; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) *
      !![1, 0, 0; 0, 1, 1; 0, 0, 1] =
    !![1, 0, 0; 0, 1, 1; 0, 0, 1] * !![1, 0, 1; 0, 1, 0; 0, 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem negOuterSL3_mul_transvection13 :
    negOuterSL3 F * transvection13 F = transvection13 F * negOuterSL3 F := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change diagonal ![-1, 1, -1] * (!![1, 0, 1; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) =
    !![1, 0, 1; 0, 1, 0; 0, 0, 1] * diagonal ![-1, 1, -1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, diagonal]

theorem negOuterSL3_mul_transvection23 :
    negOuterSL3 F * transvection23 F = transvection23Inv F * negOuterSL3 F := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change diagonal ![-1, 1, -1] * (!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) =
    !![1, 0, 0; 0, 1, -1; 0, 0, 1] * diagonal ![-1, 1, -1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, diagonal]

theorem transvection23_mul_transvection23Inv :
    transvection23 F * transvection23Inv F = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  change (!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) *
    !![1, 0, 0; 0, 1, -1; 0, 0, 1] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem transvection12_mul_transvection13 :
    transvection12 F * transvection13 F = transvection13 F * transvection12 F := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change (!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) *
      !![1, 0, 1; 0, 1, 0; 0, 0, 1] =
    !![1, 0, 1; 0, 1, 0; 0, 0, 1] * !![1, 1, 0; 0, 1, 0; 0, 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem transvection12_mul_transvection23 :
    transvection12 F * transvection23 F =
      transvection23 F * transvection13 F * transvection12 F := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]
  change (!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) *
      !![1, 0, 0; 0, 1, 1; 0, 0, 1] =
    !![1, 0, 0; 0, 1, 1; 0, 0, 1] * !![1, 0, 1; 0, 1, 0; 0, 0, 1] *
      !![1, 1, 0; 0, 1, 0; 0, 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem exists_three_square_psl33 (h3 : (3 : F) = 0) :
    ∃ e₁ e₂ g h : ProjectiveSpecialLinearGroup (Fin 3) F, e₁ ^ 3 = 1 ∧ e₂ ^ 3 = 1 ∧
      e₁ * e₂ = e₂ * e₁ ∧ e₁ ≠ 1 ∧ g * e₁ * g⁻¹ = e₁ ∧ g * e₂ * g⁻¹ = e₂⁻¹ ∧
      h * e₁ * h⁻¹ = e₁ ∧ h * e₂ * h⁻¹ = e₂ * e₁ := by
  set π := QuotientGroup.mk' (Subgroup.center SL(3, F))
  have hinv : (transvection23 F)⁻¹ = transvection23Inv F :=
    inv_eq_of_mul_eq_one_right transvection23_mul_transvection23Inv
  refine ⟨π (transvection13 F), π (transvection23 F), π (negOuterSL3 F), π (transvection12 F),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, transvection13_pow_three h3, map_one]
  · rw [← map_pow, transvection23_pow_three h3, map_one]
  · rw [← map_mul, ← map_mul, transvection13_mul_transvection23]
  · intro h
    exact transvection13_not_mem_center (F := F) (by simpa [π, QuotientGroup.eq_one_iff] using h)
  · rw [← map_inv, ← map_mul, ← map_mul, negOuterSL3_mul_transvection13, mul_inv_cancel_right]
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, negOuterSL3_mul_transvection23,
      mul_inv_cancel_right, hinv]
  · rw [← map_inv, ← map_mul, ← map_mul, transvection12_mul_transvection13,
      mul_inv_cancel_right]
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, transvection12_mul_transvection23,
      mul_inv_cancel_right]

end Linear

theorem false_of_psl33 {K : Type*} [Field K] [Finite K] (h3 : (3 : K) ≠ 0)
    {H : Subgroup (GL (Fin 3) K)} (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1) {F : Type} [Field F] (hF3 : (3 : F) = 0)
    (e : (H ⧸ Subgroup.center H) ≃* ProjectiveSpecialLinearGroup (Fin 3) F) : False := by
  obtain ⟨e₁, e₂, g, h, he₁, he₂, he₁₂, he₁1, hg₁, hg₂, hh₁, hh₂⟩ :=
    exists_three_square_psl33 hF3
  exact false_of_mulEquiv_three_square h3 hdet hZ3 e he₁ he₂ he₁₂ he₁1 hg₁ hg₂ hh₁ hh₂

section Unitary

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] noncomputable def negOuterGL3 (K : Type) [Field K] : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mk'' (diagonal ![-1, 1, -1])
    (by simp [det_diagonal, Fin.prod_univ_three])

theorem coe_negOuterGL3 :
    ((negOuterGL3 K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![-1, 1, -1] :=
  rfl

theorem negOuterGL3_mem_SU : negOuterGL3 K ∈ SU σ 3 := by
  refine ⟨by simp [coe_negOuterGL3, det_diagonal, Fin.prod_univ_three], ?_⟩
  rw [coe_negOuterGL3, antidiag_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTr, Matrix.mul_apply, Fin.sum_univ_three, diagonal]

theorem negOuterGL3_mul_unipGL (a c : K) :
    negOuterGL3 K * unipGL σ a c = unipGL σ (-a) c * negOuterGL3 K := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_negOuterGL3, coe_unipGL, coe_unipGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipMat, Matrix.mul_apply, diagonal]

theorem unipGL_pow_three (h3 : (3 : K) = 0) (a c : K) : unipGL σ a c ^ 3 = 1 := by
  rw [pow_three, unipGL_mul, unipGL_mul, ← unipGL_zero_zero σ]
  exact unipGL_congr σ (by linear_combination a * h3)
    (by rw [map_add]; linear_combination (c - a * σ a) * h3)

end Unitary

theorem exists_three_square_psu33 {K : Type} [Field K] [Finite K] [CharP K 3]
    (hK : Nat.card K = (3 ^ 1) ^ 2) :
    ∃ e₁ e₂ g h : StatedProj (StatedSU 3 (3 ^ 1) K), e₁ ^ 3 = 1 ∧ e₂ ^ 3 = 1 ∧
      e₁ * e₂ = e₂ * e₁ ∧ e₁ ≠ 1 ∧ g * e₁ * g⁻¹ = e₁ ∧ g * e₂ * g⁻¹ = e₂⁻¹ ∧
      h * e₁ * h⁻¹ = e₁ ∧ h * e₂ * h⁻¹ = e₂ * e₁ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set σ := unitaryInvolution K 3 1 with hσdef
  have hσ : ∀ x, σ (σ x) = x := unitaryInvolution_involutive hK
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  obtain ⟨b, hb⟩ : ∃ b : K, σ b ≠ b := by
    by_contra hno
    push Not at hno
    have hcard := CFSG.LieType.Steinberg.card_fixedSubfield (F := K) (p := 3) (f := 1) hK
    have hall : ∀ w : K, w ∈ CFSG.LieType.Steinberg.fixedSubfield K 3 1 := fun w => hno w
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), hK] at hcard
    norm_num at hcard
  obtain ⟨d, hd⟩ := exists_add_unitaryInvolution_eq (K := K) (p := 3) (f := 1) hK
    (a := -(b * σ b)) (by rw [map_neg, map_mul, hσ, mul_comm])
  set c₀ := σ b - b with hc₀
  have hc₀0 : c₀ ≠ 0 := sub_ne_zero.mpr hb
  have hz : c₀ + σ c₀ + 0 * σ 0 = 0 := by
    rw [hc₀, map_sub, hσ, zero_mul, add_zero]
    ring
  have hu : (1 : K) + σ 1 + 1 * σ 1 = 0 := by
    rw [map_one]
    linear_combination h3
  have hui : (1 : K) + σ 1 + (-1) * σ (-1) = 0 := by
    rw [map_neg, map_one]
    linear_combination h3
  have hh : d + σ d + b * σ b = 0 := by
    rw [hd]
    ring
  set e := equivStatedSU (p := 3) (f := 1) hK 3
  set π := QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (3 ^ 1) K))
  let E1 : SU σ 3 := ⟨unipGL σ 0 c₀, unipGL_mem_SU σ hσ hz⟩
  let E2 : SU σ 3 := ⟨unipGL σ 1 1, unipGL_mem_SU σ hσ hu⟩
  let E2i : SU σ 3 := ⟨unipGL σ (-1) 1, unipGL_mem_SU σ hσ hui⟩
  let D : SU σ 3 := ⟨negOuterGL3 K, negOuterGL3_mem_SU σ⟩
  let Hh : SU σ 3 := ⟨unipGL σ b d, unipGL_mem_SU σ hσ hh⟩
  set Φ : SU σ 3 →* StatedProj (StatedSU 3 (3 ^ 1) K) := π.comp e.toMonoidHom with hΦ
  have hΦe : ∀ M, π (e M) = Φ M := fun M => rfl
  have hval : ∀ M N : SU σ 3, (M : GL (Fin 3) K) = N → M = N := fun M N h => Subtype.ext h
  have cE1 : (E1 : GL (Fin 3) K) = unipGL σ 0 c₀ := rfl
  have cE2 : (E2 : GL (Fin 3) K) = unipGL σ 1 1 := rfl
  have cE2i : (E2i : GL (Fin 3) K) = unipGL σ (-1) 1 := rfl
  have cD : (D : GL (Fin 3) K) = negOuterGL3 K := rfl
  have cHh : (Hh : GL (Fin 3) K) = unipGL σ b d := rfl
  have hpow3 : ∀ M : SU σ 3, (∃ a c : K, (M : GL (Fin 3) K) = unipGL σ a c) → M ^ 3 = 1 := by
    rintro M ⟨a, c, hM⟩
    apply hval
    rw [Subgroup.coe_pow, hM, unipGL_pow_three σ h3, Subgroup.coe_one]
  have hnsc : Φ E1 ≠ 1 := by
    intro h
    rw [← hΦe, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    obtain ⟨μ, hμ⟩ := h
    have hcube : ((e E1 : StatedSU 3 (3 ^ 1) K) : GL (Fin 3) K) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← map_pow, hpow3 E1 ⟨0, c₀, cE1⟩, map_one, Subgroup.coe_one]
    rw [← hμ, ← map_pow] at hcube
    have h00 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hcube
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val, Units.val_one,
      Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h00
    have hμ1 : μ = 1 := by
      have hcu : ((μ : K) - 1) ^ 3 = 0 := by
        linear_combination h00 + (1 - (μ : K)) * (μ : K) * h3
      have hμ0 : (μ : K) - 1 = 0 := (pow_eq_zero_iff (n := 3) (by norm_num)).mp hcu
      exact Units.ext (by rw [Units.val_one]; linear_combination hμ0)
    rw [hμ1, map_one] at hμ
    have hM1 : E1 = 1 := e.injective (by rw [map_one]; exact Subtype.ext hμ.symm)
    have h02 := congrArg (fun g : SU σ 3 => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2)
      hM1
    simp only [cE1, coe_unipGL, unipMat, Subgroup.coe_one, Units.val_one] at h02
    simp at h02
    exact hc₀0 h02
  have hcomm : ∀ M N P : SU σ 3, M * N = P * M → Φ M * Φ N * (Φ M)⁻¹ = Φ P := by
    intro M N P h
    rw [← map_inv, ← map_mul, ← map_mul, h, mul_inv_cancel_right]
  refine ⟨Φ E1, Φ E2, Φ D, Φ Hh, ?_, ?_, ?_, hnsc, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hpow3 E1 ⟨0, c₀, cE1⟩, map_one]
  · rw [← map_pow, hpow3 E2 ⟨1, 1, cE2⟩, map_one]
  · rw [← map_mul, ← map_mul]
    congr 1
    apply hval
    rw [Subgroup.coe_mul, Subgroup.coe_mul, cE1, cE2, unipGL_mul, unipGL_mul]
    exact unipGL_congr σ (by ring) (by rw [map_zero, map_one]; ring)
  · apply hcomm
    apply hval
    rw [Subgroup.coe_mul, Subgroup.coe_mul, cD, cE1, negOuterGL3_mul_unipGL, neg_zero]
  · have hE2i : E2⁻¹ = E2i := by
      apply inv_eq_of_mul_eq_one_right
      apply hval
      rw [Subgroup.coe_mul, cE2, cE2i, unipGL_mul, Subgroup.coe_one, ← unipGL_zero_zero σ]
      exact unipGL_congr σ (by ring)
        (by rw [map_neg, map_one]; linear_combination h3)
    rw [show (Φ E2)⁻¹ = Φ E2i by rw [← map_inv, hE2i]]
    apply hcomm
    apply hval
    rw [Subgroup.coe_mul, Subgroup.coe_mul, cD, cE2, cE2i, negOuterGL3_mul_unipGL]
  · apply hcomm
    apply hval
    rw [Subgroup.coe_mul, Subgroup.coe_mul, cHh, cE1, unipGL_mul, unipGL_mul]
    exact unipGL_congr σ (by ring) (by rw [map_zero]; ring)
  · rw [show Φ E2 * Φ E1 = Φ (E2 * E1) from (map_mul Φ E2 E1).symm]
    apply hcomm
    apply hval
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, cHh, cE1, cE2, unipGL_mul,
      unipGL_mul, unipGL_mul]
    exact unipGL_congr σ (by ring) (by rw [map_zero, map_one, hc₀]; ring)

theorem false_of_psu33 {K : Type*} [Field K] [Finite K] (h3 : (3 : K) ≠ 0)
    {H : Subgroup (GL (Fin 3) K)} (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1) {K' : Type} [Field K'] [Finite K']
    (hK' : Nat.card K' = (3 ^ 1) ^ 2)
    (e : (H ⧸ Subgroup.center H) ≃* StatedProj (StatedSU 3 (3 ^ 1) K')) : False := by
  have : CharP K' 3 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_three
    (by rw [hK', ← pow_mul])
  obtain ⟨e₁, e₂, g, h, he₁, he₂, he₁₂, he₁1, hg₁, hg₂, hh₁, hh₂⟩ :=
    exists_three_square_psu33 hK'
  exact false_of_mulEquiv_three_square h3 hdet hZ3 e he₁ he₂ he₁₂ he₁1 hg₁ hg₂ hh₁ hh₂

end CFSG.RankThree.SubgroupLists
