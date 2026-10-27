module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.MatrixHeis
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.PSLFormsFinite
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOddHigherLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL proj conjAut fieldAut dualAut
  conjAut_proj coe_slConjugation fieldAut_proj dualAut_proj
  odd_linear_graph_field_involution_conjugacy)
open CFSG.LocalAnalysis.ComponentInitial.OddHigherLinear (transpose_eq_or_eq_neg_of_sq
  field_involution_conjugacy)

variable {K : Type} [Field K] [Finite K] {n p e : ℕ}

omit [Finite K] in
private theorem conjAut_apply_unipSL {N N' : Matrix (Fin n) (Fin n) K} (hN2 : N * N = 0)
    (A : GL (Fin n) K)
    (hA : (A : Matrix (Fin n) (Fin n) K) * N *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = N') (hN'2 : N' * N' = 0) :
    conjAut n K A (proj n K (unipSL N hN2)) = proj n K (unipSL N' hN'2) := by
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, coe_unipSL, coe_unipSL]
  have hAinv : (A : Matrix (Fin n) (Fin n) K) *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (A : Matrix (Fin n) (Fin n) K) * (1 + N) *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = ((A : Matrix (Fin n) (Fin n) K) * 1 + (A : Matrix (Fin n) (Fin n) K) * N) *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [Matrix.mul_add]
    _ = ((A : Matrix (Fin n) (Fin n) K) * 1) *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) +
        ((A : Matrix (Fin n) (Fin n) K) * N) *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [Matrix.add_mul]
    _ = 1 + N' := by rw [Matrix.mul_one, hAinv, hA]

theorem exists_inv_unipSL_conjAut (hn : 3 ≤ n) (A : GL (Fin n) K) (h2 : conjAut n K A ^ 2 = 1)
    (h1 : conjAut n K A ≠ 1) :
    ∃ (N : Matrix (Fin n) (Fin n) K) (hN2 : N * N = 0), N ≠ 0 ∧ IsRankTwoSqZero N ∧
      conjAut n K A (proj n K (unipSL N hN2)) = (proj n K (unipSL N hN2))⁻¹ := by
  classical
  have hAA1 : conjAut n K (A * A) = 1 := by
    rw [map_mul, ← pow_two, h2]
  obtain ⟨-, c, hc⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one
      hn (A * A) 1 (by rw [hAA1, map_one, mul_one])
  have hA2 : (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) =
      (c : K) • 1 := by
    rw [← Units.val_mul, ← hc, GeneralLinearGroup.coe_scalar, smul_one_eq_diagonal]
    rfl
  have hAnot : ∀ d : K, (A : Matrix (Fin n) (Fin n) K) ≠ d • 1 := by
    intro d hd
    apply h1
    have hd0 : d ≠ 0 := by
      rintro rfl
      have hunit : IsUnit (A : Matrix (Fin n) (Fin n) K).det := Matrix.isUnits_det_units A
      have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      rw [hd, zero_smul, Matrix.det_zero] at hunit
      exact not_isUnit_zero hunit
    have hAs : A = GeneralLinearGroup.scalar (Fin n) (Units.mk0 d hd0) := by
      apply Units.ext
      rw [hd, GeneralLinearGroup.coe_scalar, Units.val_mk0, smul_one_eq_diagonal]
      rfl
    rw [hAs]
    exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_scalar (Units.mk0 d hd0)
  obtain ⟨N, hN0, hNr, hAN⟩ := exists_rankTwo_anticomm hn hA2 hAnot
  have hN2 : N * N = 0 := hNr.mul_self_eq_zero
  have hNneg : (-N) * (-N) = 0 := by rw [neg_mul_neg, hN2]
  have hAinv : (A : Matrix (Fin n) (Fin n) K) *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAN' : (A : Matrix (Fin n) (Fin n) K) * N *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = -N := by
    rw [hAN, Matrix.neg_mul, Matrix.mul_assoc, hAinv, Matrix.mul_one]
  refine ⟨N, hN2, hN0, hNr, ?_⟩
  rw [conjAut_apply_unipSL hN2 A hAN' hNneg, ← map_inv, unipSL_inv]

theorem inverts_good_conjAut (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p] (hK : Nat.card K = p ^ e)
    (h3 : 3 < p ^ e) (hn : 3 ≤ n) (A : GL (Fin n) K) (h2 : conjAut n K A ^ 2 = 1)
    (h1 : conjAut n K A ≠ 1) :
    ∃ x : projectiveSL n K, orderOf x = p ∧ conjAut n K A x = x⁻¹ ∧
      (IsSpecialGood p x ∨ IsOrbitGood p x) := by
  obtain ⟨N, hN2, hN0, -, hinv⟩ := exists_inv_unipSL_conjAut hn A h2 h1
  obtain ⟨hxord, hxgood⟩ := good_unipSL hp hp2 hK h3 hn hN0 hN2
  exact ⟨proj n K (unipSL N hN2), hxord, hinv, Or.inl hxgood⟩

omit [Finite K] in
private theorem map_unipSL (σ : K ≃+* K) {N N' : Matrix (Fin n) (Fin n) K}
    (hN2 : N * N = 0) (hN'2 : N' * N' = 0) (h : N.map σ = N') :
    SpecialLinearGroup.map σ.toRingHom (unipSL N hN2) = unipSL N' hN'2 := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_unipSL, coe_unipSL]
  calc ((1 + N) : Matrix (Fin n) (Fin n) K).map (σ : K → K)
      = (1 : Matrix (Fin n) (Fin n) K).map (σ : K → K) + N.map (σ : K → K) :=
        Matrix.map_add _ (map_add σ) _ _
    _ = 1 + N' := by rw [Matrix.map_one _ (map_zero σ) (map_one σ), h]

theorem inverts_good_fieldAut (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p] (hK : Nat.card K = p ^ e)
    (h3 : 3 < p ^ e) (hn : 3 ≤ n) (σ : K ≃+* K) (hσ : σ ≠ 1) (hσσ : σ * σ = 1) :
    ∃ x : projectiveSL n K, orderOf x = p ∧ fieldAut n K σ x = x⁻¹ ∧
      (IsSpecialGood p x ∨ IsOrbitGood p x) := by
  classical
  have hσσ' : ∀ x, σ (σ x) = x := fun x => by rw [← RingAut.mul_apply, hσσ]; rfl
  obtain ⟨N, hN0, hN2, hNmap⟩ := exists_sq_zero_field (by omega : 2 ≤ n) hσ hσσ'
  have hNneg : (-N) * (-N) = 0 := by rw [neg_mul_neg, hN2]
  obtain ⟨hxord, hxgood⟩ := good_unipSL hp hp2 hK h3 hn hN0 hN2
  refine ⟨proj n K (unipSL N hN2), hxord, ?_, Or.inl hxgood⟩
  rw [fieldAut_proj, map_unipSL σ hN2 hNneg hNmap, ← map_inv, unipSL_inv]

omit [Finite K] in
private theorem dualAut_apply_unipSL {N : Matrix (Fin n) (Fin n) K} (hN2 : N * N = 0)
    (hT : (-(Nᵀ)) * (-(Nᵀ)) = 0) :
    dualAut n K (proj n K (unipSL N hN2)) = proj n K (unipSL (-(Nᵀ)) hT) := by
  rw [dualAut_proj, unipSL_inv]
  congr 1
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_transpose, coe_unipSL, coe_unipSL, Matrix.transpose_add,
    Matrix.transpose_one, Matrix.transpose_neg]

omit [Finite K] in
private theorem two_ne_zero_of_charP (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p] :
    (2 : K) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp h
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hge : 2 ≤ p := hp.two_le
  omega

theorem exists_inv_unipSL_conjAut_dualAut (h2K : (2 : K) ≠ 0) (hn : 3 ≤ n) (A : GL (Fin n) K)
    (h2 : (conjAut n K A * fieldAut n K 1 * dualAut n K) ^ 2 = 1) :
    ∃ (N : Matrix (Fin n) (Fin n) K) (hN2 : N * N = 0), N ≠ 0 ∧ IsRankTwoSqZero N ∧
      (conjAut n K A * fieldAut n K 1 * dualAut n K) (proj n K (unipSL N hN2)) =
        (proj n K (unipSL N hN2))⁻¹ := by
  classical
  have hAd : IsUnit (A : Matrix (Fin n) (Fin n) K).det := Matrix.isUnits_det_units A
  have hex : ∃ N : Matrix (Fin n) (Fin n) K, N ≠ 0 ∧ IsRankTwoSqZero N ∧
      (A : Matrix (Fin n) (Fin n) K) * Nᵀ = N * (A : Matrix (Fin n) (Fin n) K) := by
    rcases transpose_eq_or_eq_neg_of_sq hn A h2 with hAs | hAs
    · exact exists_rankTwo_symm hn hAd hAs
    · exact exists_rankTwo_alt h2K hn hAd hAs
  obtain ⟨N, hN0, hNr, hAN⟩ := hex
  have hN2 : N * N = 0 := hNr.mul_self_eq_zero
  have hNneg : (-N) * (-N) = 0 := by rw [neg_mul_neg, hN2]
  have hT : (-(Nᵀ)) * (-(Nᵀ)) = 0 := by
    rw [neg_mul_neg, ← Matrix.transpose_mul, hN2, Matrix.transpose_zero]
  have hAinv : (A : Matrix (Fin n) (Fin n) K) *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAN' : (A : Matrix (Fin n) (Fin n) K) * Nᵀ *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = N := by
    rw [hAN, Matrix.mul_assoc, hAinv, Matrix.mul_one]
  have hneg : (A : Matrix (Fin n) (Fin n) K) * (-(Nᵀ)) *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = -N := by
    rw [Matrix.mul_neg, Matrix.neg_mul, hAN']
  refine ⟨N, hN2, hN0, hNr, ?_⟩
  simp only [map_one, MulAut.mul_apply, MulAut.one_apply]
  rw [dualAut_apply_unipSL hN2 hT, conjAut_apply_unipSL hT A hneg hNneg, ← map_inv, unipSL_inv]

theorem inverts_good_conjAut_dualAut (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p]
    (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) (hn : 3 ≤ n) (A : GL (Fin n) K)
    (h2 : (conjAut n K A * fieldAut n K 1 * dualAut n K) ^ 2 = 1) :
    ∃ x : projectiveSL n K, orderOf x = p ∧
      (conjAut n K A * fieldAut n K 1 * dualAut n K) x = x⁻¹ ∧
      (IsSpecialGood p x ∨ IsOrbitGood p x) := by
  obtain ⟨N, hN2, hN0, -, hinv⟩ :=
    exists_inv_unipSL_conjAut_dualAut (two_ne_zero_of_charP hp hp2) hn A h2
  obtain ⟨hxord, hxgood⟩ := good_unipSL hp hp2 hK h3 hn hN0 hN2
  exact ⟨proj n K (unipSL N hN2), hxord, hinv, Or.inl hxgood⟩

theorem inverts_good_fieldAut_dualAut (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p]
    (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) (hn : 3 ≤ n) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hσσ : σ * σ = 1) :
    ∃ x : projectiveSL n K, orderOf x = p ∧ (fieldAut n K σ * dualAut n K) x = x⁻¹ ∧
      (IsSpecialGood p x ∨ IsOrbitGood p x) := by
  classical
  have hσσ' : ∀ x, σ (σ x) = x := fun x => by rw [← RingAut.mul_apply, hσσ]; rfl
  obtain ⟨N, hN0, hN2, hNmapT⟩ := exists_sq_zero_herm (by omega : 2 ≤ n) hσ hσσ'
  have hNneg : (-N) * (-N) = 0 := by rw [neg_mul_neg, hN2]
  have hT : (-(Nᵀ)) * (-(Nᵀ)) = 0 := by
    rw [neg_mul_neg, ← Matrix.transpose_mul, hN2, Matrix.transpose_zero]
  have hmap : (-(Nᵀ)).map σ = -N := by
    rw [Matrix.map_neg (σ : K → K) (map_neg σ), Matrix.transpose_map, hNmapT]
  obtain ⟨hxord, hxgood⟩ := good_unipSL hp hp2 hK h3 hn hN0 hN2
  refine ⟨proj n K (unipSL N hN2), hxord, ?_, Or.inl hxgood⟩
  simp only [MulAut.mul_apply]
  rw [dualAut_apply_unipSL hN2 hT, fieldAut_proj, map_unipSL σ hT hNneg hmap, ← map_inv,
    unipSL_inv]

theorem involInvertsGood_projectiveSL (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p]
    (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) (hn : 3 ≤ n) :
    InvolInvertsGood p (projectiveSL n K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  intro α hα
  have hα2 : α ^ 2 = 1 := by
    rw [← hα]
    exact pow_orderOf_eq_one α
  have hα1 : α ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hα
    omega
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · rw [pow_zero] at h3
      omega
    · exact h
  obtain ⟨A, σ, ε, hε, hstd⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_std_of_mulEquiv hn
      (MulEquiv.refl (projectiveSL n K)) α
  have hαeq : α = conjAut n K A * fieldAut n K σ * dualAut n K ^ ε := by
    rw [← hstd]
    ext x
    simp [MulAut.congr_apply]
  have hε01 : ε = 0 ∨ ε = 1 := by omega
  rcases hε01 with rfl | rfl
  · simp only [pow_zero, mul_one] at hαeq
    have hsq : (conjAut n K A * fieldAut n K σ) ^ 2 = 1 := by
      rw [hαeq] at hα2
      simpa using hα2
    by_cases hσ : σ = 1
    · subst hσ
      have h2 : conjAut n K A ^ 2 = 1 := by simpa using hsq
      have h1 : conjAut n K A ≠ 1 := by
        intro h
        apply hα1
        rw [hαeq, h]
        simp
      simpa [hαeq] using inverts_good_conjAut hp hp2 hK h3 hn A h2 h1
    · have hσσ : σ * σ = 1 := by
        have hsq' : conjAut n K (A * GeneralLinearGroup.map (σ : K →+* K) A) *
            fieldAut n K (σ * σ) = 1 := by
          rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_mul_fieldAut_mul,
            ← pow_two]
          exact hsq
        exact (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one
          hn _ _ hsq').1
      obtain ⟨H, hH⟩ := field_involution_conjugacy hp hp2 he hK hn A σ hσ hsq
      obtain ⟨x, hxord, hxinv, hxgood⟩ := inverts_good_fieldAut hp hp2 hK h3 hn σ hσ hσσ
      have hconj : α = conjAut n K H * fieldAut n K σ * (conjAut n K H)⁻¹ := by
        rw [hαeq]
        exact hH
      exact exists_inv_good_of_conj hconj hxord hxinv hxgood
  · simp only [pow_one] at hαeq
    have hsq : (conjAut n K A * fieldAut n K σ * dualAut n K) ^ 2 = 1 := by
      rw [hαeq] at hα2
      simpa using hα2
    by_cases hσ : σ = 1
    · subst hσ
      simpa [hαeq] using
        inverts_good_conjAut_dualAut hp hp2 hK h3 hn A (by simpa using hsq)
    · obtain ⟨heven, hσpow, H, hH⟩ :=
        odd_linear_graph_field_involution_conjugacy hp he hK hn A σ hσ hsq
      have hσσx : ∀ x : K, σ (σ x) = x := fun x => by
        rw [hσpow, hσpow, ← pow_mul, ← pow_add]
        have hhalf : e / 2 + e / 2 = e := by
          obtain ⟨k, hk⟩ := heven
          omega
        rw [hhalf, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
      have hσσ : σ * σ = 1 := by
        ext x
        rw [RingAut.mul_apply]
        simpa using hσσx x
      obtain ⟨x, hxord, hxinv, hxgood⟩ :=
        inverts_good_fieldAut_dualAut hp hp2 hK h3 hn σ hσ hσσ
      have hconj : α = conjAut n K H * (fieldAut n K σ * dualAut n K) * (conjAut n K H)⁻¹ := by
        rw [hαeq]
        exact hH
      exact exists_inv_good_of_conj hconj hxord hxinv hxgood

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
