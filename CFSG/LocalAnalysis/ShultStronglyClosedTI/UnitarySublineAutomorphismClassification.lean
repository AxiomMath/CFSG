module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineAutomorphismMaps
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismCover

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryAutomorphism

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K] {J : HermitianForm 3 K}

theorem eq_one_or_conj_of_fix [Finite K] {q : ℕ} (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q) {σ : K ≃+* K}
    (hσ : ∀ x, J.conj x = x → σ x = x) : σ = 1 ∨ σ = J.conj := by
  set k0 := FixedBy.subfield K J.conj
  have hfin := huppert_II_10_4_fixedField_finrank_two J q hcard hfixed
  have hcardG : Nat.card (K ≃ₐ[k0] K) = 2 := (IsGalois.card_aut_eq_finrank k0 K).trans hfin
  let σ' : K ≃ₐ[k0] K := AlgEquiv.ofRingEquiv (f := σ) (fun x => hσ _ x.2)
  let c' : K ≃ₐ[k0] K := AlgEquiv.ofRingEquiv (f := J.conj) (fun x => x.2)
  have hc' : c' ≠ 1 := by
    intro h
    have hall : ∀ x : K, J.conj x = x := fun x => by
      have := DFunLike.congr_fun h x
      exact this
    have hK : Nat.card {x : K // J.conj x = x} = Nat.card K :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hall)
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hfixed, hcard] at hK
    rw [hcard] at h1
    have hq : 2 ≤ q := by
      by_contra hq
      interval_cases q <;> simp at h1
    nlinarith
  obtain ⟨x, y, hxy, hU⟩ := Nat.card_eq_two_iff.mp hcardG
  have hmem : ∀ τ : K ≃ₐ[k0] K, τ = x ∨ τ = y := fun τ => by
    have : τ ∈ ({x, y} : Set (K ≃ₐ[k0] K)) := hU ▸ Set.mem_univ τ
    simpa using this
  have hσ' : σ' = 1 ∨ σ' = c' := by
    rcases hmem 1 with h1 | h1 <;> rcases hmem c' with h2 | h2 <;> rcases hmem σ' with h3 | h3
    all_goals first
      | exact absurd (h2.trans h1.symm) hc'
      | exact Or.inl (h3.trans h1.symm)
      | exact Or.inr (h3.trans h2.symm)
  rcases hσ' with h | h
  · left
    exact RingEquiv.ext fun a => DFunLike.congr_fun h a
  · right
    exact RingEquiv.ext fun a => DFunLike.congr_fun h a

theorem mul_scalar_eq_of_conj {A g g' : GL (Fin 3) K} {u : Kˣ}
    (h : A * g * A⁻¹ * GeneralLinearGroup.scalar (Fin 3) u = g') :
    (A : Matrix (Fin 3) (Fin 3) K) * g * scalar (Fin 3) (u : K) = g' * A := by
  have hc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  have h' : A * g * GeneralLinearGroup.scalar (Fin 3) u = g' * A := by
    rw [← h]
    calc A * g * GeneralLinearGroup.scalar (Fin 3) u
        = A * g * A⁻¹ * (A * GeneralLinearGroup.scalar (Fin 3) u) := by group
      _ = A * g * A⁻¹ * GeneralLinearGroup.scalar (Fin 3) u * A := by rw [hc]; group
  have := congrArg Units.val h'
  simpa only [Units.val_mul, GeneralLinearGroup.coe_scalar] using this

theorem det_ne_zero_GL (A : GL (Fin 3) K) : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
  rw [← GeneralLinearGroup.val_det_apply]
  exact Units.ne_zero _

theorem col_zero_of_fix_upper (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {A : GL (Fin 3) K}
    (hA : A ∈ J.unitarySubgroup) {u : Kˣ}
    (h : (A : Matrix (Fin 3) (Fin 3) K) * !![1, 0, 1; 0, 1, 0; 0, 0, 1] *
      scalar (Fin 3) (u : K) = !![1, 0, 1; 0, 1, 0; 0, 0, 1] * (A : Matrix (Fin 3) (Fin 3) K)) :
    (u : K) = 1 ∧ (A : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
  set M : Matrix (Fin 3) (Fin 3) K := (A : Matrix (Fin 3) (Fin 3) K) with hM
  have entry : ∀ i j, (M * (!![1, 0, 1; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) *
      scalar (Fin 3) (u : K)) i j =
      ((!![1, 0, 1; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) * M) i j := fun i j => by rw [h]
  have e00 := entry 0 0
  have e10 := entry 1 0
  have e20 := entry 2 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, scalar_apply, diagonal_apply] at e00 e10 e20
  have hu1 : (u : K) = 1 := by
    by_contra hu
    have hu' : (u : K) - 1 ≠ 0 := sub_ne_zero.mpr hu
    have h10 : M 1 0 = 0 := by
      have : M 1 0 * ((u : K) - 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hu'
    have h20 : M 2 0 = 0 := by
      have : M 2 0 * ((u : K) - 1) = 0 := by linear_combination e20
      exact (mul_eq_zero.mp this).resolve_right hu'
    have h00 : M 0 0 = 0 := by
      have : M 0 0 * ((u : K) - 1) = 0 := by linear_combination e00 + h20
      exact (mul_eq_zero.mp this).resolve_right hu'
    apply det_ne_zero_GL A
    rw [← hM, det_fin_three, h00, h10, h20]
    ring
  rw [hu1] at e00
  have h20 : M 2 0 = 0 := by linear_combination -e00
  refine ⟨hu1, ?_, h20⟩
  have hgram := (J.mem_unitarySubgroup_iff A).mp hA
  have g00 := congrArg (fun B => B 0 0) hgram
  simp [hJ, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, ← hM, h20] at g00
  exact g00

theorem col_two_of_fix_lower (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {A : GL (Fin 3) K}
    (hA : A ∈ J.unitarySubgroup) {u : Kˣ}
    (h : (A : Matrix (Fin 3) (Fin 3) K) * !![1, 0, 0; 0, 1, 0; 1, 0, 1] *
      scalar (Fin 3) (u : K) = !![1, 0, 0; 0, 1, 0; 1, 0, 1] * (A : Matrix (Fin 3) (Fin 3) K)) :
    (u : K) = 1 ∧ (A : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
  set M : Matrix (Fin 3) (Fin 3) K := (A : Matrix (Fin 3) (Fin 3) K) with hM
  have entry : ∀ i j, (M * (!![1, 0, 0; 0, 1, 0; 1, 0, 1] : Matrix (Fin 3) (Fin 3) K) *
      scalar (Fin 3) (u : K)) i j =
      ((!![1, 0, 0; 0, 1, 0; 1, 0, 1] : Matrix (Fin 3) (Fin 3) K) * M) i j := fun i j => by rw [h]
  have e02 := entry 0 2
  have e12 := entry 1 2
  have e22 := entry 2 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, scalar_apply, diagonal_apply] at e02 e12 e22
  have hu1 : (u : K) = 1 := by
    by_contra hu
    have hu' : (u : K) - 1 ≠ 0 := sub_ne_zero.mpr hu
    have h02 : M 0 2 = 0 := by
      have : M 0 2 * ((u : K) - 1) = 0 := by linear_combination e02
      exact (mul_eq_zero.mp this).resolve_right hu'
    have h12 : M 1 2 = 0 := by
      have : M 1 2 * ((u : K) - 1) = 0 := by linear_combination e12
      exact (mul_eq_zero.mp this).resolve_right hu'
    have h22 : M 2 2 = 0 := by
      have : M 2 2 * ((u : K) - 1) = 0 := by linear_combination e22 + h02
      exact (mul_eq_zero.mp this).resolve_right hu'
    apply det_ne_zero_GL A
    rw [← hM, det_fin_three, h02, h12, h22]
    ring
  rw [hu1] at e22
  have h02 : M 0 2 = 0 := by linear_combination -e22
  refine ⟨hu1, h02, ?_⟩
  have hgram := (J.mem_unitarySubgroup_iff A).mp hA
  have g22 := congrArg (fun B => B 2 2) hgram
  simp [hJ, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, ← hM, h02] at g22
  exact g22

section Classification

variable [Finite K] [CharP K 2] {C : Subgroup J.specialSubgroup} [C.Normal]

omit [Finite K] in
theorem glAut_sublineHom_upperSL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (σ : K ≃+* K)
    (t : Multiplicative (unitaryCoverFixedField J)) :
    ((glAut σ ((sublineHom J hJ (upperSL _ t) : J.specialSubgroup) : GL (Fin 3) K) :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, σ (fixedToK J t.toAdd); 0, 1, 0; 0, 0, 1] := by
  rw [coe_glAut, coe_sublineHom_upperSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [Finite K] in
theorem glAut_sublineHom_lowerSL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (σ : K ≃+* K)
    (t : Multiplicative (unitaryCoverFixedField J)) :
    ((glAut σ ((sublineHom J hJ (lowerSL _ t) : J.specialSubgroup) : GL (Fin 3) K) :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, 0; 0, 1, 0; σ (fixedToK J t.toAdd), 0, 1] := by
  rw [coe_glAut, coe_sublineHom_lowerSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem mem_range_sublineAutHom {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hC : C ≤ scalarCenter J)
    {β : MulAut (J.specialSubgroup ⧸ C)} (hβ : ∀ x ∈ sublineL J C hJ, β x = x) :
    β ∈ (sublineAutHom J C hJ hC).range := by
  have hq : 2 < 2 ^ f := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right two_pos hf)
  have hP := center_psu_eq_bot (2 ^ f) hq hcard hfixed hJ
  have hcen := center_eq_ker_coverToPSU hJ hC hP
  have : Group.IsPerfect J.specialSubgroup :=
    isPerfect_specialSubgroup Nat.prime_two hq hcard hfixed hJ
  obtain ⟨σ, A, hA, hAg⟩ :=
    exists_isometry_psu_of_card Nat.prime_two hq hcard hfixed hJ (coverAutPSU hJ hC hcen β)
  have hfixm : ∀ m : SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J), ∃ u : Kˣ,
      A * glAut σ ((sublineHom J hJ m : J.specialSubgroup) : GL (Fin 3) K) * A⁻¹ *
        GeneralLinearGroup.scalar (Fin 3) u =
        ((sublineHom J hJ m : J.specialSubgroup) : GL (Fin 3) K) := by
    intro m
    obtain ⟨hg, hβg⟩ := hAg (sublineHom J hJ m)
    have hfixβ : β ((sublineHom J hJ m : J.specialSubgroup) : J.specialSubgroup ⧸ C) =
        ((sublineHom J hJ m : J.specialSubgroup) : J.specialSubgroup ⧸ C) := hβ _ ⟨m, rfl⟩
    have h1 := coverAutPSU_apply hJ hC hcen β
      ((sublineHom J hJ m : J.specialSubgroup) : J.specialSubgroup ⧸ C)
    rw [hfixβ, coverToPSU_mk, hβg] at h1
    exact psuMk_eq_psuMk_iff.mp h1
  set M : Matrix (Fin 3) (Fin 3) K := (A : Matrix (Fin 3) (Fin 3) K) with hM
  obtain ⟨u1, hu1⟩ := hfixm (upperSL _ (Multiplicative.ofAdd 1))
  have hm1 := mul_scalar_eq_of_conj hu1
  rw [glAut_sublineHom_upperSL, coe_sublineHom_upperSL] at hm1
  simp only [toAdd_ofAdd, map_one] at hm1
  obtain ⟨-, h10, h20⟩ := col_zero_of_fix_upper hJ hA hm1
  obtain ⟨u2, hu2⟩ := hfixm (lowerSL _ (Multiplicative.ofAdd 1))
  have hm2 := mul_scalar_eq_of_conj hu2
  rw [glAut_sublineHom_lowerSL, coe_sublineHom_lowerSL] at hm2
  simp only [toAdd_ofAdd, map_one] at hm2
  obtain ⟨-, h02, h12⟩ := col_two_of_fix_lower hJ hA hm2
  obtain ⟨h01, h21⟩ :=
    CFSG.ShultStronglyClosedTI.TwoCoreGrowth.unitary_outer_plane_preserves_middle J hJ A hA h10 h12
  rw [← hM] at h10 h20 h02 h12 h01 h21
  have hgram := (J.mem_unitarySubgroup_iff A).mp hA
  have g02 := congrArg (fun B => B 0 2) hgram
  have g11 := congrArg (fun B => B 1 1) hgram
  simp [hJ, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, ← hM, h10, h20,
    h01, h21, h02, h12] at g02 g11
  have hb0 : M 1 1 ≠ 0 := by
    rintro h
    simp [h] at g11
  have hroot : ∀ x : unitaryCoverFixedField J, M 0 0 * σ (x : K) = (x : K) * M 2 2 := by
    intro x
    obtain ⟨u, hu⟩ := hfixm (upperSL _ (Multiplicative.ofAdd x))
    have hm := mul_scalar_eq_of_conj hu
    rw [glAut_sublineHom_upperSL, coe_sublineHom_upperSL] at hm
    simp only [toAdd_ofAdd] at hm
    have e11 := congrFun (congrFun hm 1) 1
    have e02 := congrFun (congrFun hm 0) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, scalar_apply, diagonal_apply, ← hM, h10,
      h01, h21, h02, h12] at e11 e02
    have hu1 : (u : K) = 1 := by
      have := e11
      rw [mul_eq_left₀ hb0] at this
      exact this
    rw [hu1, mul_one] at e02
    linear_combination e02
  have hac : M 0 0 = M 2 2 := by simpa using hroot 1
  have ha0 : M 0 0 ≠ 0 := by
    rintro h
    rw [← hac, h] at g02
    simp at g02
  have hσk : ∀ x : K, J.conj x = x → σ x = x := by
    intro x hx
    have := hroot ⟨x, hx⟩
    rw [← hac] at this
    exact mul_left_cancel₀ ha0 (this.trans (mul_comm _ _))
  have hσmem : σ ∈ conjGroup J := by
    rcases eq_one_or_conj_of_fix hcard hfixed hσk with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  set a : Kˣ := Units.mk0 (M 0 0) ha0
  set d : Kˣ := Units.mk0 (M 1 1) hb0 * a⁻¹
  have hna : M 0 0 * J.conj (M 0 0) = 1 := by
    rw [← hac] at g02
    linear_combination g02
  have hd : d ∈ normOne J := by
    change ((Units.mk0 (M 1 1) hb0 * a⁻¹ : Kˣ) : K) *
      J.conj ((Units.mk0 (M 1 1) hb0 * a⁻¹ : Kˣ) : K) = 1
    simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, a, map_mul, map_inv₀]
    have hc0 : J.conj (M 0 0) ≠ 0 := (map_ne_zero J.conj).mpr ha0
    field_simp
    linear_combination g11 - hna
  have hAeq : A = GeneralLinearGroup.scalar (Fin 3) a * diag3 1 d 1 := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_diag3, ← hM]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [a, d, scalar_apply, diagonal_apply, Matrix.mul_apply, h10, h20, h01, h21, h02, h12,
        ← hac]
    field_simp
  refine ⟨⟨⟨d, hd⟩, ⟨σ, hσmem⟩⟩, eq_of_coverToPSU_comp_eq hJ hC hcen fun x => ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C x
  obtain ⟨hg, hΨ⟩ := sublineAutHom_mk hJ hC ⟨⟨d, hd⟩, ⟨σ, hσmem⟩⟩ g
  obtain ⟨hg', hβg⟩ := hAg g
  rw [QuotientGroup.mk'_apply, hΨ, coverToPSU_mk, ← coverAutPSU_apply hJ hC hcen β,
    coverToPSU_mk, hβg]
  congr 1
  apply Subtype.ext
  change diag3 1 d 1 * glAut σ (g : GL (Fin 3) K) * (diag3 1 d 1)⁻¹ =
    A * glAut σ (g : GL (Fin 3) K) * A⁻¹
  rw [hAeq, scalar_mul_conj_eq]

end Classification

end CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
