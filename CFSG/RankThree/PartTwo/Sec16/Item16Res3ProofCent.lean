module

public import CFSG.RankThree.PartTwo.Sec16.Item16Res3ProofModel
public import CFSG.RankThree.PartTwo.Sec16.Item163ResProofU35
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res3U35

open CFSG.RankThree.PartOne.HNB CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts CFSG.Quasithin.H13 Matrix
open CFSG.Assembly.RankThreeEven (projSU)

theorem dMat_mul_apply (M : Matrix (Fin 3) (Fin 3) F25) (i j : Fin 3) :
    (U35A6.dMat om * M) i j = ![1, om, om ^ 2] i * M i j := by
  fin_cases i <;> simp [U35A6.dMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem mul_dMat_apply (M : Matrix (Fin 3) (Fin 3) F25) (i j : Fin 3) :
    (M * U35A6.dMat om) i j = M i j * ![1, om, om ^ 2] j := by
  fin_cases j <;> simp [U35A6.dMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem cMat_mul_apply (M : Matrix (Fin 3) (Fin 3) F25) (i j : Fin 3) :
    ((U35A6.cMat : Matrix (Fin 3) (Fin 3) F25) * M) i j = M (i - 1) j := by
  fin_cases i
  · simp only [U35A6.cMat, Matrix.mul_apply, Fin.sum_univ_three]
    simp
    rfl
  · simp [U35A6.cMat, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [U35A6.cMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem mul_cMat_apply (M : Matrix (Fin 3) (Fin 3) F25) (i j : Fin 3) :
    (M * (U35A6.cMat : Matrix (Fin 3) (Fin 3) F25)) i j = M i (j + 1) := by
  fin_cases j <;> simp [U35A6.cMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem diag_ne : ∀ i j : Fin 3, i ≠ j →
    (![1, om, om ^ 2] : Fin 3 → F25) i ≠ ![1, om, om ^ 2] j := by
  decide +kernel

theorem eq_zero_of_mul_eq_mul {a b m : F25} (hab : a ≠ b) (h : a * m = m * b) : m = 0 := by
  have h1 : (a - b) * m = 0 := by
    rw [sub_mul, h, mul_comm b m, sub_self]
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact absurd (sub_eq_zero.mp h2) hab
  · exact h2

theorem eq_smul_one_of_comm {M : Matrix (Fin 3) (Fin 3) F25}
    (h1 : U35A6.dMat om * M = M * U35A6.dMat om)
    (h2 : (U35A6.cMat : Matrix (Fin 3) (Fin 3) F25) * M = M * U35A6.cMat) :
    M = M 0 0 • 1 := by
  have hoff : ∀ i j : Fin 3, i ≠ j → M i j = 0 := fun i j hij => by
    have e := congrFun (congrFun h1 i) j
    rw [dMat_mul_apply, mul_dMat_apply] at e
    exact eq_zero_of_mul_eq_mul (diag_ne i j hij) e
  have e10 := congrFun (congrFun h2 1) 0
  have e21 := congrFun (congrFun h2 2) 1
  rw [cMat_mul_apply, mul_cMat_apply] at e10 e21
  have e10' : M 0 0 = M 1 1 := e10
  have e21' : M 1 1 = M 2 2 := e21
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hoff 0 1 (by decide), hoff 0 2 (by decide), hoff 1 0 (by decide),
      hoff 1 2 (by decide), hoff 2 0 (by decide), hoff 2 1 (by decide), e10', e21']

theorem exists_eq_om_pow : ∀ c : F25, c ^ 3 = 1 → ∃ k : Fin 3, c = om ^ (k : ℕ) := by
  decide +kernel

theorem exists_N_rel : ∀ k₁ k₂ : Fin 3, ∃ a b : Fin 3,
    U35A6.dMat om * (U35A6.dMat om ^ (a : ℕ) * U35A6.cMat ^ (b : ℕ)) =
        om ^ (k₁ : ℕ) • (U35A6.dMat om ^ (a : ℕ) * U35A6.cMat ^ (b : ℕ) * U35A6.dMat om) ∧
      (U35A6.cMat : Matrix (Fin 3) (Fin 3) F25) * (U35A6.dMat om ^ (a : ℕ) * U35A6.cMat ^ (b : ℕ)) =
        om ^ (k₂ : ℕ) • (U35A6.dMat om ^ (a : ℕ) * U35A6.cMat ^ (b : ℕ) * U35A6.cMat) := by
  decide +kernel

theorem det_dMat : (U35A6.dMat om).det = 1 := by
  rw [Matrix.det_fin_three]
  decide +kernel

theorem det_cMat : (U35A6.cMat : Matrix (Fin 3) (Fin 3) F25).det = 1 := by
  rw [Matrix.det_fin_three]
  decide +kernel

theorem comm_of_rel {X Bm Nm Ni : Matrix (Fin 3) (Fin 3) F25} {c : F25} (hc : c ≠ 0)
    (hNi : Ni * Nm = 1) (hNi' : Nm * Ni = 1) (hN : X * Nm = c • (Nm * X))
    (hB : X * Bm = c • (Bm * X)) : X * (Ni * Bm) = Ni * Bm * X := by
  have h1 : Ni * X = c • (X * Ni) := by
    calc Ni * X = Ni * X * (Nm * Ni) := by rw [hNi', Matrix.mul_one]
      _ = Ni * (X * Nm) * Ni := by simp only [Matrix.mul_assoc]
      _ = Ni * (c • (Nm * X)) * Ni := by rw [hN]
      _ = c • (Ni * Nm * X * Ni) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
          simp only [Matrix.mul_assoc]
      _ = c • (X * Ni) := by rw [hNi, Matrix.one_mul]
  have h2 : c • (X * (Ni * Bm)) = c • (Ni * Bm * X) := by
    calc c • (X * (Ni * Bm)) = (c • (X * Ni)) * Bm := by
          rw [Matrix.smul_mul, Matrix.mul_assoc]
      _ = Ni * X * Bm := by rw [h1]
      _ = Ni * (X * Bm) := by rw [Matrix.mul_assoc]
      _ = Ni * (c • (Bm * X)) := by rw [hB]
      _ = c • (Ni * Bm * X) := by rw [Matrix.mul_smul, Matrix.mul_assoc]
  exact smul_right_injective _ hc h2

theorem exists_eq_conj_of_fix (B : unitaryIsom3 hF) (h1 : psuConj hF B x1 = x1)
    (h2 : psuConj hF B x2 = x2) : ∃ e ∈ E0, psuConj hF B = MulAut.conj e := by
  have hmap : ∀ X : Matrix (Fin 3) (Fin 3) F25, X.map ⇑(1 : F25 ≃+* F25) = X := fun X => by
    ext i j
    rfl
  have hf1 : (psuConj hF B * psuField hF 1) (g1 : PU5) = g1 := by
    rw [map_one, mul_one]
    exact h1
  have hf2 : (psuConj hF B * psuField hF 1) (g2 : PU5) = g2 := by
    rw [map_one, mul_one]
    exact h2
  obtain ⟨c₁, hc₁⟩ := U35A6.exists_smul_of_fix hF B 1 g1 hf1
  obtain ⟨c₂, hc₂⟩ := U35A6.exists_smul_of_fix hF B 1 g2 hf2
  rw [hmap, coe_g1] at hc₁
  rw [hmap, coe_g2] at hc₂
  set Bm := ((B : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) with hBm
  set Bi := (((B : GL (Fin 3) F25)⁻¹ : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) with hBi
  have hBB : Bi * Bm = 1 := by rw [hBi, hBm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hBB' : Bm * Bi = 1 := by rw [hBi, hBm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hR1 : U35A6.dMat om * Bm = c₁ • (Bm * U35A6.dMat om) := by
    conv_lhs => rw [hc₁]
    rw [Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, hBB, Matrix.mul_one]
  have hR2 : (U35A6.cMat : Matrix (Fin 3) (Fin 3) F25) * Bm = c₂ • (Bm * U35A6.cMat) := by
    conv_lhs => rw [hc₂]
    rw [Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, hBB, Matrix.mul_one]
  have hdetB : Bm.det * Bi.det = 1 := by rw [← Matrix.det_mul, hBB', Matrix.det_one]
  have hcube : ∀ {X : Matrix (Fin 3) (Fin 3) F25} {c : F25}, X.det = 1 →
      X = c • (Bm * X * Bi) → c ^ 3 = 1 := fun {X c} hX hXc => by
    have e := congrArg Matrix.det hXc
    rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, hX, Fintype.card_fin, mul_one,
      hdetB, mul_one] at e
    exact e.symm
  obtain ⟨k₁, hk₁⟩ := exists_eq_om_pow c₁ (hcube det_dMat hc₁)
  obtain ⟨k₂, hk₂⟩ := exists_eq_om_pow c₂ (hcube det_cMat hc₂)
  obtain ⟨a, b, hN1, hN2⟩ := exists_N_rel k₁ k₂
  rw [← hk₁] at hN1
  rw [← hk₂] at hN2
  have hc₁0 : c₁ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc₁
    have := congrArg (fun X => X 0 0) hc₁
    simp [U35A6.dMat] at this
  have hc₂0 : c₂ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc₂
    have := congrArg (fun X => X 1 0) hc₂
    simp [U35A6.cMat] at this
  set N : SU5 := g1 ^ (a : ℕ) * g2 ^ (b : ℕ) with hN
  have hNm : ((N : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) =
      U35A6.dMat om ^ (a : ℕ) * U35A6.cMat ^ (b : ℕ) := by
    rw [hN, coe_mul, coe_pow, coe_pow, coe_g1, coe_g2]
  set Nm := ((N : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) with hNmdef
  set Ni := (((N : GL (Fin 3) F25)⁻¹ : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) with hNi
  have hNN : Ni * Nm = 1 := by rw [hNi, hNmdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hNN' : Nm * Ni = 1 := by rw [hNi, hNmdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [← hNm] at hN1 hN2
  have hM1 := comm_of_rel hc₁0 hNN hNN' hN1 hR1
  have hM2 := comm_of_rel hc₂0 hNN hNN' hN2 hR2
  have hMs := eq_smul_one_of_comm hM1 hM2
  set m := (Ni * Bm) 0 0 with hm
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hMs
    have e : Ni * Bm * (Bi * Nm) = 1 := by
      calc Ni * Bm * (Bi * Nm) = Ni * (Bm * Bi) * Nm := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hBB', Matrix.mul_one, hNN]
    rw [hMs, Matrix.zero_mul] at e
    have := congrArg (fun X => X 0 0) e
    simp at this
  set N' : unitaryIsom3 hF := ⟨N, unitarySU_le_unitaryIsom3 N.2⟩ with hN'
  set s : unitaryIsom3 hF := N'⁻¹ * B with hs
  have hsc : (s : GL (Fin 3) F25) = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 m hm0) := by
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_mk0,
      ← Matrix.smul_one_eq_diagonal, ← hMs]
    rfl
  have hBs : B = N' * s := by rw [hs, mul_inv_cancel_left]
  refine ⟨x1 ^ (a : ℕ) * x2 ^ (b : ℕ), mem_E0 _ _, ?_⟩
  rw [hBs, map_mul, U35A6.psuConj_scalar hF s _ hsc, mul_one, hN',
    ← conj_mk_eq_psuConj N, hN, QuotientGroup.mk_mul, QuotientGroup.mk_pow,
    QuotientGroup.mk_pow]

theorem eq_one_of_fix_a7 {K : Subgroup PU5} (hK : Nonempty (↥K ≃* alternatingGroup (Fin 7)))
    (σ : MulAut PU5) (hσ : ∀ k ∈ K, σ k = k) : σ = 1 := by
  have hK2520 : Nat.card K = 2520 := by
    obtain ⟨φ⟩ := hK
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
  obtain ⟨g, hg⟩ := exists_conj_E0_le (K := K) (by rw [hK2520]; norm_num)
  set β := MulAut.conj g * σ * (MulAut.conj g)⁻¹ with hβ
  have hβK : ∀ k ∈ K, β (g * k * g⁻¹) = g * k * g⁻¹ := by
    intro k hk
    simp only [hβ, MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, MulAut.conj_symm_apply]
    rw [show g⁻¹ * (g * k * g⁻¹) * g = k by group, hσ k hk]
  have hβE : ∀ y ∈ E0, β y = y := by
    intro y hy
    have h1 := hβK _ (hg y hy)
    rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h1
  obtain ⟨B, τ, hBτ⟩ := exists_psuConj_mul_psuField (h := hF) (by norm_num) β
  have hτ : τ = 1 := by
    have hτω := U35A6.sigma_eq_of_fix hF om_pow_three B τ
      (by rw [← hBτ]; exact hβE _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers x1)))
      (by rw [← hBτ]; exact hβE _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x2)))
    exact U35A6.eq_one_of_fix_omega hF om_pow_three om_ne_one hτω
  rw [hτ, map_one, mul_one] at hBτ
  obtain ⟨e, he, hBe⟩ := exists_eq_conj_of_fix B
    (by rw [← hBτ]; exact hβE _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers x1)))
    (by rw [← hBτ]; exact hβE _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x2)))
  have hβe : β = MulAut.conj e := hBτ.trans hBe
  obtain ⟨-, hZ, -, -, -⟩ := KFacts.KS14.a7_facts ↥K hK
  have heK : g⁻¹ * e * g ∈ K := hg e he
  have hcen : (⟨g⁻¹ * e * g, heK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    have h1 := hβK k k.2
    rw [hβe, MulAut.conj_apply] at h1
    simp only [Subgroup.coe_mul]
    calc (k : PU5) * (g⁻¹ * e * g) = g⁻¹ * (g * k * g⁻¹) * e * g := by group
      _ = g⁻¹ * (e * (g * k * g⁻¹) * e⁻¹) * e * g := by rw [h1]
      _ = g⁻¹ * e * g * k := by group
  rw [hZ, Subgroup.mem_bot] at hcen
  have he1 : e = 1 := by
    have h1 : g⁻¹ * e * g = 1 := congrArg Subtype.val hcen
    calc e = g * (g⁻¹ * e * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hβ1 : β = 1 := by rw [hβe, he1, map_one]
  calc σ = (MulAut.conj g)⁻¹ * β * MulAut.conj g := by rw [hβ]; group
    _ = 1 := by rw [hβ1, mul_one, inv_mul_cancel]

theorem ks163U35CentA7 : KS163U35CentA7 := by
  intro _ K hK σ hσ
  set φ := equivPU with hφ
  set σ' : MulAut PU5 := MulAut.congr φ σ with hσ'
  have h1 : σ' = 1 := by
    refine eq_one_of_fix_a7 (K := K.map φ.toMonoidHom) ?_ σ' ?_
    · obtain ⟨e⟩ := hK
      exact ⟨(K.equivMapOfInjective _ φ.injective).symm.trans e⟩
    · rintro _ ⟨k, hk, rfl⟩
      simp [hσ', hσ k hk]
  have h2 : σ = (MulAut.congr φ).symm σ' := by rw [hσ', MulEquiv.symm_apply_apply]
  rw [h2, h1, map_one]

end CFSG.RankThree.PartTwo.Sec16.Res3U35
