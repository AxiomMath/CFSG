module

public import CFSG.Quasithin.EmptyFaithful.E22SFrame
public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofField

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Res6Proof

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification
open CFSG.Assembly (IsElemAbelian)
open Item211Lie2Proof Item211Res5Proof
open scoped MatrixGroups Matrix

section Tau

variable {K : Type} [Field K]

@[expose] def mOne : Matrix (Fin 3) (Fin 3) K := !![-1, 0, -1; 0, 0, -1; 2, -1, 1]

@[expose] def mTwo : Matrix (Fin 3) (Fin 3) K := !![-1, -1, 0; 2, 1, -1; 0, -1, 0]

@[expose] def uMat : Matrix (Fin 3) (Fin 3) K := !![1, 2, 0; 0, 1, 0; -4, -4, 1]

@[expose] def jZero : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, 0, 2; 0, 2, 0]

@[expose] def tauOne : SL(3, K) := ⟨mOne, by simp [mOne, Matrix.det_fin_three]⟩

@[expose] def tauTwo : SL(3, K) := ⟨mTwo, by simp [mTwo, Matrix.det_fin_three]⟩

theorem mOne_mul_mTwo : (mOne : Matrix (Fin 3) (Fin 3) K) * mTwo = uMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mOne, mTwo, uMat, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem tauOne_pow_three : (tauOne : SL(3, K)) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, pow_three]
  change (mOne : Matrix (Fin 3) (Fin 3) K) * (mOne * mOne) = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mOne, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem tauTwo_pow_three : (tauTwo : SL(3, K)) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, pow_three]
  change (mTwo : Matrix (Fin 3) (Fin 3) K) * (mTwo * mTwo) = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mTwo, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem mOne_jZero : (mOne : Matrix (Fin 3) (Fin 3) K) * jZero * mOneᵀ = jZero := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mOne, jZero, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals norm_num

theorem mTwo_jZero : (mTwo : Matrix (Fin 3) (Fin 3) K) * jZero * mTwoᵀ = jZero := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mTwo, jZero, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals norm_num

theorem not_common_eigenvector (hK2 : (2 : K) ≠ 0) {w : Fin 3 → K} (hw : w ≠ 0) {l m : K}
    (h1 : (mOne : Matrix (Fin 3) (Fin 3) K) *ᵥ w = l • w)
    (h2 : (mTwo : Matrix (Fin 3) (Fin 3) K) *ᵥ w = m • w) : False := by
  have hU : (uMat : Matrix (Fin 3) (Fin 3) K) *ᵥ w = (l * m) • w := by
    rw [← mOne_mul_mTwo, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, h1, smul_smul,
      mul_comm]
  have e0 := congrFun hU 0
  have e1 := congrFun hU 1
  have e2 := congrFun hU 2
  have f0 := congrFun h1 0
  simp [uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at e0 e1 e2
  simp [mOne, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at f0
  have hK4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero hK2 hK2
  have hw1 : w 1 = 0 := by
    by_contra h
    have hc : l * m = 1 := by
      have : (l * m - 1) * w 1 = 0 := by linear_combination -e1
      have := (mul_eq_zero.mp this).resolve_right h
      linear_combination this
    rw [hc] at e0
    exact h (by
      have : 2 * w 1 = 0 := by linear_combination e0
      exact (mul_eq_zero.mp this).resolve_left hK2)
  have hw0 : w 0 = 0 := by
    by_contra h
    rw [hw1] at e0
    have hc : l * m = 1 := by
      have : (l * m - 1) * w 0 = 0 := by linear_combination -e0
      have := (mul_eq_zero.mp this).resolve_right h
      linear_combination this
    rw [hc, hw1] at e2
    exact h (by
      have : 4 * w 0 = 0 := by linear_combination -e2
      exact (mul_eq_zero.mp this).resolve_left hK4)
  have hw2 : w 2 = 0 := by
    rw [hw0] at f0
    linear_combination -f0
  exact hw (funext fun i => by fin_cases i <;> simp [hw0, hw1, hw2])

@[expose] def eTwo : Fin 3 → K := Pi.single 2 1

theorem exists_inv_lift {y : projectiveSL 3 K} (hy2 : y ^ 2 = 1) :
    ∃ Y : SL(3, K), Y ^ 2 = 1 ∧ proj 3 K Y = y := by
  have hAe : IsElemAbelian 2 (Subgroup.zpowers y) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨m, rfl⟩⟩ := a
      obtain ⟨_, ⟨n, rfl⟩⟩ := b
      simp only [Subgroup.coe_mul]
      rw [← zpow_add, ← zpow_add, add_comm]
    · rintro _ ⟨m, rfl⟩
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy2, one_zpow]
  obtain ⟨Y, hY, hYy⟩ := CFSG.Quasithin.E22S.exists_invLift hAe (Subgroup.mem_zpowers y)
  exact ⟨Y, hY.2, hYy⟩

theorem not_commute_tau [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp3 : 3 < p)
    {y : projectiveSL 3 K} (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1)
    (h1 : proj 3 K tauOne * y = y * proj 3 K tauOne)
    (h2 : proj 3 K tauTwo * y = y * proj 3 K tauTwo) : False := by
  have hK2 : (2 : K) ≠ 0 := two_ne_zero_of_charP hp3
  obtain ⟨Y, hY2, rfl⟩ := exists_inv_lift hy2
  have hY1 : Y ≠ 1 := fun h => hy1 (by rw [h, map_one])
  obtain ⟨g, hg⟩ := exists_frame_sZero (by omega : p ≠ 2) hY2 hY1
  have hblock : ∀ Z : SL(3, K), proj 3 K Z * proj 3 K Y = proj 3 K Y * proj 3 K Z →
      ∃ c : K, (Z : Matrix (Fin 3) (Fin 3) K) *ᵥ ((g⁻¹ : SL(3, K)) *ᵥ (eTwo : Fin 3 → K)) =
        c • ((g⁻¹ : SL(3, K)) *ᵥ (eTwo : Fin 3 → K)) := by
    intro Z hZ
    have hc : Y * Z = Z * Y := CFSG.Quasithin.E22S.commute_of_proj_commute_two hY2 hZ.symm
    have hN : (g * Z * g⁻¹) * sZero = sZero * (g * Z * g⁻¹) := by
      rw [← hg]
      calc g * Z * g⁻¹ * (g * Y * g⁻¹) = g * (Z * Y) * g⁻¹ := by group
        _ = g * (Y * Z) * g⁻¹ := by rw [hc]
        _ = g * Y * g⁻¹ * (g * Z * g⁻¹) := by group
    obtain ⟨N, hNdef⟩ : ∃ N, N = ((g * Z * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) :=
      ⟨_, rfl⟩
    obtain ⟨h02, h12, -, -⟩ := isBlock_coe hK2 hN
    rw [← hNdef] at h02 h12
    refine ⟨N 2 2, ?_⟩
    have hNe : N *ᵥ (eTwo : Fin 3 → K) = N 2 2 • (eTwo : Fin 3 → K) := by
      ext i
      fin_cases i <;> simp [eTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h02, h12]
    have e : (Z : Matrix (Fin 3) (Fin 3) K) =
        ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * N * (g : Matrix (Fin 3) (Fin 3) K) := by
      rw [hNdef, ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
        show g⁻¹ * (g * Z * g⁻¹) * g = Z by group]
    calc (Z : Matrix (Fin 3) (Fin 3) K) *ᵥ ((g⁻¹ : SL(3, K)) *ᵥ (eTwo : Fin 3 → K))
        = (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * N * (g : Matrix (Fin 3) (Fin 3) K)) *ᵥ
            ((g⁻¹ : SL(3, K)) *ᵥ (eTwo : Fin 3 → K)) := by rw [e]
      _ = ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ (N *ᵥ
            (((g : Matrix (Fin 3) (Fin 3) K) * ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) *ᵥ
              (eTwo : Fin 3 → K))) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ (N *ᵥ (eTwo : Fin 3 → K)) := by
          rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
            Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
      _ = N 2 2 • ((g⁻¹ : SL(3, K)) *ᵥ (eTwo : Fin 3 → K)) := by
          rw [hNe, Matrix.mulVec_smul]
  obtain ⟨c₁, hc₁⟩ := hblock tauOne h1
  obtain ⟨c₂, hc₂⟩ := hblock tauTwo h2
  refine not_common_eigenvector hK2 ?_ hc₁ hc₂
  intro h0
  have := congrArg (fun v => (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v) h0
  simp only [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  have := congrFun this 2
  simp [eTwo] at this

theorem uMat_sub_one_pow_three : ((uMat : Matrix (Fin 3) (Fin 3) K) - 1) ^ 3 = 0 := by
  rw [pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]

theorem uMat_pow (n : ℕ) : (uMat : Matrix (Fin 3) (Fin 3) K) ^ n =
    1 + (n : K) • (uMat - 1) + ((n.choose 2 : ℕ) : K) • ((uMat - 1) * (uMat - 1)) := by
  set N := (uMat : Matrix (Fin 3) (Fin 3) K) - 1 with hN
  have hN3 : N * N * N = 0 := by
    have h := uMat_sub_one_pow_three (K := K)
    rw [pow_three, ← Matrix.mul_assoc] at h
    exact h
  have hU : (uMat : Matrix (Fin 3) (Fin 3) K) = 1 + N := by rw [hN]; abel
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, hU, Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      add_smul, one_smul, hN3, smul_zero, add_zero]
    abel

theorem uMat_pow_char {p : ℕ} [Fact p.Prime] [CharP K p] (hp3 : 3 ≤ p) :
    (uMat : Matrix (Fin 3) (Fin 3) K) ^ p = 1 := by
  rw [uMat_pow, CharP.cast_eq_zero, zero_smul, add_zero]
  have hdvd : p ∣ p.choose 2 := (Fact.out : p.Prime).dvd_choose_self (by norm_num) (by omega)
  rw [(CharP.cast_eq_zero_iff K p _).mpr hdvd, zero_smul, add_zero]

theorem uMat_ne_one (hK2 : (2 : K) ≠ 0) : (uMat : Matrix (Fin 3) (Fin 3) K) ≠ 1 := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [uMat] at this
  exact hK2 this

theorem not_commute_u_four [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp3 : 3 < p)
    {A : Subgroup (projectiveSL 3 K)} (hA : IsElemAbelian 2 A) {y₁ y₂ : projectiveSL 3 K}
    (hy₁ : y₁ ∈ A) (hy₂ : y₂ ∈ A) (h1 : y₁ ≠ 1) (h2 : y₂ ≠ 1) (h12 : y₁ ≠ y₂)
    (hc₁ : proj 3 K (tauOne * tauTwo) * y₁ = y₁ * proj 3 K (tauOne * tauTwo))
    (hc₂ : proj 3 K (tauOne * tauTwo) * y₂ = y₂ * proj 3 K (tauOne * tauTwo)) : False := by
  classical
  have hK2 : (2 : K) ≠ 0 := two_ne_zero_of_charP hp3
  have hne1 : (-1 : K) ≠ 1 := fun h => hK2 (by linear_combination -h)
  obtain ⟨g, hg⟩ := CFSG.Quasithin.E22S.exists_frame (by omega : p ≠ 2) hA
  obtain ⟨X₁, hX₁, rfl⟩ := CFSG.Quasithin.E22S.exists_invLift hA hy₁
  obtain ⟨X₂, hX₂, rfl⟩ := CFSG.Quasithin.E22S.exists_invLift hA hy₂
  have hd₁ := CFSG.Quasithin.E22S.conj_eq_diagonal (hg X₁ hX₁)
  have hd₂ := CFSG.Quasithin.E22S.conj_eq_diagonal (hg X₂ hX₂)
  set d₁ := CFSG.Quasithin.E22S.dg g X₁ with hd₁def
  set d₂ := CFSG.Quasithin.E22S.dg g X₂ with hd₂def
  have hs₁ : ∀ k, d₁ k = 1 ∨ d₁ k = -1 := fun k =>
    mul_self_eq_one_iff.mp (CFSG.Quasithin.E22S.dg_sq (hg X₁ hX₁) hX₁.2 k)
  have hs₂ : ∀ k, d₂ k = 1 ∨ d₂ k = -1 := fun k =>
    mul_self_eq_one_iff.mp (CFSG.Quasithin.E22S.dg_sq (hg X₂ hX₂) hX₂.2 k)
  have hp₁ := CFSG.Quasithin.E22S.dg_prod (hg X₁ hX₁)
  have hp₂ := CFSG.Quasithin.E22S.dg_prod (hg X₂ hX₂)
  rw [Fin.prod_univ_three] at hp₁ hp₂
  have hn₁ : ¬ ∀ k, d₁ k = 1 := fun h => h1 (by
    have : X₁ = 1 := CFSG.Quasithin.E22S.dg_inj (hg X₁ hX₁)
      (fun i j hij => by simp [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne hij])
      fun k => by rw [CFSG.Quasithin.E22S.dg_one]; exact h k
    rw [this, map_one])
  have hn₂ : ¬ ∀ k, d₂ k = 1 := fun h => h2 (by
    have : X₂ = 1 := CFSG.Quasithin.E22S.dg_inj (hg X₂ hX₂)
      (fun i j hij => by simp [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne hij])
      fun k => by rw [CFSG.Quasithin.E22S.dg_one]; exact h k
    rw [this, map_one])
  have hn₁₂ : ¬ ∀ k, d₁ k = d₂ k := fun h => h12 (by
    rw [CFSG.Quasithin.E22S.dg_inj (hg X₁ hX₁) (hg X₂ hX₂) h])
  have hU₁ := CFSG.Quasithin.E22S.commute_of_proj_commute_two hX₁.2 hc₁.symm
  have hU₂ := CFSG.Quasithin.E22S.commute_of_proj_commute_two hX₂.2 hc₂.symm
  obtain ⟨V, hVdef⟩ : ∃ V, V = ((g * (tauOne * tauTwo) * g⁻¹ : SL(3, K)) :
      Matrix (Fin 3) (Fin 3) K) := ⟨_, rfl⟩
  have hVc : ∀ (X : SL(3, K)), X * (tauOne * tauTwo) = (tauOne * tauTwo) * X →
      V * ((g * X * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
        ((g * X * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * V := by
    intro X hX
    rw [hVdef, ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul]
    congr 1
    calc g * (tauOne * tauTwo) * g⁻¹ * (g * X * g⁻¹) = g * ((tauOne * tauTwo) * X) * g⁻¹ := by
          group
      _ = g * (X * (tauOne * tauTwo)) * g⁻¹ := by rw [hX]
      _ = g * X * g⁻¹ * (g * (tauOne * tauTwo) * g⁻¹) := by group
  have hV₁ := hVc X₁ hU₁
  have hV₂ := hVc X₂ hU₂
  rw [hd₁] at hV₁
  rw [hd₂] at hV₂
  have hsep : ∀ k l : Fin 3, k ≠ l → d₁ k ≠ d₁ l ∨ d₂ k ≠ d₂ l := by
    intro k l hkl
    by_contra hc
    push Not at hc
    obtain ⟨hc1, hc2⟩ := hc
    obtain ⟨m, hmk, hml⟩ := CFSG.Quasithin.E22S.exists_third k l hkl
    have hd : ∀ d : Fin 3 → K, (∀ k, d k = 1 ∨ d k = -1) → d 0 * d 1 * d 2 = 1 →
        d k = d l → ¬ (∀ k, d k = 1) → d k = -1 ∧ d l = -1 ∧ d m = 1 := by
      intro d hs hp hkl' hn
      have hprod : d k * d l * d m = 1 := by
        rw [← CFSG.Quasithin.E22S.prod_three d hkl hmk.symm hml.symm, Fin.prod_univ_three, hp]
      rcases hs k with h | h
      · exfalso
        have hl' : d l = 1 := hkl' ▸ h
        have hm' : d m = 1 := by rw [h, hl', one_mul, one_mul] at hprod; exact hprod
        apply hn
        intro j
        rcases CFSG.Quasithin.E22S.cases_three hkl hmk.symm hml.symm j with hj | hj | hj
        · rw [hj]; exact h
        · rw [hj]; exact hl'
        · rw [hj]; exact hm'
      · have hl' : d l = -1 := hkl' ▸ h
        refine ⟨h, hl', ?_⟩
        rw [h, hl'] at hprod
        linear_combination hprod
    obtain ⟨a1, a2, a3⟩ := hd d₁ hs₁ hp₁ hc1 hn₁
    obtain ⟨b1, b2, b3⟩ := hd d₂ hs₂ hp₂ hc2 hn₂
    apply hn₁₂
    intro j
    rcases CFSG.Quasithin.E22S.cases_three hkl hmk.symm hml.symm j with hj | hj | hj
    · rw [hj, a1, b1]
    · rw [hj, a2, b2]
    · rw [hj, a3, b3]
  have hVdiag : ∀ k l : Fin 3, k ≠ l → V k l = 0 := by
    intro k l hkl
    rcases hsep k l hkl with h | h
    · exact Sec4.entry_eq_zero_of_commute_diagonal hV₁ h
    · exact Sec4.entry_eq_zero_of_commute_diagonal hV₂ h
  have hgg : ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) = 1 :=
    by rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have e : V - 1 = (g : Matrix (Fin 3) (Fin 3) K) * ((uMat : Matrix (Fin 3) (Fin 3) K) - 1) *
      ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
    rw [hVdef, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
    change (g : Matrix (Fin 3) (Fin 3) K) * (mOne * mTwo) *
      ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) - 1 = _
    rw [mOne_mul_mTwo, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hVN : (V - 1) ^ 3 = 0 := by
    rw [e]
    calc ((g : Matrix (Fin 3) (Fin 3) K) * ((uMat : Matrix (Fin 3) (Fin 3) K) - 1) *
          ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) ^ 3
        = (g : Matrix (Fin 3) (Fin 3) K) * ((uMat : Matrix (Fin 3) (Fin 3) K) - 1) *
          (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K)) *
          ((uMat : Matrix (Fin 3) (Fin 3) K) - 1) *
          (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K)) *
          ((uMat : Matrix (Fin 3) (Fin 3) K) - 1) *
          ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
          simp only [pow_three, Matrix.mul_assoc]
      _ = (g : Matrix (Fin 3) (Fin 3) K) * ((uMat : Matrix (Fin 3) (Fin 3) K) - 1) ^ 3 *
          ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
          rw [hgg]; simp only [Matrix.mul_one, pow_three, Matrix.mul_assoc]
      _ = 0 := by rw [uMat_sub_one_pow_three, Matrix.mul_zero, Matrix.zero_mul]
  have hVd : V = Matrix.diagonal fun k => V k k := by
    ext k l
    by_cases hkl : k = l
    · subst hkl; rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hkl, hVdiag k l hkl]
  have hV1 : V = 1 := by
    have h3 : (Matrix.diagonal fun k => (V k k - 1) ^ 3) = 0 := by
      have e3 : (V - 1) ^ 3 = Matrix.diagonal fun k => (V k k - 1) ^ 3 := by
        conv_lhs => rw [hVd]
        rw [← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.diagonal_pow]
        rfl
      rw [← e3, hVN]
    rw [hVd, ← Matrix.diagonal_one]
    congr 1
    funext k
    have := congrFun (congrFun h3 k) k
    rw [Matrix.diagonal_apply_eq, Matrix.zero_apply] at this
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)
  apply uMat_ne_one hK2
  have h4 : g * (tauOne * tauTwo) * g⁻¹ = 1 := Subtype.ext (by
    rw [← hVdef, hV1, Matrix.SpecialLinearGroup.coe_one])
  have h5 : (tauOne : SL(3, K)) * tauTwo = 1 := by
    calc (tauOne : SL(3, K)) * tauTwo = g⁻¹ * (g * (tauOne * tauTwo) * g⁻¹) * g := by group
      _ = 1 := by rw [h4]; group
  rw [← mOne_mul_mTwo]
  have := congrArg (fun X : SL(3, K) => (X : Matrix (Fin 3) (Fin 3) K)) h5
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at this
  exact this

end Tau

end Item211Res6Proof

end CFSG.RankThree.PartTwo.Sec21
