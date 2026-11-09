module

public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartOne.HNB.F25

section

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.OE5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups CFSG.RankThree.Classical CFSG.RankThree.PartOne.HNB

theorem card_su35 {K : Type} [Field K] (h : UnitaryFieldData 5 1 K) :
    Nat.card (unitarySU 5 1 K 3) = 378000 := by
  have hBs := gramForm_isSymm h (G := (1 : Matrix (Fin 3) (Fin 3) K)) (by
    rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one])
  have hBl := gramForm_separatingLeft h (G := (1 : Matrix (Fin 3) (Fin 3) K)) (by simp)
  have hSint : (Nat.card (unitarySU 5 1 K 3) : ℤ) = ((5 ^ 1 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
      ∏ j ∈ Finset.Icc 2 3, (((5 ^ 1 : ℕ) : ℤ) ^ j - (-1) ^ j) := by
    rw [unitarySU_eq_gramSU h, card_gramSU]
    exact (unitary_full_group_order h hBs hBl (Module.finrank_fin_fun K) (by norm_num)).2.1
  have : (Nat.card (unitarySU 5 1 K 3) : ℤ) = 378000 := by
    rw [hSint]
    decide
  exact_mod_cast this

theorem hF25 : UnitaryFieldData 5 1 F25 := ⟨Nat.prime_five, le_rfl, by rw [F25.card]; norm_num⟩

@[expose] def cc : F25 := ((0 : ZMod 5), (1 : ZMod 5))

@[expose] def aMat : Matrix (Fin 3) (Fin 3) F25 := !![-cc, cc, 0; -cc, -cc, 0; 0, 0, -1]

@[expose] def wMat : Matrix (Fin 3) (Fin 3) F25 := diagonal ![1, -1, -1]

theorem aMat_det : aMat.det = 1 := by
  rw [Matrix.det_fin_three]
  decide +kernel

theorem aMat_unitary : (aMat.map (· ^ (5 ^ 1)))ᵀ * aMat = 1 := by
  decide +kernel

theorem wMat_det : wMat.det = 1 := by
  rw [Matrix.det_fin_three]
  decide +kernel

theorem wMat_unitary : (wMat.map (· ^ (5 ^ 1)))ᵀ * wMat = 1 := by
  decide +kernel

theorem aMat_pow_four : aMat * aMat * aMat * aMat = negNegOneDiag F25 := by
  decide +kernel

theorem wMat_sq : wMat * wMat = 1 := by
  decide +kernel

theorem wMat_conj : wMat * aMat * wMat = aMat * aMat * aMat := by
  decide +kernel

theorem negNegOneDiag_ne_one : negNegOneDiag F25 ≠ 1 := by
  decide +kernel

@[expose] noncomputable def aU : unitarySU 5 1 F25 3 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero aMat (by rw [aMat_det]; exact one_ne_zero),
    Subgroup.subset_closure ⟨by simpa using aMat_det, by simpa using aMat_unitary⟩⟩

@[expose] noncomputable def wU : unitarySU 5 1 F25 3 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero wMat (by rw [wMat_det]; exact one_ne_zero),
    Subgroup.subset_closure ⟨by simpa using wMat_det, by simpa using wMat_unitary⟩⟩

theorem mat_aU : mat aU = aMat := rfl

theorem mat_wU : mat wU = wMat := rfl

theorem mat_mul (x y : unitarySU 5 1 F25 3) : mat (x * y) = mat x * mat y := rfl

theorem mat_injective : Function.Injective (mat : unitarySU 5 1 F25 3 → _) :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem aU_pow_four : aU ^ 4 = unitaryInvT hF25 := by
  rw [show aU ^ 4 = aU * aU * aU * aU by rw [pow_succ, pow_succ, pow_succ, pow_one]]
  apply mat_injective
  rw [mat_mul, mat_mul, mat_mul, mat_aU, aMat_pow_four]
  rfl

theorem wU_sq : wU * wU = 1 := mat_injective (by rw [mat_mul, mat_wU, wMat_sq]; rfl)

theorem wU_conj : wU * aU * wU⁻¹ = aU ^ 3 := by
  have hw : wU⁻¹ = wU := inv_eq_of_mul_eq_one_right wU_sq
  rw [hw, show aU ^ 3 = aU * aU * aU by rw [pow_succ, pow_succ, pow_one]]
  apply mat_injective
  rw [mat_mul, mat_mul, mat_mul, mat_mul, mat_aU, mat_wU, wMat_conj]

theorem invT_ne_one : unitaryInvT hF25 ≠ 1 := fun h =>
  negNegOneDiag_ne_one (by rw [← coe_unitaryInvT hF25, h]; rfl)

theorem orderOf_aU : orderOf aU = 8 := by
  have h1 : ¬ aU ^ 2 ^ 2 = 1 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, aU_pow_four]
    exact invT_ne_one
  have h2 : aU ^ 2 ^ (2 + 1) = 1 := by
    rw [show (2 : ℕ) ^ (2 + 1) = 4 * 2 by norm_num, pow_mul, aU_pow_four, ← orderOf_invT hF25,
      pow_orderOf_eq_one]
  rw [orderOf_eq_prime_pow h1 h2]
  norm_num

end CFSG.Quasithin.Vol2.Ch11.SecS.OE5

end

end

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.OE5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups CFSG.RankThree.Classical CFSG.RankThree.PartOne.HNB

theorem two_ne_zero_F25 : (2 : F25) ≠ 0 := by decide +kernel

theorem cc_ne_zero : cc ≠ 0 := by decide +kernel

theorem eq_one_or_neg_one : ∀ x : F25, x ^ 5 * x = 1 → x ^ 16 = 1 → x = 1 ∨ x = -1 := by
  decide +kernel

theorem eq_of_commute {g : unitarySU 5 1 F25 3} (ha : g * aU = aU * g) (hw : g * wU = wU * g)
    (h16 : g ^ 16 = 1) : g = 1 ∨ g = unitaryInvT hF25 := by
  have ht : g * unitaryInvT hF25 = unitaryInvT hF25 * g := by
    rw [← aU_pow_four]
    exact (Commute.pow_right ha 4).eq
  have hT := congrArg mat ht
  rw [mat_mul, mat_mul] at hT
  obtain ⟨h02, h12, h20, h21⟩ := entries_of_commute two_ne_zero_F25 hT
  have hW := congrArg mat hw
  rw [mat_mul, mat_mul, mat_wU] at hW
  have e : ∀ i j, mat g i j * ![(1 : F25), -1, -1] j = ![(1 : F25), -1, -1] i * mat g i j :=
    fun i j => by
      have := congrFun (congrFun hW i) j
      simpa [wMat, mul_diagonal, diagonal_mul] using this
  have h01 : mat g 0 1 = 0 := by
    have e01 : -mat g 0 1 = mat g 0 1 := by simpa using e 0 1
    have h2 : (2 : F25) * mat g 0 1 = 0 := by linear_combination -e01
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero_F25
  have h10 : mat g 1 0 = 0 := by
    have e10 : mat g 1 0 = -mat g 1 0 := by simpa using e 1 0
    have h2 : (2 : F25) * mat g 1 0 = 0 := by linear_combination e10
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero_F25
  have hA := congrArg mat ha
  rw [mat_mul, mat_mul, mat_aU] at hA
  have e01 := congrFun (congrFun hA 0) 1
  simp only [mul_apply, Fin.sum_univ_three, aMat, of_apply, cons_val', cons_val_zero,
    cons_val_one, cons_val_two, empty_val', cons_val_fin_one, head_cons, tail_cons, head_fin_const,
    h01, h21, h02] at e01
  have h11 : mat g 1 1 = mat g 0 0 := by
    have h1 : cc * (mat g 1 1 - mat g 0 0) = 0 := by linear_combination -e01
    exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left cc_ne_zero)
  have hmem := (mem_unitarySU_iff hF25).mp g.2
  have hu00 := congrFun (congrFun hmem.2 0) 0
  have hu22 := congrFun (congrFun hmem.2 2) 2
  simp only [mul_apply, transpose_apply, map_apply, Fin.sum_univ_three, h10, h20, h02, h12,
    one_apply_eq, map_zero, zero_mul, add_zero, zero_add] at hu00 hu22
  rw [UnitaryFieldData.bar_apply] at hu00 hu22
  have hdet := hmem.1
  rw [det_eq_block h02 h12 h20 h21, det_fin_two] at hdet
  simp only [block, of_apply, Fin.castSucc_zero, Fin.castSucc_one, h01, h10, mul_zero,
    sub_zero, h11] at hdet
  have hdiag : mat g = diagonal ![mat g 0 0, mat g 0 0, mat g 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h12, h20, h21, h11]
  have h16' : (mat g) ^ 16 = 1 := by
    have := congrArg mat h16
    rwa [show mat (g ^ 16) = (mat g) ^ 16 by simp [mat]] at this
  rw [hdiag, diagonal_pow] at h16'
  have h0 : mat g 0 0 ^ 16 = 1 := by
    have := congrFun (congrFun h16' 0) 0
    simpa using this
  have h22 : mat g 2 2 = 1 := by
    rcases eq_one_or_neg_one _ (by simpa using hu00) h0 with h | h
    · rw [h] at hdet
      simpa using hdet
    · rw [h] at hdet
      simpa using hdet
  rcases eq_one_or_neg_one _ (by simpa using hu00) h0 with h | h
  · left
    apply mat_injective
    rw [hdiag, h, h22]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · right
    apply mat_injective
    rw [hdiag, h, h22]
    show _ = negNegOneDiag F25
    rfl

@[expose] noncomputable def S0 : Subgroup (unitarySU 5 1 F25 3) :=
  Subgroup.zpowers aU ⊔ Subgroup.zpowers wU

theorem wU_inv : wU⁻¹ = wU := inv_eq_of_mul_eq_one_right wU_sq

theorem wU_ne_one : wU ≠ 1 := fun h => by
  have h1 : mat wU 1 1 = mat (1 : unitarySU 5 1 F25 3) 1 1 := by rw [h]
  rw [mat_wU] at h1
  exact absurd h1 (by decide +kernel)

theorem orderOf_wU : orderOf wU = 2 := orderOf_eq_prime (by rw [sq, wU_sq]) wU_ne_one

theorem conj_zpow_aU (k : ℤ) : wU * aU ^ k * wU⁻¹ = (aU ^ 3) ^ k := by
  rw [← wU_conj, ← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]

theorem zpow_mem_zpowers_aU (k : ℤ) : (aU ^ 3) ^ k ∈ Subgroup.zpowers aU :=
  Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers aU) 3) k

theorem wU_mem_normalizer : wU ∈ Subgroup.normalizer (Subgroup.zpowers aU : Set _) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨k, rfl⟩
    rw [conj_zpow_aU]
    exact zpow_mem_zpowers_aU k
  · rintro ⟨k, hk⟩
    have hx : x = wU * (wU * x * wU⁻¹) * wU⁻¹ := by
      rw [wU_inv, ← mul_assoc, ← mul_assoc, wU_sq, one_mul, mul_assoc, wU_sq, mul_one]
    rw [hx, ← hk, conj_zpow_aU]
    exact zpow_mem_zpowers_aU k

theorem isPGroup_S0 : IsPGroup 2 S0 := by
  have ha : IsPGroup 2 (Subgroup.zpowers aU) :=
    IsPGroup.of_card (n := 3) (by rw [Nat.card_zpowers, orderOf_aU]; norm_num)
  have hw : IsPGroup 2 (Subgroup.zpowers wU) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_wU]; norm_num)
  have := IsPGroup.to_sup_of_normal_right' hw ha (Subgroup.zpowers_le.mpr wU_mem_normalizer)
  rw [sup_comm] at this
  exact this

theorem wU_not_mem : wU ∉ Subgroup.zpowers aU := by
  intro hw
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hw
  have h1 : wU * aU * wU⁻¹ = aU := by
    rw [← hm]
    have : aU ^ m * aU = aU * aU ^ m := (Commute.zpow_left (Commute.refl aU) m).eq
    rw [this, mul_inv_cancel_right]
  rw [wU_conj] at h1
  have h2 : aU ^ 2 = 1 := by
    have : aU ^ 3 = aU ^ 2 * aU := by rw [pow_succ]
    rw [this] at h1
    simpa using h1
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [orderOf_aU] at h3
  norm_num at h3

theorem card_S0 : Nat.card S0 = 16 := by
  obtain ⟨k, hk⟩ := isPGroup_S0.exists_card_eq
  have h8 : 8 ∣ Nat.card S0 := by
    rw [← orderOf_aU, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le le_sup_left
  have hne : Nat.card S0 ≠ 8 := by
    intro h
    have heq : Subgroup.zpowers aU = S0 :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, Nat.card_zpowers, orderOf_aU])
    exact wU_not_mem (heq ▸ (le_sup_right : Subgroup.zpowers wU ≤ S0) (Subgroup.mem_zpowers wU))
  have hdvd : Nat.card S0 ∣ 378000 := by
    rw [← card_su35 hF25]
    exact Subgroup.card_subgroup_dvd_card S0
  rw [hk] at h8 hne hdvd ⊢
  have hk4 : k ≤ 4 := by
    by_contra hk5
    have := (Nat.pow_dvd_pow 2 (show 5 ≤ k by omega)).trans hdvd
    norm_num at this
  interval_cases k <;> omega

end CFSG.Quasithin.Vol2.Ch11.SecS.OE5
