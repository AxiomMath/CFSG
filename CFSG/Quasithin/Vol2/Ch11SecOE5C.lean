module

public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartOne.HNB.F25

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
