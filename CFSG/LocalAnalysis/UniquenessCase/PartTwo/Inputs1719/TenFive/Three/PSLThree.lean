module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.PSLThreeComp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Map
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedInner
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphTools
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWSymForm
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open Matrix Module
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL proj conjAut fieldAut dualAut)
open CFSG.HardMathSupport.Seitz.TrialityOdd.Inner (sym2Form)

private lemma isGenGood_conjAut_of_diag {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 3) (B : GL (Fin 3) K) (hB2 : B * B = 1)
    (hB1 : conjAut 3 K B ≠ 1)
    (h2k : 2 ≤ finrank K (LinearMap.ker (toLin' (B : Matrix (Fin 3) (Fin 3) K) - 1))) :
    IsGenGood (conjAut 3 K B) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CharP K 3 :=
    charP_of_card_eq_prime (p := 3) (by rw [Fintype.card_eq_nat_card]; exact hK)
  have hring : ringChar K ≠ 2 := by
    rw [ringChar.eq_iff.mpr hchar]; norm_num
  have hBm : (B : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, hB2, Units.val_one]
  have hsum : finrank K (LinearMap.ker (toLin' (B : Matrix (Fin 3) (Fin 3) K) - 1)) +
      finrank K (LinearMap.ker (toLin' (B : Matrix (Fin 3) (Fin 3) K) + 1)) = 3 := by
    rw [Submodule.finrank_add_eq_of_isCompl
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.isCompl_eigenspaces hring hBm),
      finrank_fin_fun]
  obtain ⟨b, hb⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_eigenbasis hring hBm
  obtain ⟨P, D, hPD, hD⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_gl_inv_mul_mul_eq_toMatrix b B
  set d : Fin 3 → K := fun i =>
    if (i : ℕ) < finrank K (LinearMap.ker (toLin' (B : Matrix (Fin 3) (Fin 3) K) - 1))
    then 1 else -1 with hd
  have hDd : (D : Matrix (Fin 3) (Fin 3) K) = diagonal d := by
    rw [hD]
    ext a c
    rw [LinearMap.toMatrix_apply, toLin'_apply, hb c, map_smul, Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply, diagonal_apply]
    by_cases hac : a = c
    · subst hac; simp [hd]
    · simp [hac, Ne.symm hac]
  have hBPD : B = P * D * P⁻¹ := by rw [← hPD]; group
  have hk23 : finrank K (LinearMap.ker (toLin' (B : Matrix (Fin 3) (Fin 3) K) - 1)) = 2 ∨
      finrank K (LinearMap.ker (toLin' (B : Matrix (Fin 3) (Fin 3) K) - 1)) = 3 := by
    omega
  rcases hk23 with hk2 | hk3
  · have hd2 : d = ![1, 1, -1] := by
      rw [hd, hk2]
      funext i
      fin_cases i <;> simp
    have hD2 : (D : Matrix (Fin 3) (Fin 3) K) = diagonal ![1, 1, -1] := by
      rw [hDd, hd2]
    have hconj : conjAut 3 K B =
        conjAut 3 K P * conjAut 3 K D * (conjAut 3 K P)⁻¹ := by
      rw [hBPD, map_mul, map_mul, map_inv]
    exact IsGenGood.conj hconj (isGenGood_conjAut_diag_three hK D hD2)
  · exfalso
    have hd3 : d = fun _ => (1 : K) := by
      rw [hd, hk3]
      funext i; simp
    have hD1 : (D : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [hDd, hd3]; simp
    have hDgl : D = 1 := Units.ext hD1
    have hB1' : B = 1 := by rw [hBPD, hDgl]; group
    exact hB1 (by rw [hB1', map_one])

private lemma isGenGood_conjAut_of_sq_one {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 3) (A : GL (Fin 3) K) (h2 : conjAut 3 K A ^ 2 = 1)
    (h1 : conjAut 3 K A ≠ 1) : IsGenGood (conjAut 3 K A) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CharP K 3 :=
    charP_of_card_eq_prime (p := 3) (by rw [Fintype.card_eq_nat_card]; exact hK)
  have hring : ringChar K ≠ 2 := by
    rw [ringChar.eq_iff.mpr hchar]; norm_num
  have hAA1 : conjAut 3 K (A * A) = 1 := by rw [map_mul, ← pow_two, h2]
  obtain ⟨-, c, hc⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one
      (le_refl 3) (A * A) 1 (by rw [hAA1, map_one, mul_one])
  have hA2 : (A : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) =
      (c : K) • 1 := by
    rw [← Units.val_mul, ← hc, GeneralLinearGroup.coe_scalar, smul_one_eq_diagonal]
    rfl
  have hc0 : (c : K) ≠ 0 := Units.ne_zero c
  have hdet0 : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
    (Matrix.isUnits_det_units A).ne_zero
  have hcard : Fintype.card K - 1 = 2 := by rw [Fintype.card_eq_nat_card, hK]
  have hdet2 : (A : Matrix (Fin 3) (Fin 3) K).det ^ 2 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one
      (A : Matrix (Fin 3) (Fin 3) K).det hdet0
    rwa [hcard] at h
  have hc3 : (c : K) ^ 3 = 1 := by
    have h := congrArg Matrix.det hA2
    rw [Matrix.det_mul, Matrix.det_smul] at h
    simp only [Fintype.card_fin, Matrix.det_one, mul_one] at h
    rw [← pow_two] at h
    exact h.symm.trans hdet2
  have hc2 : (c : K) ^ 2 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one (c : K) hc0
    rwa [hcard] at h
  have hc1 : (c : K) = 1 := by
    calc (c : K) = (c : K) * (c : K) ^ 2 := by rw [hc2, mul_one]
      _ = (c : K) ^ 3 := by ring
      _ = 1 := hc3
  have hA2gl : A * A = 1 := by
    apply Units.ext
    rw [Units.val_mul, hA2, hc1, one_smul, Units.val_one]
  have hAm : (A : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, hA2gl, Units.val_one]
  have hsum : finrank K (LinearMap.ker (toLin' (A : Matrix (Fin 3) (Fin 3) K) - 1)) +
      finrank K (LinearMap.ker (toLin' (A : Matrix (Fin 3) (Fin 3) K) + 1)) = 3 := by
    rw [Submodule.finrank_add_eq_of_isCompl
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.isCompl_eigenspaces hring hAm),
      finrank_fin_fun]
  by_cases h2k : 2 ≤ finrank K (LinearMap.ker (toLin' (A : Matrix (Fin 3) (Fin 3) K) - 1))
  · exact isGenGood_conjAut_of_diag hK A hA2gl h1 h2k
  · have hker : LinearMap.ker (toLin' ((-A : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) - 1) =
        LinearMap.ker (toLin' (A : Matrix (Fin 3) (Fin 3) K) + 1) := by
      ext v
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply, toLin'_apply,
        Module.End.one_apply, Units.val_neg, neg_mulVec]
      rw [← neg_add', neg_eq_zero]
    have h2k' : 2 ≤ finrank K (LinearMap.ker (toLin' ((-A : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) - 1)) := by
      rw [hker]; omega
    have hneg : (-A) * (-A) = 1 := by rw [neg_mul_neg, hA2gl]
    have h1neg : conjAut 3 K (-A) ≠ 1 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_neg]; exact h1
    have hg := isGenGood_conjAut_of_diag hK (-A) hneg h1neg h2k'
    rwa [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_neg] at hg

private lemma isGenGood_conjAut_dualAut_of_sq_one {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 3) (A : GL (Fin 3) K)
    (h2 : (conjAut 3 K A * dualAut 3 K) ^ 2 = 1) :
    IsGenGood (conjAut 3 K A * dualAut 3 K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CharP K 3 :=
    charP_of_card_eq_prime (p := 3) (by rw [Fintype.card_eq_nat_card]; exact hK)
  have h2K : (2 : K) ≠ 0 := by
    intro h
    have hdvd : 3 ∣ 2 := (CharP.cast_eq_zero_iff K 3 2).mp h
    omega
  have hdet : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
    (Matrix.isUnits_det_units A).ne_zero
  rcases CFSG.LocalAnalysis.ComponentInitial.LinearFlag.transpose_eq_or_eq_neg_of_sq_conjAut_dualAut
    (le_refl 3) A h2 with hA | hA
  · obtain ⟨P, c, hc⟩ :=
      CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.exists_sym_form_equiv h2K
        (A : Matrix (Fin 3) (Fin 3) K) hA hdet
    have hdetS : (sym2Form K).det ≠ 0 := by
      rw [sym2Form, Matrix.det_fin_three]
      norm_num
      exact h2K
    set S : GL (Fin 3) K :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero (sym2Form K) hdetS with hSdef
    have hS : (S : Matrix (Fin 3) (Fin 3) K) = sym2Form K := by
      rw [hSdef, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    set PT : GL (Fin 3) K := Matrix.GeneralLinearGroup.inverseTranspose P⁻¹ with hPTdef
    have hPT : (PT : Matrix (Fin 3) (Fin 3) K) = (P : Matrix (Fin 3) (Fin 3) K)ᵀ := by
      rw [hPTdef, Matrix.GeneralLinearGroup.coe_inverseTranspose, inv_inv]
    have hAgl : A = GeneralLinearGroup.scalar (Fin 3) c * P * S * PT := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.val_mul, hPT, GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, hS, hc, ← Matrix.smul_eq_diagonal_mul, Matrix.smul_mul,
        Matrix.smul_mul]
    have hcA : conjAut 3 K A = conjAut 3 K P * conjAut 3 K S * conjAut 3 K PT := by
      rw [hAgl, map_mul, map_mul, map_mul,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_scalar, one_mul]
    have hdual : conjAut 3 K PT * dualAut 3 K = dualAut 3 K * conjAut 3 K P⁻¹ := by
      rw [hPTdef, ← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut_mul_conjAut (P⁻¹)]
    have hf1 : fieldAut 3 K (1 : K ≃+* K) = 1 := map_one _
    have hconj : conjAut 3 K A * dualAut 3 K =
        conjAut 3 K P * (conjAut 3 K S * fieldAut 3 K 1 * dualAut 3 K) *
          (conjAut 3 K P)⁻¹ := by
      calc conjAut 3 K A * dualAut 3 K
          = (conjAut 3 K P * conjAut 3 K S * conjAut 3 K PT) * dualAut 3 K := by rw [hcA]
        _ = conjAut 3 K P * conjAut 3 K S * (conjAut 3 K PT * dualAut 3 K) := by group
        _ = conjAut 3 K P * conjAut 3 K S * (dualAut 3 K * conjAut 3 K P⁻¹) := by rw [hdual]
        _ = conjAut 3 K P * (conjAut 3 K S * fieldAut 3 K 1 * dualAut 3 K) *
              (conjAut 3 K P)⁻¹ := by rw [hf1, map_inv]; group
    exact IsGenGood.conj hconj (isGenGood_conjAut_sym2Form_dualAut_three hK S hS)
  · exfalso
    have h := congrArg Matrix.det hA
    rw [Matrix.det_transpose, Matrix.det_neg] at h
    have h2' : (2 : K) * (A : Matrix (Fin 3) (Fin 3) K).det = 0 := by
      simp at h
      linear_combination h
    exact hdet ((mul_eq_zero.mp h2').resolve_left h2K)

theorem involGen_projectiveSL_three_three {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 3) : InvolGen (projectiveSL 3 K) := by
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
  obtain ⟨A, σ, ε, hε, hstd⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_std_of_mulEquiv (le_refl 3) (MulEquiv.refl _) α
  have hαeq : α = conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K ^ ε := by
    rw [← hstd]
    ext x
    simp [MulAut.congr_apply]
  have hσ1 : σ = 1 := ringEquiv_eq_one_of_card_three hK σ
  subst hσ1
  have hf1 : fieldAut 3 K (1 : K ≃+* K) = 1 := map_one _
  rw [hf1] at hαeq
  have hε01 : ε = 0 ∨ ε = 1 := by omega
  rcases hε01 with rfl | rfl
  · simp only [pow_zero, mul_one] at hαeq
    have h2 : conjAut 3 K A ^ 2 = 1 := by
      rw [hαeq] at hα2
      simpa using hα2
    have h1 : conjAut 3 K A ≠ 1 := by
      rw [hαeq] at hα1
      exact hα1
    rw [hαeq]
    exact isGenGood_conjAut_of_sq_one hK A h2 h1
  · simp only [pow_one, mul_one] at hαeq
    have h2 : (conjAut 3 K A * dualAut 3 K) ^ 2 = 1 := by
      rw [hαeq] at hα2
      simpa using hα2
    rw [hαeq]
    exact isGenGood_conjAut_dualAut_of_sq_one hK A h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
