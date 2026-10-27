module

public import CFSG.Monster.Xi.Defs
public import CFSG.Monster.Xi.GreyIdentities
public import CFSG.Monster.Spin.DyadicNormalizer
import CFSG.Monster.FourierTriality
public import CFSG.Monster.Spin.FourierPauli

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Xi

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin Matrix

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

private theorem add_self_fin6 (μ : Fin 6 → ZMod 2) : μ + μ = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  exact zmod2_add_self _

private theorem add_add_cancel_fin6 (μ κ : Fin 6 → ZMod 2) : μ + (μ + κ) = κ := by
  rw [← add_assoc, add_self_fin6, zero_add]

private theorem add_add_cancel_fin6' (ν μ : Fin 6 → ZMod 2) : ν + μ + μ = ν := by
  rw [add_assoc, add_self_fin6, add_zero]

private theorem sum_add_right' {M : Type*} [AddCommMonoid M] (f : (Fin 6 → ZMod 2) → M)
    (μ : Fin 6 → ZMod 2) : ∑ ν, f (ν + μ) = ∑ ν, f ν :=
  Equiv.sum_comp (Equiv.addRight μ) f

private theorem sum_add_left' {M : Type*} [AddCommMonoid M] (f : (Fin 6 → ZMod 2) → M)
    (μ : Fin 6 → ZMod 2) : ∑ ν, f (μ + ν) = ∑ ν, f ν :=
  Equiv.sum_comp (Equiv.addLeft μ) f

theorem zmat_pow_val (t : ZMod 2) : zmat ^ t.val = sgn t • (1 : Matrix SpinIdx SpinIdx ℚ) := by
  have : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases this t with rfl | rfl
  · rw [ZMod.val_zero, pow_zero, sgn_zero, one_smul]
  · rw [ZMod.val_one, pow_one, zmat, show sgn 1 = -1 from rfl, neg_one_smul]

theorem Dmat_mul_Tmat_eq (δ : Cocode) (a : C) :
    Dmat δ * Tmat a = sgn (pair a δ) • (Tmat a * Dmat δ) := by
  rw [Dmat_mul_Tmat, zmat_pow_val, Matrix.smul_mul, Matrix.one_mul]

@[simp] theorem Tmat_zero : Tmat 0 = 1 := by
  rw [Tmat_eq_qmatR, qmatR_zero]

@[simp] theorem Dmat_zero : Dmat 0 = 1 := by
  rw [Dmat_eq_qmatR, qmatR_zero]

theorem Tmat_comm (a b : C) : Tmat a * Tmat b = Tmat b * Tmat a := by
  rw [Tmat_mul_Tmat, Tmat_mul_Tmat, add_comm]

theorem Dmat_comm (δ ε : Cocode) : Dmat δ * Dmat ε = Dmat ε * Dmat δ := by
  rw [Dmat_mul_Dmat, Dmat_mul_Dmat, add_comm]

theorem Tmat_mul_self (a : C) : Tmat a * Tmat a = 1 := by
  rw [Tmat_mul_Tmat, add_self_C', Tmat_zero]

theorem Dmat_mul_self (δ : Cocode) : Dmat δ * Dmat δ = 1 := by
  rw [Dmat_mul_Dmat, add_self_cocode, Dmat_zero]

theorem Tmat_transpose (a : C) : (Tmat a)ᵀ = Tmat a := by
  rw [Tmat_eq_qmatR, qmatR_transpose, pair_zero_right, add_zero]

theorem Dmat_transpose (δ : Cocode) : (Dmat δ)ᵀ = Dmat δ := by
  rw [Dmat_eq_qmatR, qmatR_transpose, pair_zero_left, add_zero]

theorem Dg_mul_Tg (μ ν : Fin 6 → ZMod 2) :
    Dmat (gammaD ν) * Tmat (greyC μ) = sgn (bG μ ν) • (Tmat (greyC μ) * Dmat (gammaD ν)) := by
  rw [Dmat_mul_Tmat_eq, pair_greyC_gammaD]

theorem Dg_mul_TH (ν : Fin 6 → ZMod 2) {h : C} (hh : (h : Fin 24 → ZMod 2) ∈ H) :
    Dmat (gammaD ν) * Tmat h = Tmat h * Dmat (gammaD ν) := by
  rw [Dmat_mul_Tmat_eq, pair_H_gammaD hh, sgn_zero, one_smul]

theorem DHstar_mul_Tg {η : Cocode} (hη : η ∈ Hstar) (μ : Fin 6 → ZMod 2) :
    Dmat η * Tmat (greyC μ) = Tmat (greyC μ) * Dmat η := by
  rw [Dmat_mul_Tmat_eq, mem_Hstar_iff.1 hη μ, sgn_zero, one_smul]

private theorem sum_sgn_qG_mul_aux : ∀ κ : Fin 6 → ZMod 2,
    ∑ ν : Fin 6 → ZMod 2, sgn (qG ν) * sgn (qG (ν + κ)) = if κ = 0 then 64 else 0 := by
  decide +kernel

theorem sum_sgn_qG_mul (κ : Fin 6 → ZMod 2) :
    ∑ ν : Fin 6 → ZMod 2, sgn (qG ν) * sgn (qG (ν + κ)) = if κ = 0 then 64 else 0 :=
  sum_sgn_qG_mul_aux κ

theorem sum_sum_sgn_qG {V : Type*} [AddCommGroup V] [Module ℚ V]
    (X : (Fin 6 → ZMod 2) → V) :
    ∑ μ : Fin 6 → ZMod 2, ∑ ν : Fin 6 → ZMod 2, (sgn (qG μ) * sgn (qG ν)) • X (μ + ν) =
      (64 : ℚ) • X 0 := by
  have h1 : ∀ μ : Fin 6 → ZMod 2, ∑ ν : Fin 6 → ZMod 2, (sgn (qG μ) * sgn (qG ν)) • X (μ + ν) =
      ∑ κ : Fin 6 → ZMod 2, (sgn (qG μ) * sgn (qG (μ + κ))) • X κ := by
    intro μ
    rw [← sum_add_left' (fun ν => (sgn (qG μ) * sgn (qG ν)) • X (μ + ν)) μ]
    simp only [add_add_cancel_fin6]
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, sum_sgn_qG_mul, ite_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem XiGamma_transpose : XiGammaᵀ = XiGamma := by
  rw [XiGamma, transpose_smul, transpose_sum]
  simp only [transpose_smul, Dmat_transpose]

theorem XiG_transpose : XiGᵀ = XiG := by
  rw [XiG, transpose_smul, transpose_sum]
  simp only [transpose_smul, Tmat_transpose]

private theorem avg_mul_avg (F F' : (Fin 6 → ZMod 2) → Matrix SpinIdx SpinIdx ℚ) :
    ((1 / 8 : ℚ) • ∑ μ : Fin 6 → ZMod 2, sgn (qG μ) • F μ) *
        ((1 / 8 : ℚ) • ∑ ν : Fin 6 → ZMod 2, sgn (qG ν) • F' ν) =
      (1 / 64 : ℚ) • ∑ μ : Fin 6 → ZMod 2, ∑ ν : Fin 6 → ZMod 2,
        (sgn (qG μ) * sgn (qG ν)) • (F μ * F' ν) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Finset.sum_mul]
  simp only [Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num [mul_comm]

theorem XiGamma_mul_self : XiGamma * XiGamma = 1 := by
  rw [XiGamma, avg_mul_avg]
  simp only [Dmat_mul_Dmat, ← map_add]
  rw [sum_sum_sgn_qG (fun κ => Dmat (gammaD κ)), map_zero, Dmat_zero, smul_smul]
  norm_num

theorem XiG_mul_self : XiG * XiG = 1 := by
  rw [XiG, avg_mul_avg]
  simp only [Tmat_mul_Tmat, ← map_add]
  rw [sum_sum_sgn_qG (fun κ => Tmat (greyC κ)), map_zero, Tmat_zero, smul_smul]
  norm_num

theorem XiGamma_transpose_mul_self : XiGammaᵀ * XiGamma = 1 := by
  rw [XiGamma_transpose, XiGamma_mul_self]

theorem XiG_transpose_mul_self : XiGᵀ * XiG = 1 := by
  rw [XiG_transpose, XiG_mul_self]

theorem Tg_mul_XiGamma (μ : Fin 6 → ZMod 2) :
    Tmat (greyC μ) * XiGamma =
      XiGamma * (sgn (qG μ) • (Tmat (greyC μ) * Dmat (gammaD μ))) := by
  have hL : ∀ ν : Fin 6 → ZMod 2, Tmat (greyC μ) * (sgn (qG ν) • Dmat (gammaD ν)) =
      sgn (qG ν) • (Tmat (greyC μ) * Dmat (gammaD ν)) := fun ν => Matrix.mul_smul _ _ _
  have hR : ∀ ν : Fin 6 → ZMod 2, sgn (qG ν) • Dmat (gammaD ν) *
      (sgn (qG μ) • (Tmat (greyC μ) * Dmat (gammaD μ))) =
      sgn (qG (ν + μ)) • (Tmat (greyC μ) * Dmat (gammaD (ν + μ))) := by
    intro ν
    have hc : sgn (qG ν) * sgn (qG μ) * sgn (bG μ ν) = sgn (qG (ν + μ)) := by
      rw [← sgn_add, ← sgn_add, qG_add, bG_comm ν μ]
    rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, Dg_mul_Tg, Matrix.smul_mul,
      Matrix.mul_assoc, Dmat_mul_Dmat, ← map_add, smul_smul, smul_smul, hc]
  rw [XiGamma, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  refine congrArg ((1 / 8 : ℚ) • ·) ?_
  simp only [hL, hR]
  exact (sum_add_right' (fun ν => sgn (qG ν) • (Tmat (greyC μ) * Dmat (gammaD ν))) μ).symm

theorem Dg_mul_XiG (ν : Fin 6 → ZMod 2) :
    Dmat (gammaD ν) * XiG = XiG * (sgn (qG ν) • (Tmat (greyC ν) * Dmat (gammaD ν))) := by
  have hL : ∀ μ : Fin 6 → ZMod 2, Dmat (gammaD ν) * (sgn (qG μ) • Tmat (greyC μ)) =
      (sgn (qG μ) * sgn (bG μ ν)) • (Tmat (greyC μ) * Dmat (gammaD ν)) := by
    intro μ
    rw [Matrix.mul_smul, Dg_mul_Tg, smul_smul]
  have hR : ∀ μ : Fin 6 → ZMod 2, sgn (qG μ) • Tmat (greyC μ) *
      (sgn (qG ν) • (Tmat (greyC ν) * Dmat (gammaD ν))) =
      (sgn (qG μ) * sgn (qG ν)) • (Tmat (greyC (μ + ν)) * Dmat (gammaD ν)) := by
    intro μ
    rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, Tmat_mul_Tmat, ← map_add,
      smul_smul]
  rw [XiG, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  refine congrArg ((1 / 8 : ℚ) • ·) ?_
  simp only [hL, hR]
  rw [← sum_add_right' (fun μ => (sgn (qG μ) * sgn (qG ν)) •
    (Tmat (greyC (μ + ν)) * Dmat (gammaD ν))) ν]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [add_add_cancel_fin6']
  have hc : sgn (qG (μ + ν)) * sgn (qG ν) = sgn (qG μ) * sgn (bG μ ν) := by
    rw [← sgn_add, ← sgn_add, qG_add]
    congr 1
    linear_combination qG ν * two_eq_zero'
  rw [hc]

theorem Dmat_mul_XiGamma (δ : Cocode) : Dmat δ * XiGamma = XiGamma * Dmat δ := by
  rw [XiGamma, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Dmat_comm δ]

theorem Tmat_mul_XiG (a : C) : Tmat a * XiG = XiG * Tmat a := by
  rw [XiG, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Tmat_comm a]

theorem TH_mul_XiGamma {h : C} (hh : (h : Fin 24 → ZMod 2) ∈ H) :
    Tmat h * XiGamma = XiGamma * Tmat h := by
  rw [XiGamma, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Dg_mul_TH _ hh]

theorem DHstar_mul_XiG {η : Cocode} (hη : η ∈ Hstar) : Dmat η * XiG = XiG * Dmat η := by
  rw [XiG, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, DHstar_mul_Tg hη]

@[expose] def XiW : Matrix SpinIdx SpinIdx ℚ :=
  (1 / 8 : ℚ) • ∑ μ : Fin 6 → ZMod 2, Tmat (greyC μ) * Dmat (gammaD μ)

theorem XiG_mul_XiGamma : XiG * XiGamma = XiGamma * XiW := by
  rw [XiG, Matrix.smul_mul, Finset.sum_mul, XiW, Matrix.mul_smul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Matrix.smul_mul, Tg_mul_XiGamma, Matrix.mul_smul, smul_smul, sgn_mul_self, one_smul]

theorem XiGamma_mul_XiG : XiGamma * XiG = XiG * XiW := by
  rw [XiGamma, Matrix.smul_mul, Finset.sum_mul, XiW, Matrix.mul_smul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Matrix.smul_mul, Dg_mul_XiG, Matrix.mul_smul, smul_smul, sgn_mul_self, one_smul]

theorem XiGamma_XiG_XiGamma : XiGamma * XiG * XiGamma = XiW := by
  rw [Matrix.mul_assoc, XiG_mul_XiGamma, ← Matrix.mul_assoc, XiGamma_mul_self, Matrix.one_mul]

theorem XiG_XiGamma_XiG : XiG * XiGamma * XiG = XiW := by
  rw [Matrix.mul_assoc, XiGamma_mul_XiG, ← Matrix.mul_assoc, XiG_mul_self, Matrix.one_mul]

theorem Ximat_pow_three : Ximat ^ 3 = 1 := by
  have hW : XiW * XiW = 1 := by
    calc XiW * XiW = XiGamma * XiG * (XiGamma * XiGamma) * XiG * XiGamma := by
          rw [← XiGamma_XiG_XiGamma]; simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [XiGamma_mul_self, Matrix.mul_one, Matrix.mul_assoc XiGamma, XiG_mul_self,
            Matrix.mul_one, XiGamma_mul_self]
  calc Ximat ^ 3 = (XiGamma * XiG * XiGamma) * (XiG * XiGamma * XiG) := by
        rw [pow_succ, pow_two, Ximat]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [XiGamma_XiG_XiGamma, XiG_XiGamma_XiG, hW]

theorem Ximat_transpose : Ximatᵀ = XiG * XiGamma := by
  rw [Ximat, transpose_mul, XiGamma_transpose, XiG_transpose]

theorem Ximat_transpose_mul_self : Ximatᵀ * Ximat = 1 := by
  rw [Ximat_transpose, Ximat, Matrix.mul_assoc, ← Matrix.mul_assoc XiGamma, XiGamma_mul_self,
    Matrix.one_mul, XiG_mul_self]

theorem Ximat_mul_transpose_self : Ximat * Ximatᵀ = 1 := by
  rw [Ximat_transpose, Ximat, Matrix.mul_assoc, ← Matrix.mul_assoc XiG, XiG_mul_self,
    Matrix.one_mul, XiGamma_mul_self]

theorem Ximat_inv : Ximat⁻¹ = Ximatᵀ := Matrix.inv_eq_left_inv Ximat_transpose_mul_self

theorem Ximat_inv_mul_self : Ximat⁻¹ * Ximat = 1 := by
  rw [Ximat_inv, Ximat_transpose_mul_self]

theorem Ximat_mul_inv_self : Ximat * Ximat⁻¹ = 1 := by
  rw [Ximat_inv, Ximat_mul_transpose_self]

theorem conj_eq_of_mul_eq {X Y : Matrix SpinIdx SpinIdx ℚ} (h : X * Ximat = Ximat * Y) :
    Ximat⁻¹ * X * Ximat = Y := by
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, Ximat_inv_mul_self, Matrix.one_mul]

private theorem two_ne_zero_rat : (2 : ℚ) ≠ 0 := two_ne_zero

theorem trace_Tmat_mul_Dmat (a : C) (δ : Cocode) :
    trace (Tmat a * Dmat δ) = if a = 0 ∧ δ = 0 then 4096 else 0 := by
  rw [← TDR_rat (a, δ), TDR_eq_qmatR, trace_qmatR two_ne_zero_rat]
  simp only [sgnR_zero, one_mul]

theorem trace_Tg_mul_Dg (μ ν : Fin 6 → ZMod 2) :
    trace (Tmat (greyC μ) * Dmat (gammaD ν)) = if μ = 0 ∧ ν = 0 then 4096 else 0 := by
  rw [trace_Tmat_mul_Dmat]
  congr 1
  exact propext (and_congr (greyC.map_eq_zero_iff greyC_injective)
    (gammaD.map_eq_zero_iff gammaD_injective))

theorem trace_Ximat : trace Ximat = 64 := by
  rw [Ximat, XiGamma, XiG, avg_mul_avg, trace_smul, trace_sum]
  simp only [trace_sum, trace_smul, smul_eq_mul]
  have h : ∀ μ ν : Fin 6 → ZMod 2, trace (Dmat (gammaD μ) * Tmat (greyC ν)) =
      if ν = 0 ∧ μ = 0 then 4096 else 0 := fun μ ν => by
    rw [trace_mul_comm, trace_Tg_mul_Dg]
  simp only [h, ite_and, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    qG_zero, sgn_zero]
  norm_num

theorem trace_XiGamma : trace XiGamma = 512 := by
  rw [XiGamma, trace_smul, trace_sum]
  have h : ∀ μ : Fin 6 → ZMod 2, trace (sgn (qG μ) • Dmat (gammaD μ)) =
      if μ = 0 then 4096 else 0 := fun μ => by
    rw [trace_smul, ← Matrix.one_mul (Dmat _), ← Tmat_zero, trace_Tmat_mul_Dmat]
    by_cases hμ : μ = 0
    · subst hμ; simp [sgn_zero]
    · have h0 : gammaD μ ≠ 0 := fun h => hμ (gammaD_injective (h.trans (map_zero _).symm))
      simp [hμ, h0]
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, ite_true, smul_eq_mul]
  norm_num

theorem trace_XiG : trace XiG = 512 := by
  rw [XiG, trace_smul, trace_sum]
  have h : ∀ μ : Fin 6 → ZMod 2, trace (sgn (qG μ) • Tmat (greyC μ)) =
      if μ = 0 then 4096 else 0 := fun μ => by
    rw [trace_smul, ← Matrix.mul_one (Tmat _), ← Dmat_zero, trace_Tmat_mul_Dmat]
    by_cases hμ : μ = 0
    · subst hμ; simp [sgn_zero]
    · have h0 : greyC μ ≠ 0 := fun h => hμ (greyC_injective (h.trans (map_zero _).symm))
      simp [hμ, h0]
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, ite_true, smul_eq_mul]
  norm_num

theorem trace_one_spin : trace (1 : Matrix SpinIdx SpinIdx ℚ) = 4096 := by
  rw [trace_one, card_spinIdx]
  norm_num

theorem Ximat_ne_one : Ximat ≠ 1 := fun h => by
  have := trace_Ximat
  rw [h, trace_one_spin] at this
  norm_num at this

theorem XiGamma_ne_one : XiGamma ≠ 1 := fun h => by
  have := trace_XiGamma
  rw [h, trace_one_spin] at this
  norm_num at this

theorem XiG_ne_one : XiG ≠ 1 := fun h => by
  have := trace_XiG
  rw [h, trace_one_spin] at this
  norm_num at this

theorem orderOf_Ximat : orderOf Ximat = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime Ximat_pow_three Ximat_ne_one

theorem orderOf_XiGamma : orderOf XiGamma = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two, XiGamma_mul_self]) XiGamma_ne_one

theorem orderOf_XiG : orderOf XiG = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two, XiG_mul_self]) XiG_ne_one

theorem Tg_mul_Ximat (μ : Fin 6 → ZMod 2) :
    Tmat (greyC μ) * Ximat = Ximat * Dmat (gammaD μ) := by
  rw [Ximat, ← Matrix.mul_assoc, Tg_mul_XiGamma, Matrix.mul_assoc, Matrix.mul_assoc]
  congr 1
  rw [Matrix.smul_mul, Matrix.mul_assoc, Dg_mul_XiG, ← Matrix.mul_assoc, Tmat_mul_XiG,
    Matrix.mul_assoc, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc (Tmat _),
    Tmat_mul_self, Matrix.one_mul, smul_smul, sgn_mul_self, one_smul]

theorem Dg_mul_Ximat (ν : Fin 6 → ZMod 2) :
    Dmat (gammaD ν) * Ximat = Ximat * (sgn (qG ν) • (Tmat (greyC ν) * Dmat (gammaD ν))) := by
  rw [Ximat, ← Matrix.mul_assoc, Dmat_mul_XiGamma, Matrix.mul_assoc, Dg_mul_XiG,
    Matrix.mul_assoc]

theorem TH_mul_Ximat {h : C} (hh : (h : Fin 24 → ZMod 2) ∈ H) :
    Tmat h * Ximat = Ximat * Tmat h := by
  rw [Ximat, ← Matrix.mul_assoc, TH_mul_XiGamma hh, Matrix.mul_assoc, Tmat_mul_XiG,
    Matrix.mul_assoc]

theorem DHstar_mul_Ximat {η : Cocode} (hη : η ∈ Hstar) : Dmat η * Ximat = Ximat * Dmat η := by
  rw [Ximat, ← Matrix.mul_assoc, Dmat_mul_XiGamma, Matrix.mul_assoc, DHstar_mul_XiG hη,
    Matrix.mul_assoc]

theorem conj_Tg (μ : Fin 6 → ZMod 2) :
    Ximat⁻¹ * Tmat (greyC μ) * Ximat = Dmat (gammaD μ) :=
  conj_eq_of_mul_eq (Tg_mul_Ximat μ)

theorem conj_Dg (ν : Fin 6 → ZMod 2) :
    Ximat⁻¹ * Dmat (gammaD ν) * Ximat = sgn (qG ν) • (Tmat (greyC ν) * Dmat (gammaD ν)) :=
  conj_eq_of_mul_eq (Dg_mul_Ximat ν)

theorem conj_TH {h : C} (hh : (h : Fin 24 → ZMod 2) ∈ H) : Ximat⁻¹ * Tmat h * Ximat = Tmat h :=
  conj_eq_of_mul_eq (TH_mul_Ximat hh)

theorem conj_DHstar {η : Cocode} (hη : η ∈ Hstar) : Ximat⁻¹ * Dmat η * Ximat = Dmat η :=
  conj_eq_of_mul_eq (DHstar_mul_Ximat hη)

theorem conj_Ximat (μ ν : Fin 6 → ZMod 2) {h : C} (hh : (h : Fin 24 → ZMod 2) ∈ H) {η : Cocode}
    (hη : η ∈ Hstar) :
    Ximat⁻¹ * (Tmat (greyC μ) * Tmat h * Dmat (gammaD ν) * Dmat η) * Ximat =
      sgn (qG ν + bG μ ν) • (Tmat (greyC ν) * Tmat h * Dmat (gammaD (μ + ν)) * Dmat η) := by
  apply conj_eq_of_mul_eq
  have e1 : Tmat (greyC μ) * Tmat h * Dmat (gammaD ν) * Dmat η * Ximat =
      Ximat * (Dmat (gammaD μ) * Tmat h * (sgn (qG ν) • (Tmat (greyC ν) * Dmat (gammaD ν))) *
        Dmat η) := by
    simp only [Matrix.mul_assoc]
    rw [DHstar_mul_Ximat hη, ← Matrix.mul_assoc (Dmat (gammaD ν)), Dg_mul_Ximat,
      Matrix.mul_assoc, ← Matrix.mul_assoc (Tmat h), TH_mul_Ximat hh, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Tmat (greyC μ)), Tg_mul_Ximat]
    simp only [Matrix.mul_assoc]
  rw [e1]
  refine congrArg (Ximat * ·) ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, Dg_mul_TH μ hh, Matrix.mul_assoc (Tmat h),
    ← Matrix.mul_assoc (Dmat (gammaD μ)), Dg_mul_Tg, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, ← sgn_add, Matrix.mul_assoc (Tmat (greyC ν)),
    Dmat_mul_Dmat, ← map_add, bG_comm ν μ, ← Matrix.mul_assoc (Tmat h), Tmat_comm h]

theorem qmatR_mem_Qmats (s : ZMod 2) (a : C) (δ : Cocode) : qmatR ℚ s a δ ∈ Qmats :=
  ⟨toGL ⟨s, a, δ⟩, by rw [← range_toGL]; exact ⟨_, rfl⟩, coe_toGL _⟩

theorem mem_Qmats_iff {g : Matrix SpinIdx SpinIdx ℚ} :
    g ∈ Qmats ↔ ∃ (s : ZMod 2) (a : C) (δ : Cocode), g = qmatR ℚ s a δ := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [← range_toGL] at hu
    obtain ⟨x, rfl⟩ := hu
    exact ⟨x.s, x.a, x.δ, coe_toGL x⟩
  · rintro ⟨s, a, δ, rfl⟩
    exact qmatR_mem_Qmats s a δ

theorem exists_greyC_add (a : C) :
    ∃ (μ : Fin 6 → ZMod 2) (h : C), (h : Fin 24 → ZMod 2) ∈ H ∧ a = greyC μ + h := by
  have ha : (a : Fin 24 → ZMod 2) ∈ G ⊔ H := by rw [G_sup_H]; exact a.2
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 ha
  obtain ⟨μ, hμ⟩ := (mem_G_iff x).1 hx
  refine ⟨μ, ⟨y, H_le_C hy⟩, hy, Subtype.ext ?_⟩
  rw [Submodule.coe_add, hμ, ← hxy]

theorem conj_mem_Qmats {g : Matrix SpinIdx SpinIdx ℚ} (hg : g ∈ Qmats) :
    Ximat⁻¹ * g * Ximat ∈ Qmats := by
  obtain ⟨s, a, δ, rfl⟩ := mem_Qmats_iff.1 hg
  obtain ⟨μ, h, hh, rfl⟩ := exists_greyC_add a
  obtain ⟨ν, hν⟩ := exists_gammaD_add_mem_Hstar δ
  set η := δ - gammaD ν
  have hδ : δ = gammaD ν + η := by simp [η]
  rw [hδ, qmatR_eq, ← Tmat_eq, ← Dmat_eq, sgnR_rat, ← Tmat_mul_Tmat, ← Dmat_mul_Dmat,
    Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc (Tmat (greyC μ) * Tmat h),
    conj_Ximat μ ν hh hν, smul_smul, ← sgn_add, Matrix.mul_assoc (Tmat (greyC ν) * Tmat h),
    Tmat_mul_Tmat, Dmat_mul_Dmat, ← sgnR_rat, Tmat_eq, Dmat_eq, ← qmatR_eq]
  exact qmatR_mem_Qmats _ _ _

theorem Ximat_inv_pow_three_conj (g : Matrix SpinIdx SpinIdx ℚ) :
    Ximat⁻¹ * (Ximat⁻¹ * (Ximat⁻¹ * g * Ximat) * Ximat) * Ximat = g := by
  have h3 : Ximat * Ximat * Ximat = 1 := by
    rw [← Ximat_pow_three, pow_succ, pow_two]
  have hinv : Ximat⁻¹ = Ximat * Ximat := by
    calc Ximat⁻¹ = Ximat⁻¹ * (Ximat * Ximat * Ximat) := by rw [h3, Matrix.mul_one]
      _ = Ximat * Ximat := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc Ximat⁻¹, Ximat_inv_mul_self, Matrix.one_mul]
  calc Ximat⁻¹ * (Ximat⁻¹ * (Ximat⁻¹ * g * Ximat) * Ximat) * Ximat =
        (Ximat * Ximat * Ximat) * (Ximat * Ximat * Ximat) * g * (Ximat * Ximat * Ximat) := by
          rw [hinv]; simp only [Matrix.mul_assoc]
    _ = g := by rw [h3, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]

theorem image_conj_Qmats : (fun g => Ximat⁻¹ * g * Ximat) '' Qmats = Qmats := by
  refine Set.Subset.antisymm ?_ fun g hg => ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact conj_mem_Qmats hg
  · exact ⟨_, conj_mem_Qmats (conj_mem_Qmats hg), Ximat_inv_pow_three_conj g⟩

@[expose] def XiU : GL SpinIdx ℚ :=
  ⟨Ximat, Ximatᵀ, Ximat_mul_transpose_self, Ximat_transpose_mul_self⟩

@[simp] theorem coe_XiU : (XiU : Matrix SpinIdx SpinIdx ℚ) = Ximat := rfl

theorem coe_XiU_inv : ((XiU⁻¹ : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = Ximat⁻¹ := by
  rw [Ximat_inv]
  rfl

theorem mem_Q_iff_coe_mem_Qmats (u : GL SpinIdx ℚ) :
    u ∈ Q ↔ (u : Matrix SpinIdx SpinIdx ℚ) ∈ Qmats := by
  refine ⟨fun hu => ⟨u, hu, rfl⟩, ?_⟩
  rintro ⟨v, hv, hvu⟩
  rwa [← Units.ext hvu]

theorem XiU_inv_conj_mem_Q {u : GL SpinIdx ℚ} (hu : u ∈ Q) : XiU⁻¹ * u * XiU ∈ Q := by
  rw [mem_Q_iff_coe_mem_Qmats, Units.val_mul, Units.val_mul, coe_XiU_inv, coe_XiU]
  exact conj_mem_Qmats ((mem_Q_iff_coe_mem_Qmats u).1 hu)

theorem XiU_mem_normalizer : XiU ∈ Subgroup.normalizer (Q : Set (GL SpinIdx ℚ)) := by
  have h3 : XiU ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, coe_XiU, Ximat_pow_three,
    Units.val_one])
  have hinv : XiU⁻¹ ∈ Subgroup.normalizer (Q : Set (GL SpinIdx ℚ)) := by
    rw [Subgroup.mem_normalizer_iff, inv_inv]
    intro u
    refine ⟨XiU_inv_conj_mem_Q, fun hu => ?_⟩
    have h := XiU_inv_conj_mem_Q (XiU_inv_conj_mem_Q hu)
    have h3' : XiU * XiU * XiU = 1 := by rw [← pow_three', h3]
    have hi : XiU⁻¹ = XiU * XiU := by
      rw [inv_eq_iff_mul_eq_one, ← mul_assoc, h3']
    have e : XiU⁻¹ * (XiU⁻¹ * (XiU⁻¹ * u * XiU) * XiU) * XiU = u := by
      rw [hi]
      simp only [← mul_assoc]
      rw [h3', one_mul, h3', one_mul, mul_assoc u, mul_assoc u, h3', mul_one]
    rwa [e] at h
  have h := Subgroup.inv_mem _ hinv
  rwa [inv_inv] at h

theorem orderOf_XiU : orderOf XiU = 3 := by
  rw [← orderOf_units, coe_XiU, orderOf_Ximat]

theorem xi_spin_Fourier_conjugation :
    (XiGammaᵀ = XiGamma ∧ XiGammaᵀ * XiGamma = 1 ∧ XiGamma * XiGamma = 1 ∧
      orderOf XiGamma = 2) ∧
    (XiGᵀ = XiG ∧ XiGᵀ * XiG = 1 ∧ XiG * XiG = 1 ∧ orderOf XiG = 2) ∧
    Ximatᵀ * Ximat = 1 ∧ Ximat * Ximatᵀ = 1 ∧ (∀ i j, Ximat i j ∈ dyadic) ∧
    (fun g => Ximat⁻¹ * g * Ximat) '' Qmats = Qmats ∧
    XiU ∈ Subgroup.normalizer (Q : Set (GL SpinIdx ℚ)) ∧
    Ximat ^ 3 = 1 ∧ orderOf Ximat = 3 ∧ trace Ximat = 64 ∧
    (∀ h : C, (h : Fin 24 → ZMod 2) ∈ H → Ximat⁻¹ * Tmat h * Ximat = Tmat h) ∧
    (∀ η ∈ Hstar, Ximat⁻¹ * Dmat η * Ximat = Dmat η) ∧
    (∀ (μ ν : Fin 6 → ZMod 2) (h : C), (h : Fin 24 → ZMod 2) ∈ H → ∀ η ∈ Hstar,
      Ximat⁻¹ * (Tmat (greyC μ) * Tmat h * Dmat (gammaD ν) * Dmat η) * Ximat =
        sgn (qG ν + bG μ ν) • (Tmat (greyC ν) * Tmat h * Dmat (gammaD (μ + ν)) * Dmat η)) ∧
    (∀ μ : Fin 6 → ZMod 2, Ximat⁻¹ * Tmat (greyC μ) * Ximat = Dmat (gammaD μ)) ∧
    (∀ μ : Fin 6 → ZMod 2, Ximat⁻¹ * Dmat (gammaD μ) * Ximat =
      sgn (qG μ) • (Tmat (greyC μ) * Dmat (gammaD μ))) :=
  ⟨⟨XiGamma_transpose, XiGamma_transpose_mul_self, XiGamma_mul_self, orderOf_XiGamma⟩,
    ⟨XiG_transpose, XiG_transpose_mul_self, XiG_mul_self, orderOf_XiG⟩,
    Ximat_transpose_mul_self, Ximat_mul_transpose_self, Ximat_mem_dyadic, image_conj_Qmats,
    XiU_mem_normalizer, Ximat_pow_three, orderOf_Ximat, trace_Ximat, fun _ hh => conj_TH hh,
    fun _ hη => conj_DHstar hη, fun μ ν _ hh _ hη => conj_Ximat μ ν hh hη, conj_Tg, conj_Dg⟩

end CFSG.Monster.Xi
