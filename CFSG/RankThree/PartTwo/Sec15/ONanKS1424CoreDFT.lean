module

public import CFSG.RankThree.PartTwo.Sec15.ONanKS1424Model

public section

namespace CFSG.RankThree.PartTwo.Sec15.KS1424

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial Matrix

variable {K : Type} [Field K] {π : Bool} {n : ℕ} {T : Type} [Group T]

@[expose] def dftMat (τ : K) : Matrix (Fin 3) (Fin 3) K := !![1, 1, 1; 1, τ, τ ^ 2; 1, τ ^ 2, τ]

def swapMat : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

theorem swapMat_sq : (swapMat : Matrix (Fin 3) (Fin 3) K) * swapMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat, mul_apply, Fin.sum_univ_three]

theorem dftMat_sq [CharP K 2] {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    dftMat τ * dftMat τ = swapMat := by
  have h2 : τ ^ 2 + τ + 1 = 0 := by
    have : (τ - 1) * (τ ^ 2 + τ + 1) = 0 := by linear_combination hτ
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hτ1)
  have h0 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dftMat, swapMat, mul_apply, Fin.sum_univ_three] <;> grind

theorem dftMat_pow_four [CharP K 2] {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    dftMat τ ^ 4 = 1 := by
  have : dftMat τ ^ 4 = (dftMat τ * dftMat τ) * (dftMat τ * dftMat τ) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [this, dftMat_sq hτ hτ1, swapMat_sq]

@[expose] noncomputable def dftGL [CharP K 2] {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    GL (Fin 3) K :=
  ⟨dftMat τ, dftMat τ ^ 3, by rw [← pow_succ']; exact dftMat_pow_four hτ hτ1,
    by rw [← pow_succ]; exact dftMat_pow_four hτ hτ1⟩

theorem coe_dftGL [CharP K 2] {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    ((dftGL hτ hτ1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = dftMat τ := rfl

theorem det_dftMat [CharP K 2] {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    (dftMat τ).det = 1 := by
  have h2 : τ ^ 2 + τ + 1 = 0 := by
    have : (τ - 1) * (τ ^ 2 + τ + 1) = 0 := by linear_combination hτ
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hτ1)
  have h0 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [dftMat, det_fin_three]
  simp
  grind

theorem dftGL_mem_slPi [CharP K 2] (hK : PiField π 2 n K) (hq : ModThree π (2 ^ n)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) : dftGL hτ hτ1 ∈ slPi π 3 (2 ^ n) K := by
  have h2 : τ ^ 2 + τ + 1 = 0 := by
    have : (τ - 1) * (τ ^ 2 + τ + 1) = 0 := by linear_combination hτ
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hτ1)
  have h0 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hdet := det_dftMat hτ hτ1
  cases π
  · have h := hK.unitary
    rw [mem_slPi_false h]
    refine ⟨hdet, ?_⟩
    have hn := pow_succ_eq_one_of_modThree hq hτ
    have h1 : h.bar τ * τ = 1 := by rw [h.bar_apply, ← pow_succ]; exact hn
    have hb : h.bar τ = τ ^ 2 := by
      calc h.bar τ = h.bar τ * τ ^ 3 := by rw [hτ, mul_one]
        _ = (h.bar τ * τ) * τ ^ 2 := by ring
        _ = τ ^ 2 := by rw [h1, one_mul]
    have hb2 : h.bar (τ ^ 2) = τ := by
      rw [map_pow, hb]
      grind
    rw [coe_dftGL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dftMat, mul_apply, Fin.sum_univ_three, transpose_apply, hb, hb2] <;> grind
  · rw [mem_slPi_true]
    exact hdet

theorem exists_order_four (hK : PiField π 2 n K) (hq : ModThree π (2 ^ n))
    (M : LModel π 2 n K T) : ∃ t : T, orderOf t = 4 := by
  have := hK.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  set F : ↥(slPi π 3 (2 ^ n) K) := ⟨dftGL hτ hτ1, dftGL_mem_slPi hK hq hτ hτ1⟩ with hFdef
  have hF4 : F ^ 4 = 1 := by
    apply Subtype.ext
    apply Units.ext
    show ((dftGL hτ hτ1 ^ 4 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [Units.val_pow_eq_pow_val, coe_dftGL]
    exact dftMat_pow_four hτ hτ1
  have hnot : ¬ (M.μ F) ^ 2 ^ 1 = 1 := by
    intro h
    rw [pow_one, ← map_pow] at h
    obtain ⟨c, hc⟩ := (M.ker_iff _).mp h
    have h12 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 2) hc
    have h01 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 1) hc
    have hsq : (((F ^ 2 : ↥(slPi π 3 (2 ^ n) K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        swapMat := by
      show ((dftGL hτ hτ1 ^ 2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
      rw [Units.val_pow_eq_pow_val, coe_dftGL, pow_two]
      exact dftMat_sq hτ hτ1
    simp only [hsq, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h12 h01
    simp [swapMat] at h12 h01
  refine ⟨M.μ F, ?_⟩
  have hfin : (M.μ F) ^ 2 ^ (1 + 1) = 1 := by
    rw [← map_pow]
    show M.μ (F ^ (2 ^ 2)) = 1
    rw [show 2 ^ 2 = 4 by norm_num, hF4, map_one]
  have := orderOf_eq_prime_pow hnot hfin
  simpa using this

end CFSG.RankThree.PartTwo.Sec15.KS1424
