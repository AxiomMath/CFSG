module

public import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofHess
import CFSG.RankThree.PartTwo.KFacts.KSL3PiOrder3TypeC

public section

namespace CFSG.RankThree.PartTwo.Sec16.ProofKSL3Two

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec16.ProofHess Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

theorem not_two_pow_mod_nine {n : ℕ} (hn3 : ¬ 3 ∣ n) : ¬ (2 ^ n % 9 = 1 ∨ 2 ^ n % 9 = 8) := by
  have h6 : 2 ^ n % 9 = 2 ^ (n % 6) % 9 := by
    conv_lhs => rw [← Nat.div_add_mod n 6, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have : n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
  rcases this with h | h | h | h <;> rw [h6, h] <;> norm_num

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem det_inv_mul_mul (g x : GL (Fin 3) K) :
    ((g⁻¹ * x * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      (x : Matrix (Fin 3) (Fin 3) K).det := by
  have h := congrArg Units.val (show GeneralLinearGroup.det (g⁻¹ * x * g) =
      GeneralLinearGroup.det x by
    rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul])
  simpa only [GeneralLinearGroup.val_det_apply] using h

theorem type1_of_lift (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : ¬ 9 ∣ Nat.card K - 1) {y : GL (Fin 3) K} (hy : y ∈ slPi π 3 (p ^ f) K)
    (hy3 : ProjGenLinGroup.mk y ^ 3 = 1) (hy1 : ProjGenLinGroup.mk y ≠ 1) :
    Type123 π (p ^ f) K y 1 := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hy3' : y ^ 3 = 1 := pow_three_eq_one_of_lift hK h9 hy hy3
  have hdet : (y : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hy).2
  have hyH : y ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ hy
  have hyZ : y ∉ zPi π 3 (p ^ f) K := fun hz => hy1
    (KFacts.mk_eq_one_iff_mem_statedScalars'.mpr (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz))
  rcases type123_exhaust hK hq hyH hyZ (by rw [hy3']; exact one_mem _) with h1 | h2 | h3'
  · exact h1
  · exfalso
    obtain ⟨e, he3, he1, z, hz, g, -, hD⟩ := h2
    obtain ⟨ξ, -, rfl⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hz
    have he1' : (e : K) ≠ 1 := fun h => he1 (Units.ext h)
    have hdetD := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K).det) hD
    rw [det_inv_mul_mul, Units.val_mul, det_mul, hdet, one_mul, KFacts.det_scalar_eq, coe_diagE,
      det_diagonal, Fin.prod_univ_three] at hdetD
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, mul_one] at hdetD
    exact not_cube_of_not_nine_dvd h9 he3 he1' (ξ : K) hdetD
  · exfalso
    obtain ⟨-, -, hirr⟩ := h3'
    have hys : ∀ c : K, (y : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 := by
      intro c hc
      apply hy1
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hc
        rw [hc, det_zero] at hdet
        exact zero_ne_one hdet
      exact KFacts.mk_eq_one_iff_mem_statedScalars'.mpr (mem_statedScalars_of_eq_smul hc hc0)
    have hy3m : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hy3', Units.val_one]
    obtain ⟨P, j, hP, hPD⟩ := exists_normal_form_det_one hτ hτ1 h3 hy3m hdet hys
    obtain ⟨hτ0, -, -⟩ := tau_facts hτ hτ1
    set u : Kˣ := Units.mk0 (τ ^ (j : ℕ)) (pow_ne_zero _ hτ0) with hu
    set g : GL (Fin 3) K := hP.unit with hg
    have hgm : (g : Matrix (Fin 3) (Fin 3) K) = P := IsUnit.unit_spec hP
    refine not_irreducible_of_diag (x := y) (z := GeneralLinearGroup.scalar (Fin 3) u) (g := g)
      ⟨u, rfl⟩ (d := ![τ, τ ^ 2, 1]) ?_ hirr
    have hginv : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * P = 1 := by
      rw [← hgm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hyz : ((y * GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = τ ^ (j : ℕ) • (y : Matrix (Fin 3) (Fin 3) K) := by
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, hu, Units.val_mk0]
    rw [Units.val_mul, Units.val_mul, hyz, hgm, Matrix.mul_assoc, hPD, ← Matrix.mul_assoc, hginv,
      Matrix.one_mul]

theorem exists_heis_scalar (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : ¬ 9 ∣ Nat.card K - 1) {y₁ y₂ : GL (Fin 3) K} (hy₁S : y₁ ∈ slPi π 3 (p ^ f) K)
    (hy₂S : y₂ ∈ slPi π 3 (p ^ f) K) (h₁3 : ProjGenLinGroup.mk y₁ ^ 3 = 1)
    (h₂3 : ProjGenLinGroup.mk y₂ ^ 3 = 1) (he₁1 : ProjGenLinGroup.mk y₁ ≠ 1)
    (hcomm_bar : ProjGenLinGroup.mk y₁ * ProjGenLinGroup.mk y₂ =
      ProjGenLinGroup.mk y₂ * ProjGenLinGroup.mk y₁)
    (he₂ : ProjGenLinGroup.mk y₂ ∉ Subgroup.zpowers (ProjGenLinGroup.mk y₁)) :
    ∃ ζ : Kˣ, ζ ≠ 1 ∧ y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂ := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hy₁3 : y₁ ^ 3 = 1 := pow_three_eq_one_of_lift hK h9 hy₁S h₁3
  have hdet₁ : (y₁ : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hy₁S).2
  have hdet₂ : (y₂ : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hy₂S).2
  have hy₁s : ∀ c : K, (y₁ : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 := by
    intro c hc
    apply he₁1
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      rw [hc, det_zero] at hdet₁
      exact zero_ne_one hdet₁
    exact KFacts.mk_eq_one_iff_mem_statedScalars'.mpr (mem_statedScalars_of_eq_smul hc hc0)
  have hy₁3m : (y₁ : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hy₁3, Units.val_one]
  obtain ⟨P, j, hP, hPD⟩ := exists_normal_form_det_one hτ hτ1 h3 hy₁3m hdet₁ hy₁s
  set D : Matrix (Fin 3) (Fin 3) K := diagonal ![τ, τ ^ 2, 1] with hD
  set Y : Matrix (Fin 3) (Fin 3) K := τ ^ (j : ℕ) • (y₁ : Matrix (Fin 3) (Fin 3) K) with hY
  set Q := P⁻¹ with hQ
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPQ : P * Q = 1 := Matrix.mul_nonsing_inv P hPdet
  have hQP : Q * P = 1 := Matrix.nonsing_inv_mul P hPdet
  have hYc : ∀ M : Matrix (Fin 3) (Fin 3) K,
      M * (y₁ : Matrix (Fin 3) (Fin 3) K) = (y₁ : Matrix (Fin 3) (Fin 3) K) * M →
        M * Y = Y * M := by
    intro M hM
    rw [hY, Matrix.mul_smul, Matrix.smul_mul, hM]
  have hYPD : Y = P * D * Q := by
    calc Y = Y * (P * Q) := by rw [hPQ, Matrix.mul_one]
      _ = (Y * P) * Q := by rw [Matrix.mul_assoc]
      _ = P * D * Q := by rw [hPD]
  set N := Q * (y₂ : Matrix (Fin 3) (Fin 3) K) * P with hN
  have hNdet : N.det = 1 := by rw [hN, det_conj hQP, hdet₂]
  have hnc : y₁ * y₂ ≠ y₂ * y₁ := by
    intro hcomm
    have hcomm' : (y₂ : Matrix (Fin 3) (Fin 3) K) * y₁ = y₁ * y₂ := by
      have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hcomm
      simp only [Units.val_mul] at h
      exact h.symm
    have hND : N * D = D * N := conj_commute hPQ hQP hPD (hYc _ hcomm')
    have hNdiag := eq_diagonal_of_commute hτ hτ1 hND
    have hy₂3 : y₂ ^ 3 = 1 := pow_three_eq_one_of_lift hK h9 hy₂S h₂3
    have hN3 : N ^ 3 = 1 := by
      rw [hN, conj_pow hPQ hQP, ← Units.val_pow_eq_pow_val, hy₂3, Units.val_one,
        Matrix.mul_one, hQP]
    have hcub : ∀ i, (N i i) ^ 3 = 1 := by
      intro i
      have h := congrFun (congrFun hN3 i) i
      rw [hNdiag, diagonal_pow, diagonal_apply_eq, Matrix.one_apply_eq] at h
      simpa using h
    have habc : N 0 0 * N 1 1 * N 2 2 = 1 := by
      have h := hNdet
      rw [hNdiag, det_diagonal, Fin.prod_univ_three] at h
      exact h
    obtain ⟨i, hi⟩ := exists_eq_smul_pow_of_diag hτ hτ1 (hcub 0) (hcub 1) habc
    obtain ⟨c, hc⟩ : ∃ c : K, c = N 2 2 := ⟨_, rfl⟩
    have hNeq : N = c • D ^ i := by
      rw [hc, ← hi, hNdiag]
      congr 1
      funext l
      fin_cases l <;> rfl
    have hy₂eq : (y₂ : Matrix (Fin 3) (Fin 3) K) =
        (c * (τ ^ (j : ℕ)) ^ i) • (y₁ : Matrix (Fin 3) (Fin 3) K) ^ i := by
      have h1 : (y₂ : Matrix (Fin 3) (Fin 3) K) = P * N * Q := by rw [hN, unconj hPQ]
      have h2 : P * D ^ i * Q = Y ^ i := by
        rw [hYPD, conj_pow hQP hPQ D i]
      rw [h1, hNeq, Matrix.mul_smul, Matrix.smul_mul, h2, hY, smul_pow, smul_smul]
    apply he₂
    have hc0 : c * (τ ^ (j : ℕ)) ^ i ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hy₂eq
      rw [hy₂eq, det_zero] at hdet₂
      exact zero_ne_one hdet₂
    have hsc : y₂ * (y₁ ^ i)⁻¹ ∈ StatedScalars (Fin 3) K := by
      refine mem_statedScalars_of_eq_smul (a := c * (τ ^ (j : ℕ)) ^ i) ?_ hc0
      have hinv : ((y₁ ^ i : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (((y₁ ^ i)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [Units.val_mul, hy₂eq, Matrix.smul_mul, ← Units.val_pow_eq_pow_val, hinv]
    have hmk := KFacts.mk_eq_one_iff_mem_statedScalars'.mpr hsc
    rw [map_mul, map_inv, mul_inv_eq_one] at hmk
    rw [hmk, map_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) i
  set w := y₁ * y₂ * y₁⁻¹ * y₂⁻¹ with hw
  have hwsc : w ∈ StatedScalars (Fin 3) K := by
    rw [← KFacts.mk_eq_one_iff_mem_statedScalars', hw, map_mul, map_mul, map_mul, map_inv,
      map_inv, hcomm_bar]
    group
  obtain ⟨ζ, hζ⟩ := hwsc
  refine ⟨ζ, fun h1 => hnc ?_, ?_⟩
  · have hw1 : w = 1 := by rw [← hζ, h1, map_one]
    calc y₁ * y₂ = w * (y₂ * y₁) := by rw [hw]; group
      _ = y₂ * y₁ := by rw [hw1, one_mul]
  · rw [hζ, hw]
    group

end CFSG.RankThree.PartTwo.Sec16.ProofKSL3Two
