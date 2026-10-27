module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res7ProofLin
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofACent

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofU3Two

open CFSG.RankThree.Classical2 (unitarySet)
open scoped Matrix

theorem scalar_of_commute_unitarySet {ℓ f : ℕ} [hℓ : Fact ℓ.Prime] (hℓ3 : ℓ ≠ 3)
    (hq1 : ℓ ^ f % 3 = 2) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω ℓ]
    {M : Matrix (Fin 3) (Fin 3) Ω}
    (hM : ∀ Y : GL (Fin 3) Ω, Y ∈ unitarySet (ℓ ^ f) 3 →
      M * (Y : Matrix (Fin 3) (Fin 3) Ω) = (Y : Matrix (Fin 3) (Fin 3) Ω) * M) :
    ∃ μ : Ω, M = Matrix.scalar (Fin 3) μ := by
  classical
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero _ hℓ.out.ne_zero
  have hq20 : (ℓ ^ f) ^ 2 ≠ 0 := pow_ne_zero _ hq0
  have h3Ω : (3 : Ω) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : Ω) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff Ω ℓ] at h'
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_three).1 h')
  obtain ⟨ζu, hζu⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.exists_units_orderOf_three Ω h3Ω
  have hζ3u : ζu ^ 3 = 1 := by rw [← hζu]; exact pow_orderOf_eq_one ζu
  have hζ3 : (ζu : Ω) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hζ3u, Units.val_one]
  have hζ1 : (ζu : Ω) ≠ 1 := by
    intro h
    have h' : ζu = 1 := Units.ext h
    rw [h', orderOf_one] at hζu
    exact absurd hζu (by norm_num)
  set ζ : Ω := (ζu : Ω) with hζdef
  have hζ0 : ζ ≠ 0 := ζu.ne_zero
  obtain ⟨m1, hm1⟩ : ∃ m, ℓ ^ f + 1 = 3 * m := ⟨(ℓ ^ f + 1) / 3, by omega⟩
  obtain ⟨m2, hm2⟩ : ∃ m, (ℓ ^ f) ^ 2 = 3 * m + 1 :=
    ⟨(ℓ ^ f) ^ 2 / 3, by
      have h9 : (ℓ ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq1]
      omega⟩
  have hx1 : ∀ x : Ω, x ^ 3 = 1 → x ^ (ℓ ^ f) * x = 1 := fun x hx => by
    rw [← pow_succ, hm1, pow_mul, hx, one_pow]
  have hx2 : ∀ x : Ω, x ^ 3 = 1 → x ^ ((ℓ ^ f) ^ 2) = x := fun x hx => by
    rw [hm2, pow_succ, pow_mul, hx, one_pow, one_mul]
  set ν : Fin 3 → Ω := ![ζ, ζ ^ 2, 1] with hν
  have hν3 : ∀ i, ν i ^ 3 = 1 := by
    intro i
    fin_cases i
    · simpa [hν] using hζ3
    · show (ζ ^ 2) ^ 3 = 1
      rw [← pow_mul, mul_comm, pow_mul, hζ3, one_pow]
    · simp [hν]
  have hDdet : (Matrix.diagonal ν).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    show ζ * ζ ^ 2 * 1 = 1
    linear_combination hζ3
  have hDunit : ((Matrix.diagonal ν).map (· ^ ℓ ^ f))ᵀ * Matrix.diagonal ν = 1 := by
    rw [Matrix.diagonal_map (f := fun x : Ω => x ^ (ℓ ^ f))
        (by show (0 : Ω) ^ (ℓ ^ f) = 0; exact zero_pow hq0),
      Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hx1 _ (hν3 i)
  have hDent : ∀ i j, (Matrix.diagonal ν i j) ^ (ℓ ^ f) ^ 2 = Matrix.diagonal ν i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      exact hx2 _ (hν3 i)
    · rw [Matrix.diagonal_apply_ne _ hij, zero_pow hq20]
  have hDdet0 : (Matrix.diagonal ν).det ≠ 0 := by rw [hDdet]; exact one_ne_zero
  have hD : Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ν) hDdet0 ∈
      unitarySet (ℓ ^ f) 3 := by
    unfold unitarySet
    rw [Set.mem_setOf_eq, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    exact ⟨hDent, hDdet, hDunit⟩
  have hMD := hM _ hD
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero] at hMD
  have hν01 : ν 0 ≠ ν 1 := by
    show ζ ≠ ζ ^ 2
    intro h
    apply hζ1
    have h' : ζ * (ζ - 1) = 0 := by linear_combination -h
    exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_left hζ0)
  have hν02 : ν 0 ≠ ν 2 := by
    show ζ ≠ 1
    exact hζ1
  have hν12 : ν 1 ≠ ν 2 := by
    show ζ ^ 2 ≠ 1
    intro h
    apply hζ1
    linear_combination hζ3 - ζ * h
  have hoff : ∀ i j, i ≠ j → M i j = 0 := by
    intro i j hij
    have h := congrFun (congrFun hMD i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have h' : (ν j - ν i) * M i j = 0 := by linear_combination h
    have hne : ν j - ν i ≠ 0 := by
      intro h0
      have h0' : ν j = ν i := sub_eq_zero.1 h0
      fin_cases i <;> fin_cases j <;>
        first | exact absurd rfl hij | skip
      · exact hν01 h0'.symm
      · exact hν02 h0'.symm
      · exact hν01 h0'
      · exact hν12 h0'.symm
      · exact hν02 h0'
      · exact hν12 h0'
    exact (mul_eq_zero.1 h').resolve_left hne
  have hCdet0 : (CFSG.RankThree.PartTwo.Sec4.Res424Seven.cyc3 Ω).det ≠ 0 := by
    rw [CFSG.RankThree.PartTwo.Sec4.Res424Seven.det_cyc3]; exact one_ne_zero
  have hCmap : (CFSG.RankThree.PartTwo.Sec4.Res424Seven.cyc3 Ω).map (· ^ ℓ ^ f) =
      CFSG.RankThree.PartTwo.Sec4.Res424Seven.cyc3 Ω := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.RankThree.PartTwo.Sec4.Res424Seven.cyc3, zero_pow hq0]
  have hC : Matrix.GeneralLinearGroup.mkOfDetNeZero
      (CFSG.RankThree.PartTwo.Sec4.Res424Seven.cyc3 Ω) hCdet0 ∈ unitarySet (ℓ ^ f) 3 := by
    unfold unitarySet
    rw [Set.mem_setOf_eq, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    refine ⟨fun i j => ?_, CFSG.RankThree.PartTwo.Sec4.Res424Seven.det_cyc3, ?_⟩
    · fin_cases i <;> fin_cases j <;>
        simp [CFSG.RankThree.PartTwo.Sec4.Res424Seven.cyc3, zero_pow hq20]
    · rw [hCmap]
      exact CFSG.RankThree.PartTwo.Sec4.Res424Seven.cyc3_transpose_mul
  have hMC := hM _ hC
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero] at hMC
  have e02 : M 0 0 = M 2 2 := by
    have h := congrFun (congrFun hMC 0) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three, CFSG.RankThree.PartTwo.Sec4.Res424Seven.cyc3,
      hoff 0 1 (by decide), hoff 0 2 (by decide), hoff 1 0 (by decide), hoff 1 2 (by decide),
      hoff 2 0 (by decide), hoff 2 1 (by decide)] using h
  have e10 : M 1 1 = M 0 0 := by
    have h := congrFun (congrFun hMC 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three, CFSG.RankThree.PartTwo.Sec4.Res424Seven.cyc3,
      hoff 0 1 (by decide), hoff 0 2 (by decide), hoff 1 0 (by decide), hoff 1 2 (by decide),
      hoff 2 0 (by decide), hoff 2 1 (by decide)] using h
  refine ⟨M 0 0, Matrix.ext fun i j => ?_⟩
  by_cases hij : i = j
  · subst hij
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    fin_cases i
    · rfl
    · exact e10
    · exact e02.symm
  · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
    exact hoff i j hij

end CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofU3Two

end
