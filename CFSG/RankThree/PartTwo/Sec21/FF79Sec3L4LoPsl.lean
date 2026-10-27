module

public import CFSG.Open.StatedAPI

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.Open CFSG.Open.StatedAPI Matrix

variable {K : Type} [Field K]

theorem toGL_mem_statedSL (S : SpecialLinearGroup (Fin 2) K) :
    (SpecialLinearGroup.toGL S : GL (Fin 2) K) ∈ StatedSL 2 K := by
  rw [statedSL_eq_range_toGL]; exact ⟨S, rfl⟩

noncomputable def pslMk : SpecialLinearGroup (Fin 2) K →* StatedProj (StatedSL 2 K) :=
  (QuotientGroup.mk' _).comp (SpecialLinearGroup.toGL.codRestrict (StatedSL 2 K) toGL_mem_statedSL)

theorem pslMk_eq_one_iff (S : SpecialLinearGroup (Fin 2) K) :
    pslMk S = 1 ↔ ∃ c : Kˣ, (S : Matrix (Fin 2) (Fin 2) K) = (c : K) • (1 : Matrix _ _ K) := by
  unfold pslMk
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) hc
    simp only [GeneralLinearGroup.coe_scalar] at this
    simp only [MonoidHom.codRestrict_apply] at this
    have h2 : (S : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) (c : K) := this.symm
    rw [h2]
    simp [Matrix.smul_one_eq_diagonal]
  · rintro ⟨c, hc⟩
    refine ⟨c, Units.ext ?_⟩
    simp only [GeneralLinearGroup.coe_scalar, MonoidHom.codRestrict_apply]
    show Matrix.scalar (Fin 2) (c : K) = (S : Matrix (Fin 2) (Fin 2) K)
    rw [hc]
    simp [Matrix.smul_one_eq_diagonal]

theorem exists_orderOf_nine_psl (S : SpecialLinearGroup (Fin 2) K) (c : Kˣ)
    (h9 : ((S ^ 9 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (c : K) • (1 : Matrix _ _ K))
    (h3 : ∀ d : K, ((S ^ 3 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ≠
      d • (1 : Matrix _ _ K)) :
    ∃ g : StatedProj (StatedSL 2 K), orderOf g = 9 := by
  refine ⟨pslMk S, ?_⟩
  have e : (9 : ℕ) = 3 ^ (1 + 1) := by norm_num
  rw [e]
  refine orderOf_eq_prime_pow (p := 3) (n := 1) ?_ ?_
  · rw [pow_one, ← map_pow]
    intro h
    obtain ⟨d, hd⟩ := (pslMk_eq_one_iff _).1 h
    exact h3 d hd
  · rw [← map_pow, show 3 ^ (1 + 1) = 9 by norm_num]
    exact (pslMk_eq_one_iff _).2 ⟨c, h9⟩

theorem exists_orderOf_nine_card64 [Finite K] (hK : Nat.card K = 64) :
    ∃ g : StatedProj (StatedSL 2 K), orderOf g = 9 := by
  have hcyc : IsCyclic Kˣ := inferInstance
  have hcard : Nat.card Kˣ = 63 := by
    rw [Nat.card_units, hK]
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [hcard] at hγ
  set ω : Kˣ := γ ^ 7 with hω
  have hωo : orderOf ω = 9 := by
    rw [hω, orderOf_pow' _ (by norm_num), hγ]; norm_num
  have hdet : (Matrix.diagonal ![(ω : K), ((ω⁻¹ : Kˣ) : K)]).det = 1 := by
    simp [Matrix.det_diagonal, Fin.prod_univ_two]
  let S : SpecialLinearGroup (Fin 2) K := ⟨Matrix.diagonal ![(ω : K), ((ω⁻¹ : Kˣ) : K)], hdet⟩
  have hpow : ∀ n : ℕ, ((S ^ n : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal ![((ω ^ n : Kˣ) : K), (((ω ^ n)⁻¹ : Kˣ) : K)] := by
    intro n
    induction n with
    | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
    | succ n ih =>
      rw [pow_succ]
      have ih' : (S ^ n).1 = Matrix.diagonal ![((ω ^ n : Kˣ) : K), (((ω ^ n)⁻¹ : Kˣ) : K)] := ih
      show (S ^ n).1 * S.1 = _
      rw [ih']
      show Matrix.diagonal _ * Matrix.diagonal ![(ω : K), ((ω⁻¹ : Kˣ) : K)] = _
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      ext i
      fin_cases i <;> simp [pow_succ, mul_comm]
  refine exists_orderOf_nine_psl S 1 ?_ ?_
  · rw [hpow, show (9 : ℕ) = orderOf ω from hωo.symm, pow_orderOf_eq_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro d hd
    rw [hpow] at hd
    have h0 := congrFun (congrFun hd 0) 0
    have h1 := congrFun (congrFun hd 1) 1
    simp at h0 h1
    have h2 : ((ω : K) ^ 3) * ((ω : K) ^ 3) = 1 := by
      have hne : ((ω : K) ^ 3) ≠ 0 := pow_ne_zero _ ω.ne_zero
      calc ((ω : K) ^ 3) * ((ω : K) ^ 3) = ((ω : K) ^ 3) * ((↑ω ^ 3)⁻¹) := by rw [h1, ← h0]
        _ = 1 := mul_inv_cancel₀ hne
    have h3 : ω ^ 6 = 1 := by
      apply Units.ext
      push_cast
      rw [show (6 : ℕ) = 3 + 3 by norm_num, pow_add]
      exact h2
    have := orderOf_dvd_of_pow_eq_one h3
    rw [hωo] at this
    omega

theorem zmod5_cubic_ne : ∀ y : ZMod 5, y ^ 3 + 2 * y + 4 ≠ 0 := by decide

theorem exists_root_cubic125 (K : Type) [Field K] [Finite K] (hK : Nat.card K = 125) :
    ∃ t : K, t ^ 3 + 2 * t + 4 = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let f : Polynomial (ZMod 5) := Polynomial.X ^ 3 + Polynomial.C 2 * Polynomial.X +
    Polynomial.C 4
  have hdeg : f.natDegree = 3 := by unfold f; compute_degree!
  have hirr : Irreducible f := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [hdeg]; simp
    · intro x hx
      unfold f at hx
      simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_mul, Polynomial.eval_C] at hx
      exact zmod5_cubic_ne x hx
  haveI : Fact (Irreducible f) := ⟨hirr⟩
  have hf0 : f ≠ 0 := hirr.ne_zero
  haveI : Module.Finite (ZMod 5) (AdjoinRoot f) := (AdjoinRoot.powerBasis hf0).finite
  haveI : Finite (AdjoinRoot f) := Module.finite_of_finite (ZMod 5)
  have hcard : Nat.card (AdjoinRoot f) = 125 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 5), Nat.card_zmod]
    have := (AdjoinRoot.powerBasis hf0).finrank
    rw [AdjoinRoot.powerBasis_dim, hdeg] at this
    rw [this]; norm_num
  letI := Fintype.ofFinite K
  letI := Fintype.ofFinite (AdjoinRoot f)
  have e : AdjoinRoot f ≃+* K := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hcard])
  refine ⟨e (AdjoinRoot.root f), ?_⟩
  have h := AdjoinRoot.eval₂_root f
  simp only [f, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at h
  have h2 := congrArg e h
  simp only [map_add, map_mul, map_pow, map_ofNat, map_zero] at h2
  exact h2

theorem charP_five_of_card125 (K : Type) [Field K] [Finite K] (hK : Nat.card K = 125) :
    CharP K 5 := by
  obtain ⟨p, hpc⟩ := CharP.exists K
  letI := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K p
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : p ∣ 5 ^ 3 := by
    have : p ∣ p ^ (n : ℕ) := dvd_pow_self p n.ne_zero
    rw [← hn, ← Nat.card_eq_fintype_card, hK] at this
    simpa using this
  have h2 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (hp.dvd_of_dvd_pow h1)
  rw [h2] at hpc
  exact hpc

theorem mat2_sq (M : Matrix (Fin 2) (Fin 2) K) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem coe_pow_three (T : SpecialLinearGroup (Fin 2) K) :
    ((T ^ 3 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (T : Matrix (Fin 2) (Fin 2) K) * (T : Matrix (Fin 2) (Fin 2) K) *
        (T : Matrix (Fin 2) (Fin 2) K) := by
  have e : T ^ 3 = T * T * T := by simp [pow_succ]
  rw [e]
  rfl

theorem exists_orderOf_nine_card125 [Finite K] (hK : Nat.card K = 125) :
    ∃ g : StatedProj (StatedSL 2 K), orderOf g = 9 := by
  haveI := charP_five_of_card125 K hK
  obtain ⟨t, ht⟩ := exists_root_cubic125 K hK
  have h5 : (5 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 5
  have h3 : (3 : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K 5 3).1 (by exact_mod_cast h)
    omega
  have hτ : t ^ 3 - 3 * t = 1 := by linear_combination ht - (t + 1) * h5
  have hdet : (!![0, -1; 1, t] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    simp [Matrix.det_fin_two]
  let S : SpecialLinearGroup (Fin 2) K := ⟨!![0, -1; 1, t], hdet⟩
  have hS3 : ((S ^ 3 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![-t, 1 - t ^ 2; t ^ 2 - 1, t ^ 3 - 2 * t] := by
    rw [coe_pow_three]
    show (!![0, -1; 1, t] * !![0, -1; 1, t] * !![0, -1; 1, t] : Matrix (Fin 2) (Fin 2) K) = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  refine exists_orderOf_nine_psl S (-1) ?_ ?_
  · have e9 : S ^ 9 = (S ^ 3) ^ 3 := by rw [← pow_mul]
    rw [e9, coe_pow_three]
    set N : Matrix (Fin 2) (Fin 2) K := ((S ^ 3 : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) with hN
    have hdetN : N.det = 1 := (S ^ 3).2
    have htr : N.trace = 1 := by
      rw [hS3, Matrix.trace_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
      linear_combination hτ
    have hsq : N * N = N - 1 := by
      rw [mat2_sq N, hdetN, htr]
      simp
    calc N * N * N = (N - 1) * N := by rw [hsq]
      _ = N * N - N := by rw [sub_mul, one_mul]
      _ = ((-1 : Kˣ) : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
        rw [hsq]; simp
  · intro d hd
    rw [hS3] at hd
    have e1 := congrFun (congrFun hd 0) 1
    have e2 := congrFun (congrFun hd 0) 0
    simp at e1 e2
    have e1' : t ^ 2 = 1 := by linear_combination -e1
    have e3 : -2 * t - 1 = 0 := by linear_combination hτ - t * e1'
    exact h3 (by linear_combination (-(2 * t - 1)) * e3 - 4 * e1')

end CFSG.RankThree.PartTwo.Sec21.FF79
