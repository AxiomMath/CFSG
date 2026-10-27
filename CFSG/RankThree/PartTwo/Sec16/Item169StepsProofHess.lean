module

public import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofPComm
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
import CFSG.RankThree.PartTwo.KFacts.KSL3PiOrder3TypeC

public section

namespace CFSG.RankThree.PartTwo.Sec16.ProofHess

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

section Matrices

variable {K : Type} [Field K]

theorem not_cube_of_not_nine_dvd [Finite K] (h9 : ¬ 9 ∣ Nat.card K - 1) {ζ : K}
    (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) (μ : K) : μ ^ 3 ≠ ζ := by
  intro hμ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hμ
    rw [← hμ, zero_pow (by norm_num)] at hζ3
    exact zero_ne_one hζ3
  set u := Units.mk0 μ hμ0 with hu
  have hu9 : u ^ 9 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, show (9 : ℕ) = 3 * 3 from rfl,
      pow_mul, hμ, hζ3]
  have hu3 : u ^ 3 ≠ 1 := by
    intro h
    apply hζ1
    have h' := congrArg Units.val h
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, hμ] at h'
    exact h'
  have hord : orderOf u = 9 := by
    have hd : orderOf u ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one (by norm_num; exact hu9)
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    interval_cases k
    · exfalso
      rw [pow_zero, orderOf_eq_one_iff] at hk'
      exact hu3 (by rw [hk', one_pow])
    · exfalso
      rw [pow_one] at hk'
      exact hu3 (by rw [← hk']; exact pow_orderOf_eq_one u)
    · rw [hk']
      norm_num
  have hdvd : orderOf u ∣ Nat.card Kˣ := orderOf_dvd_natCard u
  rw [hord, Nat.card_units] at hdvd
  exact h9 hdvd

theorem tau_facts {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) : τ ≠ 0 ∧ τ ^ 2 ≠ 1 ∧ τ ≠ τ ^ 2 := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    calc τ = τ * τ ^ 2 := by rw [h, mul_one]
      _ = τ ^ 3 := by ring
      _ = 1 := hτ
  refine ⟨hτ0, hτ2, fun h => hτ1 ?_⟩
  have : τ * τ = τ * 1 := by rw [← sq, ← h, mul_one]
  exact mul_left_cancel₀ hτ0 this

theorem exists_normal_form_det_one {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (h3 : (3 : K) ≠ 0)
    {y : Matrix (Fin 3) (Fin 3) K} (hy : y ^ 3 = 1) (hdet : y.det = 1)
    (hys : ∀ c : K, y ≠ c • 1) :
    ∃ (P : Matrix (Fin 3) (Fin 3) K) (j : Fin 3), IsUnit P ∧
      (τ ^ (j : ℕ) • y) * P = P * diagonal ![τ, τ ^ 2, 1] := by
  obtain ⟨-, hτ2, -⟩ := tau_facts hτ hτ1
  obtain ⟨P, j, hP, hcase⟩ := exists_normal_form hτ hτ1 h3 hy hys
  refine ⟨P, j, hP, ?_⟩
  have hdetP : P.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det P).mp hP).ne_zero
  have hdj : (τ ^ (j : ℕ) • y).det = 1 := by
    rw [Matrix.det_smul, hdet, mul_one, Fintype.card_fin, ← pow_mul, mul_comm, pow_mul, hτ,
      one_pow]
  have key : ∀ d : Fin 3 → K, (τ ^ (j : ℕ) • y) * P = P * diagonal d →
      d 0 * d 1 * d 2 = 1 := by
    intro d h
    have h' := congrArg Matrix.det h
    rw [det_mul, det_mul, hdj, one_mul, det_diagonal, Fin.prod_univ_three] at h'
    have h'' : P.det * (d 0 * d 1 * d 2) = P.det * 1 := by rw [mul_one]; exact h'.symm
    exact mul_left_cancel₀ hdetP h''
  rcases hcase with h | h | h
  · exact h
  · exfalso
    have h' := key _ h
    change τ * 1 * 1 = 1 at h'
    rw [mul_one, mul_one] at h'
    exact hτ1 h'
  · exfalso
    have h' := key _ h
    change τ ^ 2 * 1 * 1 = 1 at h'
    rw [mul_one, mul_one] at h'
    exact hτ2 h'

theorem tau_vec_injective {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {i j : Fin 3} (hij : i ≠ j) :
    (![τ, τ ^ 2, 1] : Fin 3 → K) i ≠ ![τ, τ ^ 2, 1] j := by
  obtain ⟨-, hτ2, hττ2⟩ := tau_facts hτ hτ1
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem eq_diagonal_of_commute {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {M : Matrix (Fin 3) (Fin 3) K}
    (h : M * diagonal ![τ, τ ^ 2, 1] = diagonal ![τ, τ ^ 2, 1] * M) :
    M = diagonal fun i => M i i := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [entry_eq_zero_of_commute_diagonal h (tau_vec_injective hτ hτ1 hij),
      diagonal_apply_ne _ hij]

theorem exists_eq_smul_pow_of_diag {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {a b c : K}
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (habc : a * b * c = 1) :
    ∃ i : ℕ, diagonal ![a, b, c] = c • (diagonal ![τ, τ ^ 2, 1]) ^ i := by
  have hab0 : a * b ≠ 0 := left_ne_zero_of_mul_eq_one habc
  have ha0 : a ≠ 0 := left_ne_zero_of_mul hab0
  have hc0 : c ≠ 0 := right_ne_zero_of_mul_eq_one habc
  have hc3 : c ^ 3 = 1 := by
    have h := congrArg (· ^ 3) habc
    simp only [mul_pow, ha, hb, one_mul, one_pow] at h
    exact h
  have hbc' : b * c = a ^ 2 := by
    have h1 : a * (b * c) = a * a ^ 2 := by
      rw [← mul_assoc, habc]
      linear_combination -ha
    exact mul_left_cancel₀ ha0 h1
  obtain ⟨u, hu⟩ : ∃ u : K, u = a * c⁻¹ := ⟨_, rfl⟩
  have hu3 : u ^ 3 = 1 := by rw [hu, mul_pow, inv_pow, ha, hc3, inv_one, mul_one]
  have hua : a = c * u := by
    rw [hu]
    field_simp
  have hub : b = c * u ^ 2 := by
    rw [hu, mul_pow, inv_pow, ← hbc']
    field_simp
  have hdiag : diagonal ![a, b, c] = c • diagonal ![u, u ^ 2, 1] := by
    rw [← diagonal_smul]
    congr 1
    funext l
    fin_cases l
    · simpa using hua
    · simpa using hub
    · simp
  have hpow : ∀ i : ℕ, u = τ ^ i → diagonal ![u, u ^ 2, 1] = (diagonal ![τ, τ ^ 2, 1]) ^ i := by
    intro i hi
    rw [diagonal_pow, hi]
    congr 1
    funext l
    fin_cases l <;> simp [← pow_mul, mul_comm]
  rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 hu3 with h | h | h
  · exact ⟨0, by rw [hdiag, hpow 0 (by rw [h, pow_zero])]⟩
  · exact ⟨1, by rw [hdiag, hpow 1 (by rw [h, pow_one])]⟩
  · exact ⟨2, by rw [hdiag, hpow 2 h]⟩

theorem eq_of_heis {τ ζ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)
    {N : Matrix (Fin 3) (Fin 3) K} (hN : IsUnit N)
    (hDN : diagonal ![τ, τ ^ 2, 1] * N = ζ • (N * diagonal ![τ, τ ^ 2, 1]))
    {s : Fin 3 → K} (hsN : diagonal s * N = N * diagonal s) : s 0 = s 1 ∧ s 1 = s 2 := by
  obtain ⟨hτ0, hτ2, hττ2⟩ := tau_facts hτ hτ1
  have hdet : N.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det N).mp hN).ne_zero
  have e : ∀ i l, (diagonal ![τ, τ ^ 2, 1] * N) i l = (ζ • (N * diagonal ![τ, τ ^ 2, 1])) i l :=
    fun i l => by rw [hDN]
  have f : ∀ i l, (diagonal s * N) i l = (N * diagonal s) i l := fun i l => by rw [hsN]
  have aux : ∀ {X a b : K}, a ≠ b → a * X = b * X → X = 0 := fun {X a b} hab h => by
    have h' : (a - b) * X = 0 := by rw [sub_mul, h, sub_self]
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hab)
  have can : ∀ {X a b : K}, X ≠ 0 → a * X = X * b → a = b := fun {X a b} hX h => by
    have h' : X * a = X * b := by rw [mul_comm, h]
    exact mul_left_cancel₀ hX h'
  have h4 : τ ^ 4 = τ := by rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, hτ, one_mul, pow_one]
  rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 hζ3 with hζ' | hζ' | hζ' <;> subst ζ
  · exact absurd rfl hζ1
  ·
    have e00 := e 0 0
    have e01 := e 0 1
    have e11 := e 1 1
    have e12 := e 1 2
    have e20 := e 2 0
    have e22 := e 2 2
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at e00 e01 e11 e12 e20 e22
    have n00 : N 0 0 = 0 := aux (a := τ) (b := τ * τ) (by rw [← sq]; exact hττ2)
      (by linear_combination e00)
    have n01 : N 0 1 = 0 := aux (a := τ) (b := τ * τ ^ 2) (by
        rw [show τ * τ ^ 2 = τ ^ 3 by ring, hτ]; exact hτ1)
      (by linear_combination e01)
    have n11 : N 1 1 = 0 := aux (a := τ ^ 2) (b := τ * τ ^ 2) (by
        rw [show τ * τ ^ 2 = τ ^ 3 by ring, hτ]; exact hτ2)
      (by linear_combination e11)
    have n12 : N 1 2 = 0 := aux (a := τ ^ 2) (b := τ) (Ne.symm hττ2) (by linear_combination e12)
    have n20 : N 2 0 = 0 := aux (a := 1) (b := τ * τ) (by
        rw [← sq]; exact Ne.symm hτ2) (by linear_combination e20)
    have n22 : N 2 2 = 0 := aux (a := 1) (b := τ) (Ne.symm hτ1) (by linear_combination e22)
    have hd : N.det = N 0 2 * N 1 0 * N 2 1 := by
      rw [det_fin_three, n00, n01, n11, n12, n20, n22]
      ring
    rw [hd] at hdet
    have a02 : N 0 2 ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hdet)
    have a10 : N 1 0 ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hdet)
    have a21 : N 2 1 ≠ 0 := right_ne_zero_of_mul hdet
    have f02 := f 0 2
    have f10 := f 1 0
    have f21 := f 2 1
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at f02 f10 f21
    have s02 := can a02 f02
    have s10 := can a10 f10
    have s21 := can a21 f21
    exact ⟨s10.symm, s21.symm⟩
  ·
    have e00 := e 0 0
    have e02 := e 0 2
    have e10 := e 1 0
    have e11 := e 1 1
    have e21 := e 2 1
    have e22 := e 2 2
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at e00 e02 e10 e11 e21 e22
    have n00 : N 0 0 = 0 := aux (a := τ) (b := τ ^ 2 * τ) (by
        rw [show τ ^ 2 * τ = τ ^ 3 by ring, hτ]; exact hτ1) (by linear_combination e00)
    have n02 : N 0 2 = 0 := aux (a := τ) (b := τ ^ 2) hττ2 (by linear_combination e02)
    have n10 : N 1 0 = 0 := aux (a := τ ^ 2) (b := τ ^ 2 * τ) (by
        rw [show τ ^ 2 * τ = τ ^ 3 by ring, hτ]; exact hτ2) (by linear_combination e10)
    have n11 : N 1 1 = 0 := aux (a := τ ^ 2) (b := τ ^ 2 * τ ^ 2) (by
        rw [show τ ^ 2 * τ ^ 2 = τ ^ 4 by ring, h4]; exact Ne.symm hττ2)
      (by linear_combination e11)
    have n21 : N 2 1 = 0 := aux (a := 1) (b := τ ^ 2 * τ ^ 2) (by
        rw [show τ ^ 2 * τ ^ 2 = τ ^ 4 by ring, h4]; exact Ne.symm hτ1)
      (by linear_combination e21)
    have n22 : N 2 2 = 0 := aux (a := 1) (b := τ ^ 2) (Ne.symm hτ2) (by linear_combination e22)
    have hd : N.det = N 0 1 * N 1 2 * N 2 0 := by
      rw [det_fin_three, n00, n02, n10, n11, n21, n22]
      ring
    rw [hd] at hdet
    have a01 : N 0 1 ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hdet)
    have a12 : N 1 2 ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hdet)
    have a20 : N 2 0 ≠ 0 := right_ne_zero_of_mul hdet
    have f01 := f 0 1
    have f12 := f 1 2
    have f20 := f 2 0
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at f01 f12 f20
    have s01 := can a01 f01
    have s12 := can a12 f12
    exact ⟨s01, s12⟩

end Matrices

section Conj

variable {K : Type} [Field K]

theorem inv_mul_eq {P Q Y D : Matrix (Fin 3) (Fin 3) K} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hY : Y * P = P * D) : Q * Y = D * Q := by
  calc Q * Y = Q * Y * (P * Q) := by rw [hPQ, Matrix.mul_one]
    _ = Q * (Y * P) * Q := by simp only [Matrix.mul_assoc]
    _ = Q * (P * D) * Q := by rw [hY]
    _ = (Q * P) * D * Q := by simp only [Matrix.mul_assoc]
    _ = D * Q := by rw [hQP, Matrix.one_mul]

theorem conj_commute {P Q Y D M : Matrix (Fin 3) (Fin 3) K} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hY : Y * P = P * D) (hM : M * Y = Y * M) : (Q * M * P) * D = D * (Q * M * P) := by
  calc Q * M * P * D = Q * M * (P * D) := by simp only [Matrix.mul_assoc]
    _ = Q * M * (Y * P) := by rw [hY]
    _ = Q * (M * Y) * P := by simp only [Matrix.mul_assoc]
    _ = Q * (Y * M) * P := by rw [hM]
    _ = (Q * Y) * M * P := by simp only [Matrix.mul_assoc]
    _ = D * Q * M * P := by rw [inv_mul_eq hPQ hQP hY]
    _ = D * (Q * M * P) := by simp only [Matrix.mul_assoc]

theorem conj_heis {P Q Y D M : Matrix (Fin 3) (Fin 3) K} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hY : Y * P = P * D) {ζ : K} (hM : Y * M = ζ • (M * Y)) :
    D * (Q * M * P) = ζ • ((Q * M * P) * D) := by
  calc D * (Q * M * P) = (D * Q) * M * P := by simp only [Matrix.mul_assoc]
    _ = Q * Y * M * P := by rw [inv_mul_eq hPQ hQP hY]
    _ = Q * (Y * M) * P := by simp only [Matrix.mul_assoc]
    _ = Q * (ζ • (M * Y)) * P := by rw [hM]
    _ = ζ • (Q * M * (Y * P)) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
        simp only [Matrix.mul_assoc]
    _ = ζ • (Q * M * (P * D)) := by rw [hY]
    _ = ζ • ((Q * M * P) * D) := by simp only [Matrix.mul_assoc]

theorem conj_pow {P Q : Matrix (Fin 3) (Fin 3) K} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (M : Matrix (Fin 3) (Fin 3) K) (n : ℕ) : (Q * M * P) ^ n = Q * M ^ n * P := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hQP]
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    calc Q * M ^ n * P * (Q * M * P) = Q * M ^ n * (P * Q) * M * P := by
          simp only [Matrix.mul_assoc]
      _ = Q * (M ^ n * M) * P := by rw [hPQ, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem conj_mul {P Q : Matrix (Fin 3) (Fin 3) K} (hPQ : P * Q = 1)
    (M M' : Matrix (Fin 3) (Fin 3) K) : (Q * M * P) * (Q * M' * P) = Q * (M * M') * P := by
  calc Q * M * P * (Q * M' * P) = Q * M * (P * Q) * M' * P := by simp only [Matrix.mul_assoc]
    _ = Q * (M * M') * P := by rw [hPQ, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem unconj {P Q : Matrix (Fin 3) (Fin 3) K} (hPQ : P * Q = 1) (M : Matrix (Fin 3) (Fin 3) K) :
    P * (Q * M * P) * Q = M := by
  calc P * (Q * M * P) * Q = (P * Q) * M * (P * Q) := by simp only [Matrix.mul_assoc]
    _ = M := by rw [hPQ, Matrix.one_mul, Matrix.mul_one]

theorem det_conj {P Q : Matrix (Fin 3) (Fin 3) K} (hQP : Q * P = 1)
    (M : Matrix (Fin 3) (Fin 3) K) : (Q * M * P).det = M.det := by
  have h : Q.det * P.det = 1 := by rw [← det_mul, hQP, det_one]
  rw [det_mul, det_mul, mul_comm Q.det, mul_assoc, h, mul_one]

end Conj

section Lifts

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem pow_three_eq_one_of_lift (hK : PiField π p f K) (h9 : ¬ 9 ∣ Nat.card K - 1)
    {y : GL (Fin 3) K} (hy : y ∈ slPi π 3 (p ^ f) K) (hy3 : ProjGenLinGroup.mk y ^ 3 = 1) :
    y ^ 3 = 1 := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hs : y ^ 3 ∈ StatedScalars (Fin 3) K := by
    rw [← KFacts.mk_eq_one_iff_mem_statedScalars', map_pow]
    exact hy3
  obtain ⟨ε, hε⟩ := hs
  have hdet : (y : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hy).2
  have hε3 : (ε : K) ^ 3 = 1 := by
    have h1 := congrArg (fun z : GL (Fin 3) K => (z : Matrix (Fin 3) (Fin 3) K).det) hε
    simp only [KFacts.det_scalar_eq, Units.val_pow_eq_pow_val, det_pow, hdet, one_pow] at h1
    exact h1
  by_cases hε1 : (ε : K) = 1
  · have hε1' : ε = 1 := Units.ext hε1
    rw [← hε, hε1', map_one]
  · exfalso
    have hcube : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = (ε : K) • 1 := by
      rw [← Units.val_pow_eq_pow_val, ← hε, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.smul_one_eq_diagonal]
    have h := det_eq_of_cube (not_cube_of_not_nine_dvd h9 hε3 hε1) hcube
    rw [hdet] at h
    exact hε1 h.symm

theorem exists_lift_pow_eq_one (hK : PiField π p f K) {x : ProjGenLinGroup (Fin 3) K}
    (hx : x ∈ projImage (slPi π 3 (p ^ f) K)) (hm : Nat.Coprime 3 (orderOf x)) :
    ∃ s ∈ slPi π 3 (p ^ f) K, ProjGenLinGroup.mk s = x ∧ s ^ orderOf x = 1 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨s₀, hs₀, rfl⟩ := hx
  set m := orderOf (ProjGenLinGroup.mk s₀) with hmdef
  have hsc : s₀ ^ m ∈ StatedScalars (Fin 3) K := by
    rw [← KFacts.mk_eq_one_iff_mem_statedScalars', map_pow, hmdef, pow_orderOf_eq_one]
  obtain ⟨ε, hε⟩ := hsc
  have hε3 : ε ^ 3 = 1 :=
    pow_three_eq_one_of_scalar_mem_slPi hπ (hε ▸ Subgroup.pow_mem _ hs₀ m)
  have h3 : (s₀ ^ m) ^ 3 = 1 := by rw [← hε, ← map_pow, hε3, map_one]
  by_cases hm1 : m = 1
  · refine ⟨1, one_mem _, ?_, by rw [one_pow]⟩
    rw [map_one]
    exact (orderOf_eq_one_iff.mp hm1).symm
  have hm0 : m ≠ 0 := by
    rintro h0
    rw [h0] at hm
    norm_num at hm
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hm (by omega)
  refine ⟨s₀ ^ (3 * k), Subgroup.pow_mem _ hs₀ _, ?_, ?_⟩
  · rw [map_pow, ← pow_mod_orderOf, ← hmdef, hk, pow_one]
  · rw [← pow_mul, show 3 * k * m = m * 3 * k by ring, pow_mul, pow_mul, h3, one_pow]

theorem commute_of_mk_commute (hK : PiField π p f K) {s y : GL (Fin 3) K}
    (hs : s ∈ slPi π 3 (p ^ f) K) (hy : y ∈ slPi π 3 (p ^ f) K)
    (hc : ProjGenLinGroup.mk y * ProjGenLinGroup.mk s =
      ProjGenLinGroup.mk s * ProjGenLinGroup.mk y)
    {m : ℕ} (hm : Nat.Coprime m 3) (hsm : s ^ m = 1) : s * y = y * s := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  set l := s * y * s⁻¹ * y⁻¹ with hl
  have hlS : l ∈ slPi π 3 (p ^ f) K :=
    mul_mem (mul_mem (mul_mem hs hy) (inv_mem hs)) (inv_mem hy)
  have hlsc : l ∈ StatedScalars (Fin 3) K := by
    rw [← KFacts.mk_eq_one_iff_mem_statedScalars', hl, map_mul, map_mul, map_mul, map_inv,
      map_inv, ← hc]
    group
  obtain ⟨ζ, hζ⟩ := hlsc
  have hζ3 : ζ ^ 3 = 1 := pow_three_eq_one_of_scalar_mem_slPi hπ (hζ ▸ hlS)
  have hcen : ∀ g : GL (Fin 3) K, g * l = l * g := fun g => by
    rw [← hζ]
    exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ g).eq
  have hsy : s * y = l * (y * s) := by
    rw [hl]
    group
  have hpow : ∀ n : ℕ, s ^ n * y = l ^ n * (y * s ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc s ^ (n + 1) * y = s ^ n * (s * y) := by rw [pow_succ, mul_assoc]
        _ = s ^ n * (l * (y * s)) := by rw [hsy]
        _ = l * (s ^ n * y) * s := by rw [← mul_assoc, hcen (s ^ n)]; group
        _ = l * (l ^ n * (y * s ^ n)) * s := by rw [ih]
        _ = l ^ (n + 1) * (y * s ^ (n + 1)) := by rw [pow_succ', pow_succ]; group
  have hlm : l ^ m = 1 := by
    have h := hpow m
    rw [hsm, one_mul, mul_one] at h
    have h' : l ^ m * y = 1 * y := by rw [one_mul]; exact h.symm
    exact mul_right_cancel h'
  have hl3 : l ^ 3 = 1 := by rw [← hζ, ← map_pow, hζ3, map_one]
  have hl1 : l = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hm
    (orderOf_dvd_of_pow_eq_one hlm) (orderOf_dvd_of_pow_eq_one hl3))
  rw [hsy, hl1, one_mul]

end Lifts

section Main

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_two_of_card_nine {X : Type*} [Group X] {E : Subgroup X}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) :
    ∃ e₁ ∈ E, e₁ ≠ 1 ∧ ∃ e₂ ∈ E, e₂ ∉ Subgroup.zpowers e₁ := by
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hE9]; norm_num)
  have hEnt : ∃ e₁ ∈ E, e₁ ≠ 1 := by
    by_contra hall
    push Not at hall
    have hbot : E = ⊥ := eq_bot_iff.mpr fun e he => (Subgroup.mem_bot).mpr (hall e he)
    rw [hbot, Subgroup.card_bot] at hE9
    norm_num at hE9
  obtain ⟨e₁, he₁E, he₁1⟩ := hEnt
  refine ⟨e₁, he₁E, he₁1, ?_⟩
  by_contra hall
  push Not at hall
  have hle : E ≤ Subgroup.zpowers e₁ := fun e he => hall e he
  have hz3 : Nat.card (Subgroup.zpowers e₁) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hE.2 e₁ he₁E))
  have : Finite (Subgroup.zpowers e₁) := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_zpowers]
    exact (orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨3, by norm_num, hE.2 e₁ he₁E⟩)).ne')
  have hcard := Subgroup.card_le_of_le hle
  omega

theorem eq_one_of_mem_centralizer (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : ¬ 9 ∣ Nat.card K - 1) {E : Subgroup (ProjGenLinGroup (Fin 3) K)}
    (hES : E ≤ projImage (slPi π 3 (p ^ f) K)) (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) {x : ProjGenLinGroup (Fin 3) K}
    (hxS : x ∈ projImage (slPi π 3 (p ^ f) K)) (hxE : ∀ e ∈ E, e * x = x * e)
    (hx3 : Nat.Coprime 3 (orderOf x)) : x = 1 := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨e₁, he₁E, he₁1, e₂, he₂E, he₂⟩ := exists_two_of_card_nine hE hE9
  have hcomm_bar : e₁ * e₂ = e₂ * e₁ :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨e₁, he₁E⟩ ⟨e₂, he₂E⟩)
  obtain ⟨y₁, hy₁S, rfl⟩ := hES he₁E
  obtain ⟨y₂, hy₂S, rfl⟩ := hES he₂E
  obtain ⟨s, hsS, rfl, hsm⟩ := exists_lift_pow_eq_one hK hxS hx3
  have hy₁3 : y₁ ^ 3 = 1 := pow_three_eq_one_of_lift hK h9 hy₁S (hE.2 _ he₁E)
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
    have hy₂3 : y₂ ^ 3 = 1 := pow_three_eq_one_of_lift hK h9 hy₂S (hE.2 _ he₂E)
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
  have hwS : w ∈ slPi π 3 (p ^ f) K :=
    mul_mem (mul_mem (mul_mem hy₁S hy₂S) (inv_mem hy₁S)) (inv_mem hy₂S)
  have hwsc : w ∈ StatedScalars (Fin 3) K := by
    rw [← KFacts.mk_eq_one_iff_mem_statedScalars', hw, map_mul, map_mul, map_mul, map_inv,
      map_inv, hcomm_bar]
    group
  obtain ⟨ζ, hζ⟩ := hwsc
  have hζ3 : (ζ : K) ^ 3 = 1 := by
    have h := congrArg Units.val (pow_three_eq_one_of_scalar_mem_slPi hπ (hζ ▸ hwS))
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h
  have hζ1 : (ζ : K) ≠ 1 := by
    intro h1
    apply hnc
    have hw1 : w = 1 := by rw [← hζ, show ζ = 1 from Units.ext h1, map_one]
    calc y₁ * y₂ = w * (y₂ * y₁) := by rw [hw]; group
      _ = y₂ * y₁ := by rw [hw1, one_mul]
  have hYN : Y * (y₂ : Matrix (Fin 3) (Fin 3) K) =
      (ζ : K) • ((y₂ : Matrix (Fin 3) (Fin 3) K) * Y) := by
    have h1 : y₁ * y₂ = GeneralLinearGroup.scalar (Fin 3) ζ * (y₂ * y₁) := by
      rw [hζ, hw]
      group
    have h2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h1
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h2
    rw [hY, Matrix.smul_mul, Matrix.mul_smul, h2, ← Matrix.smul_eq_diagonal_mul, smul_comm]
  have hDN : D * N = (ζ : K) • (N * D) := conj_heis hPQ hQP hPD hYN
  have hNu : IsUnit N := (Matrix.isUnit_iff_isUnit_det N).mpr (by rw [hNdet]; exact isUnit_one)
  have hm : Nat.Coprime (orderOf (ProjGenLinGroup.mk s)) 3 := hx3.symm
  have hs₁ := commute_of_mk_commute hK hsS hy₁S (hxE _ he₁E) hm hsm
  have hs₂ := commute_of_mk_commute hK hsS hy₂S (hxE _ he₂E) hm hsm
  have hs₁m : (s : Matrix (Fin 3) (Fin 3) K) * y₁ = y₁ * s := by
    have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hs₁
    simpa only [Units.val_mul] using h
  have hs₂m : (s : Matrix (Fin 3) (Fin 3) K) * y₂ = y₂ * s := by
    have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hs₂
    simpa only [Units.val_mul] using h
  set S' := Q * (s : Matrix (Fin 3) (Fin 3) K) * P with hS'
  have hSD : S' * D = D * S' := conj_commute hPQ hQP hPD (hYc _ hs₁m)
  have hSdiag := eq_diagonal_of_commute hτ hτ1 hSD
  have hSN : S' * N = N * S' := by rw [hS', hN, conj_mul hPQ, conj_mul hPQ, hs₂m]
  rw [hSdiag] at hSN
  obtain ⟨h01, h12⟩ := eq_of_heis hτ hτ1 hζ3 hζ1 hNu hDN hSN
  obtain ⟨σ, hσ⟩ : ∃ σ : K, σ = S' 0 0 := ⟨_, rfl⟩
  have hS'eq : S' = σ • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [hσ, hSdiag, Matrix.smul_one_eq_diagonal]
    congr 1
    funext l
    fin_cases l
    · rfl
    · exact h01.symm
    · exact (h01.trans h12).symm
  have hseq : (s : Matrix (Fin 3) (Fin 3) K) = σ • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [← unconj hPQ (s : Matrix (Fin 3) (Fin 3) K), ← hS', hS'eq, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hPQ]
  have hs0 : σ ≠ 0 := by
    intro h0
    have hdets : (s : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hsS).2
    rw [hseq, h0, zero_smul, det_zero] at hdets
    exact zero_ne_one hdets
  exact KFacts.mk_eq_one_iff_mem_statedScalars'.mpr (mem_statedScalars_of_eq_smul hseq hs0)

end Main

end CFSG.RankThree.PartTwo.Sec16.ProofHess

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec16.ProofHess
  CFSG.RankThree.PartTwo.Sec16.ProofPComm Matrix
open CFSG.Assembly.RankThreeEven (projImage)

theorem not_nine_dvd_card_sub_one {π : Bool} {n : ℕ} {K : Type} [Field K]
    (hK : PiField π 2 n K) (h9 : ¬ (2 ^ n % 9 = 1 ∨ 2 ^ n % 9 = 8)) :
    ¬ 9 ∣ Nat.card K - 1 := by
  rw [hK.card]
  have hr : 2 ^ n % 9 < 9 := Nat.mod_lt _ (by norm_num)
  have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  cases π
  · change ¬ 9 ∣ (2 ^ n) ^ 2 - 1
    intro hd
    have hq2 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h1 : (2 ^ n) ^ 2 % 9 = 1 := by omega
    rw [Nat.pow_mod] at h1
    have key : ∀ r < 9, r ^ 2 % 9 = 1 → r = 1 ∨ r = 8 := by decide
    exact h9 (key _ hr h1)
  · change ¬ 9 ∣ 2 ^ n - 1
    intro hd
    exact h9 (Or.inl (by omega))

theorem kS169HessCent : KS169HessCent := by
  intro X _ _ n hn hiso h9 E hE hE9
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := exists_projImage_model hn hiso
  have h9K := not_nine_dvd_card_sub_one hK h9
  intro g
  have hg0 : orderOf (g : X) ≠ 0 := (orderOf_pos (g : X)).ne'
  obtain ⟨a, m, hm3, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd hg0 3 (by norm_num)
  refine ⟨a, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  set h := (g : X) ^ 3 ^ a with hh
  have hordh : orderOf h = m := by
    rw [hh, orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) (by rw [hord]; exact Dvd.intro m rfl),
      hord]
    exact Nat.mul_div_cancel_left m (pow_pos (by norm_num) a)
  have hhC : h ∈ Subgroup.centralizer (E : Set X) := Subgroup.pow_mem _ g.2 _
  set S := projImage (slPi π 3 (2 ^ n) K) with hS
  set E' : Subgroup (ProjGenLinGroup (Fin 3) K) := (E.map φ.toMonoidHom).map S.subtype with hE'
  have hES : E' ≤ S := Subgroup.map_subtype_le _
  have hE'a : CFSG.Assembly.IsElemAbelian 3 E' :=
    ProofPComm.isElemAbelian_map (ProofPComm.isElemAbelian_map hE _) _
  have hE'9 : Nat.card E' = 9 := by
    rw [hE', Subgroup.card_map_of_injective S.subtype_injective,
      Subgroup.card_map_of_injective φ.injective, hE9]
  have hxS : ((φ h : S) : ProjGenLinGroup (Fin 3) K) ∈ S := (φ h).2
  have hxE : ∀ e ∈ E', e * ((φ h : S) : ProjGenLinGroup (Fin 3) K) =
      ((φ h : S) : ProjGenLinGroup (Fin 3) K) * e := by
    rintro _ ⟨_, ⟨e₀, he₀, rfl⟩, rfl⟩
    have hc := Subgroup.mem_centralizer_iff.mp hhC e₀ he₀
    have h1 := congrArg (fun z : X => ((φ z : S) : ProjGenLinGroup (Fin 3) K)) hc
    simpa only [map_mul, Subgroup.coe_mul, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
      using h1
  have hx3 : Nat.Coprime 3 (orderOf ((φ h : S) : ProjGenLinGroup (Fin 3) K)) := by
    have hφo := orderOf_injective φ.toMonoidHom φ.injective h
    simp only [MulEquiv.coe_toMonoidHom] at hφo
    rw [Subgroup.orderOf_coe, hφo, hordh]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3
  have hx1 := eq_one_of_mem_centralizer hK hq h9K hES hE'a hE'9 hxS hxE hx3
  have hφ : φ h = 1 := Subtype.ext hx1
  exact (MulEquiv.map_eq_one_iff φ).mp hφ

theorem step169PComm_of_item138N
    (h135 : Item135Simple) (h138 : Item138N) : Step169PComm :=
  step169PComm_of h135 h138 kS169HessCent

end CFSG.RankThree.PartTwo.Sec16
