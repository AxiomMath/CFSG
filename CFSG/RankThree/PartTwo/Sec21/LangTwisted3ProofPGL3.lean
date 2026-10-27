module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofShift
public import CFSG.RankThree.PartTwo.Sec21.LangTwisted3ProofPGL3Lin
public import CFSG.RankThree.PartOne.KF.UnitaryDiag

public section

namespace CFSG.RankThree.PartTwo.Sec8.LangTwisted3Proof

open Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem charP_two_of_piField {π : Bool} {m : ℕ} (hF : Sec4.PiField π 2 m K) : CharP K 2 := by
  have : Finite K := hF.finite
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := hF.card
  cases π
  · exact charP_of_card_eq_prime_pow (f := m * 2)
      (by rw [← Nat.card_eq_fintype_card, hc, Sec4.piCard, Bool.cond_false, ← pow_mul])
  · exact charP_of_card_eq_prime_pow (f := m)
      (by rw [← Nat.card_eq_fintype_card, hc, Sec4.piCard, Bool.cond_true])

theorem three_dvd_card_sub_one {π : Bool} {m : ℕ} (hF : Sec4.PiField π 2 m K)
    (hmod : Sec4.ModThree π (2 ^ m)) : 3 ∣ Nat.card K - 1 := by
  have hc := hF.card
  have hpos : 0 < 2 ^ m := by positivity
  cases π
  · rw [hc, Sec4.piCard, Bool.cond_false]
    have h : (2 ^ m) % 3 = 2 := hmod
    have h2 : ((2 ^ m) ^ 2) % 3 = 1 := by rw [Nat.pow_mod, h]
    have : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ hpos
    omega
  · rw [hc, Sec4.piCard, Bool.cond_true]
    have h : (2 ^ m) % 3 = 1 := hmod
    omega

theorem exists_primitive_cube_root [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    ∃ ω : Kˣ, (ω : K) ^ 2 + ω + 1 = 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rwa [Nat.card_units])
  have hζ3 : (ζ : K) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one ζ
    rw [hζ] at h
    simpa using congrArg Units.val h
  have hζ1 : (ζ : K) ≠ 1 := fun h => by
    have h1 : ζ = 1 := Units.ext (by simpa using h)
    rw [h1, orderOf_one] at hζ
    exact absurd hζ (by norm_num)
  refine ⟨ζ, ?_⟩
  have h : ((ζ : K) - 1) * ((ζ : K) ^ 2 + ζ + 1) = 0 := by linear_combination hζ3
  exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hζ1)

theorem cube_eq_one_of_sq_add {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  linear_combination (ω - 1) * hω

theorem ne_one_of_sq_add [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 1 := by
  rintro rfl
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have : (1 : K) = 0 := by linear_combination hω - h2
  exact one_ne_zero this

theorem eq_or_eq_sq_of_cube {ω ζ : K} (hω : ω ^ 2 + ω + 1 = 0) (hζ3 : ζ ^ 3 = 1)
    (hζ1 : ζ ≠ 1) : ζ = ω ∨ ζ = ω ^ 2 := by
  have h1 : ζ ^ 2 + ζ + 1 = 0 := by
    have h : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by linear_combination hζ3
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hζ1)
  have h : (ζ - ω) * (ζ - ω ^ 2) = 0 := by
    linear_combination h1 + (ω - 1 - ζ) * hω
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (sub_eq_zero.1 h)

theorem scalar_mem_glPi {π : Bool} {m : ℕ} (hF : Sec4.PiField π 2 m K) (c : Kˣ)
    (hc : π = false → (c : K) ^ (2 ^ m + 1) = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ Sec4.glPi π 3 (2 ^ m) K := by
  cases π
  · rw [Sec4.mem_glPi_false hF.unitary]
    have hc' := hc rfl
    ext i j
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply, Matrix.one_apply,
      UnitaryFieldData.bar_apply]
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
    by_cases hij : i = j
    · subst hij
      simp only [ite_true]
      rw [← pow_succ]
      exact hc'
    · simp [Ne.symm hij, hij]
  · exact Sec4.mem_glPi_true _ _

@[expose] def swap12 : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

@[expose] def swap02 : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem swap12_mul_self : (swap12 : Matrix (Fin 3) (Fin 3) K) * swap12 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap12, Matrix.mul_apply, Fin.sum_univ_three]

theorem swap02_mul_self : (swap02 : Matrix (Fin 3) (Fin 3) K) * swap02 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap02, Matrix.mul_apply, Fin.sum_univ_three]

theorem swap12_conj_diagonal (d : Fin 3 → K) :
    swap12 * diagonal d * swap12 = diagonal ![d 0, d 2, d 1] := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [swap12]

theorem swap02_conj_diagonal (d : Fin 3 → K) :
    swap02 * diagonal d * swap02 = diagonal ![d 2, d 1, d 0] := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [swap02]

@[expose] def swap12GL : GL (Fin 3) K := ⟨swap12, swap12, swap12_mul_self, swap12_mul_self⟩

@[expose] def swap02GL : GL (Fin 3) K := ⟨swap02, swap02, swap02_mul_self, swap02_mul_self⟩

theorem perm_mem_glPi {π : Bool} {m : ℕ} (hF : Sec4.PiField π 2 m K) (T : GL (Fin 3) K)
    (hmap : ∀ σ : K →+* K, (T : Matrix (Fin 3) (Fin 3) K).map σ = T)
    (hT : (T : Matrix (Fin 3) (Fin 3) K)ᵀ * T = 1) : T ∈ Sec4.glPi π 3 (2 ^ m) K := by
  cases π
  · rw [Sec4.mem_glPi_false hF.unitary, hmap]
    exact hT
  · exact Sec4.mem_glPi_true _ _

theorem swap12GL_mem {π : Bool} {m : ℕ} (hF : Sec4.PiField π 2 m K) :
    swap12GL ∈ Sec4.glPi π 3 (2 ^ m) K := by
  refine perm_mem_glPi hF _ (fun σ => ?_) ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [swap12GL, swap12]
  · change swap12ᵀ * swap12 = 1
    rw [show (swap12 : Matrix (Fin 3) (Fin 3) K)ᵀ = swap12 by
      ext i j; fin_cases i <;> fin_cases j <;> simp [swap12]]
    exact swap12_mul_self

theorem swap02GL_mem {π : Bool} {m : ℕ} (hF : Sec4.PiField π 2 m K) :
    swap02GL ∈ Sec4.glPi π 3 (2 ^ m) K := by
  refine perm_mem_glPi hF _ (fun σ => ?_) ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [swap02GL, swap02]
  · change swap02ᵀ * swap02 = 1
    rw [show (swap02 : Matrix (Fin 3) (Fin 3) K)ᵀ = swap02 by
      ext i j; fin_cases i <;> fin_cases j <;> simp [swap02]]
    exact swap02_mul_self

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel in
theorem exists_diagonalizing {π : Bool} {m : ℕ} (hF : Sec4.PiField π 2 m K)
    (hmod : Sec4.ModThree π (2 ^ m)) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {y : GL (Fin 3) K}
    (hy : y ∈ Sec4.glPi π 3 (2 ^ m) K) (hy3 : y ^ 3 = 1) :
    ∃ P : GL (Fin 3) K, P ∈ Sec4.glPi π 3 (2 ^ m) K ∧ ∃ d : Fin 3 → K, (∀ i, d i ^ 3 = 1) ∧
      (y : Matrix (Fin 3) (Fin 3) K) * P = P * diagonal d := by
  have : CharP K 2 := charP_two_of_piField hF
  have : Finite K := hF.finite
  cases π
  ·
    have hU := hF.unitary
    have h3q : 3 ∣ 2 ^ m + 1 := by
      have h : 2 ^ m % 3 = 2 := hmod
      omega
    have hyU : y ∈ primeFormUnitary hU (idGram K 3) := by
      rw [mem_primeFormUnitary]
      have := (Sec4.mem_glPi_false hU).1 hy
      simpa [idGram] using this
    set Y : primeFormUnitary hU (idGram K 3) := ⟨y, hyU⟩ with hY
    have hY3 : Y ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hy3)
    obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag hU Nat.prime_three h3q
      (Subgroup.zpowers Y)
      (fun a ha b hb => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        rw [← _root_.zpow_add, ← _root_.zpow_add, add_comm])
      (fun a ha => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hY3,
          _root_.one_zpow])
    have hd := hP Y (Subgroup.mem_zpowers Y)
    set M : Matrix (Fin 3) (Fin 3) K :=
      (((P⁻¹ * Y * P : primeFormUnitary hU (idGram K 3)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) with hM
    have hMd : M = diagonal fun i => M i i := hd.diagonal_diag.symm
    have hPm : (P : GL (Fin 3) K) ∈ Sec4.glPi false 3 (2 ^ m) K := by
      rw [Sec4.mem_glPi_false hU]
      have := (mem_primeFormUnitary).1 P.2
      simpa [idGram] using this
    have hyP : (y : Matrix (Fin 3) (Fin 3) K) * (P : GL (Fin 3) K) =
        ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M := by
      have e : (P : GL (Fin 3) K) * ((P⁻¹ * Y * P : primeFormUnitary hU (idGram K 3)) :
          GL (Fin 3) K) = y * P := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hY]
        group
      rw [hM, ← Units.val_mul, ← Units.val_mul, e]
    have hM3 : M ^ 3 = 1 := by
      rw [hM, ← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow]
      have : (P⁻¹ * Y * P) ^ 3 = 1 := by
        have e : P⁻¹ * Y * P = P⁻¹ * Y * P⁻¹⁻¹ := by rw [inv_inv]
        rw [e, conj_pow, hY3, mul_one, mul_inv_cancel]
      rw [this]
      rfl
    refine ⟨P, hPm, fun i => M i i, fun i => ?_, by rw [hyP, ← hMd]⟩
    have h3 := congrFun (congrFun hM3 i) i
    rw [hMd, diagonal_pow, diagonal_apply_eq, Matrix.one_apply_eq] at h3
    exact h3
  ·
    have hω3 : ω ^ 3 = 1 := cube_eq_one_of_sq_add hω
    have hω1 : ω ≠ 1 := ne_one_of_sq_add hω
    have h3 : (3 : K) ≠ 0 := by
      have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      intro h
      have : (1 : K) = 0 := by linear_combination h - h2
      exact one_ne_zero this
    have hy3' : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hy3, Units.val_one]
    obtain ⟨b, hb, hk⟩ := Sec4.exists_eigenbasis hω3 hω1 h3 hy3'
    choose k hk using hk
    have hmul := Sec4.mul_colMat_eq (c := fun i => ω ^ (k i : ℕ)) hk
    obtain ⟨Pu, hPu⟩ := Sec4.isUnit_colMat hb
    refine ⟨Pu, Sec4.mem_glPi_true _ _, fun i => ω ^ (k i : ℕ), fun i => ?_, ?_⟩
    · rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
    · rw [hPu]
      exact hmul

theorem frame_of_diag {π : Bool} {m : ℕ} {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {g : Matrix (Fin 3) (Fin 3) K} {Q : GL (Fin 3) K} (hQ : Q ∈ Sec4.glPi π 3 (2 ^ m) K)
    {x y : K} (hx : x ≠ 0) (hxy : x ≠ y) (h3 : x ^ 3 = y ^ 3)
    (hgQ : g * Q = Q * diagonal ![x, x, y]) :
    ∃ Q : GL (Fin 3) K, Q ∈ Sec4.glPi π 3 (2 ^ m) K ∧ ∃ ζ : K, (ζ = ω ∨ ζ = ω ^ 2) ∧
      ∃ c : K, c ≠ 0 ∧ g * Q = Q * diagonal ![c, c, c * ζ] := by
  refine ⟨Q, hQ, y / x, eq_or_eq_sq_of_cube hω ?_ ?_, x, hx, ?_⟩
  · rw [div_pow, ← h3, div_self (pow_ne_zero 3 hx)]
  · intro h
    exact hxy ((div_eq_one_iff_eq hx).1 h).symm
  · rw [hgQ, mul_div_cancel₀ y hx]

theorem exists_frame {π : Bool} {m : ℕ} (hF : Sec4.PiField π 2 m K)
    (hmod : Sec4.ModThree π (2 ^ m)) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {g S : GL (Fin 3) K}
    (hg : g ∈ Sec4.glPi π 3 (2 ^ m) K)
    (hg3 : g ^ 3 ∈ Subgroup.center (GL (Fin 3) K)) (hgc : g ∉ Subgroup.center (GL (Fin 3) K))
    (hS2 : S ^ 2 ∈ Subgroup.center (GL (Fin 3) K)) (hSc : S ∉ Subgroup.center (GL (Fin 3) K))
    (hSg : ProjGenLinGroup.mk (S * g) = ProjGenLinGroup.mk (g * S)) :
    ∃ Q : GL (Fin 3) K, Q ∈ Sec4.glPi π 3 (2 ^ m) K ∧ ∃ ζ : K, (ζ = ω ∨ ζ = ω ^ 2) ∧
      ∃ c : K, c ≠ 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) * Q = Q * diagonal ![c, c, c * ζ] := by
  have : CharP K 2 := charP_two_of_piField hF
  have : Finite K := hF.finite
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg3 hS2 hgc hSc
  obtain ⟨τ, hτ⟩ := hg3
  obtain ⟨ν, hν⟩ := hS2
  set gm := (g : Matrix (Fin 3) (Fin 3) K) with hgm
  set Sm := (S : Matrix (Fin 3) (Fin 3) K) with hSm
  have hscal : ∀ c : Kˣ, ((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = (c : K) • 1 := fun c => by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hgm3 : gm ^ 3 = (τ : K) • 1 := by
    rw [hgm, ← Units.val_pow_eq_pow_val, ← hτ, hscal]
  have hSm2 : Sm * Sm = (ν : K) • 1 := by
    rw [hSm, ← Units.val_mul, ← sq, ← hν, hscal]
  have hnotscal : ∀ (h : GL (Fin 3) K), h ∉ Set.range (Matrix.GeneralLinearGroup.scalar (Fin 3)) →
      ∀ c : K, (h : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 := by
    intro h hh c hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact not_isUnit_zero (hc ▸ h.isUnit)
    exact hh ⟨Units.mk0 c hc0, Units.ext (by rw [hscal, Units.val_mk0, hc])⟩
  have hgs := hnotscal g hgc
  have hSs := hnotscal S hSc
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.1 hSg
  have hSgm : Sm * gm = ((u⁻¹ : Kˣ) : K) • (gm * Sm) := by
    have e := congrArg (fun h : GL (Fin 3) K => (h : Matrix (Fin 3) (Fin 3) K)) hu
    simp only [Units.val_mul, hscal] at e
    rw [← e, Matrix.mul_smul, Matrix.mul_one, smul_smul, Units.val_inv_eq_inv_val,
      inv_mul_cancel₀ (Units.ne_zero u), one_smul]
  have hcomm : Sm * gm = gm * Sm :=
    commute_of_mul_eq_smul (Units.ne_zero ν) g.isUnit hSm2 hSgm
  obtain ⟨w, hw0, a, ha⟩ := exists_eigenvector_of_commute hSm2 hSs hcomm
  have hg3w : gm ^ 3 *ᵥ w = a ^ 3 • w := by
    rw [pow_three, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_smul, ha,
      smul_smul, Matrix.mulVec_smul, ha, smul_smul]
    congr 1
    ring
  have ha3 : a ^ 3 = τ := by
    rw [hgm3, Matrix.smul_mulVec, Matrix.one_mulVec] at hg3w
    have h0 : (a ^ 3 - (τ : K)) • w = 0 := by rw [sub_smul, hg3w, sub_self]
    exact (sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_right hw0))
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at ha3
    exact Units.ne_zero τ ha3.symm
  have haq : π = false → a ^ (2 ^ m + 1) = 1 := by
    rintro rfl
    have hU := hF.unitary
    have hg3U : g ^ 3 ∈ Sec4.glPi false 3 (2 ^ m) K := pow_mem hg 3
    rw [Sec4.mem_glPi_false hU, ← hτ, hscal] at hg3U
    have hτq : (τ : K) ^ (2 ^ m) * τ = 1 := by
      have e := congrFun (congrFun hg3U 0) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
        UnitaryFieldData.bar_apply] using e
    have hb3 : (a ^ (2 ^ m + 1)) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ha3, pow_succ]
      exact hτq
    have hcard : Nat.card K = (2 ^ m) ^ 2 := by rw [hU.card, ← pow_mul, mul_comm]
    have hbq : (a ^ (2 ^ m + 1)) ^ (2 ^ m - 1) = 1 := by
      have : Fintype K := Fintype.ofFinite K
      have h := FiniteField.pow_card_sub_one_eq_one a ha0
      rw [← Nat.card_eq_fintype_card, hcard] at h
      rw [← pow_mul]
      have hq1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      convert h using 2
      have : (2 ^ m + 1) * (2 ^ m - 1) = (2 ^ m) ^ 2 - 1 := by
        rw [sq]
        zify [hq1, Nat.one_le_iff_ne_zero.2 (by positivity : (2 ^ m) * 2 ^ m ≠ 0)]
        ring
      exact this
    have hcop : Nat.Coprime 3 (2 ^ m - 1) := by
      have h : 2 ^ m % 3 = 2 := hmod
      have hq1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 ?_
      omega
    exact (pow_eq_one_iff_of_coprime hcop).1 ⟨hb3, hbq⟩
  set au : Kˣ := Units.mk0 a ha0 with hau
  set y : GL (Fin 3) K := Matrix.GeneralLinearGroup.scalar (Fin 3) au⁻¹ * g with hy
  have hyG : y ∈ Sec4.glPi π 3 (2 ^ m) K := by
    refine mul_mem (scalar_mem_glPi hF au⁻¹ fun hπ => ?_) hg
    rw [Units.val_inv_eq_inv_val, inv_pow, hau, Units.val_mk0, haq hπ, inv_one]
  have hym : (y : Matrix (Fin 3) (Fin 3) K) = a⁻¹ • gm := by
    rw [hy, Units.val_mul, hscal, Matrix.smul_mul, Matrix.one_mul, Units.val_inv_eq_inv_val,
      hau, Units.val_mk0]
  have hy3 : y ^ 3 = 1 := by
    have hc : Commute (Matrix.GeneralLinearGroup.scalar (Fin 3) au⁻¹) g :=
      (Subgroup.mem_center_iff.1 (by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨au⁻¹, rfl⟩) g).symm
    rw [hy, hc.mul_pow, ← map_pow, ← hτ, ← map_mul]
    have : au⁻¹ ^ 3 * τ = 1 := Units.ext (by
      rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hau, Units.val_mk0,
        ← ha3, inv_pow, inv_mul_cancel₀ (pow_ne_zero 3 ha0), Units.val_one])
    rw [this, map_one]
  obtain ⟨P, hP, d, hd3, hyP⟩ := exists_diagonalizing hF hmod hω hyG hy3
  have hgP : gm * P = P * diagonal fun i => a * d i := by
    have e : gm = a • (y : Matrix (Fin 3) (Fin 3) K) := by
      rw [hym, smul_smul, mul_inv_cancel₀ ha0, one_smul]
    rw [e, Matrix.smul_mul, hyP, ← Matrix.mul_smul, ← Matrix.diagonal_smul]
    rfl
  have hd0 : ∀ i, d i ≠ 0 := fun i h => by
    have := hd3 i
    rw [h, zero_pow (by norm_num)] at this
    exact zero_ne_one this
  have hnconst : ¬ (d 0 = d 1 ∧ d 1 = d 2) := by
    rintro ⟨h01, h12⟩
    apply hgs (a * d 0)
    have hdc : (diagonal fun i => a * d i) = (a * d 0) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [Matrix.smul_one_eq_diagonal]
      congr 1
      funext i
      fin_cases i
      · rfl
      · simp [h01]
      · simp [h01, h12]
    obtain ⟨Pu, hPu⟩ : IsUnit (P : Matrix (Fin 3) (Fin 3) K) := P.isUnit
    have h1 : gm * P * (P⁻¹ : GL (Fin 3) K) = gm := by
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    change gm = _
    rw [← h1, hgP, hdc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one]
  have hndist : ¬ (d 0 ≠ d 1 ∧ d 0 ≠ d 2 ∧ d 1 ≠ d 2) := by
    rintro ⟨h01, h02, h12⟩
    have hSy : Sm * (y : Matrix (Fin 3) (Fin 3) K) = (y : Matrix (Fin 3) (Fin 3) K) * Sm := by
      rw [hym, Matrix.mul_smul, Matrix.smul_mul, hcomm]
    have hdist : ∀ i j, i ≠ j → d i ≠ d j := by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals first
        | exact absurd rfl hij
        | exact h01 | exact h02 | exact h12
        | exact Ne.symm h01 | exact Ne.symm h02 | exact Ne.symm h12
    obtain ⟨c, hc⟩ := eq_smul_one_of_commute_diagonal P.isUnit hyP hdist hSy hSm2
    exact hSs c hc
  by_cases h01 : d 0 = d 1
  · have h2 : d 2 ≠ d 0 := fun h => hnconst ⟨h01, h01 ▸ h.symm⟩
    refine frame_of_diag hω hP (mul_ne_zero ha0 (hd0 0))
      (fun h => h2 (mul_left_cancel₀ ha0 h).symm) (by rw [mul_pow, mul_pow, hd3, hd3]) ?_
    rw [hgP]
    congr 1
    funext i j
    fin_cases i <;> fin_cases j <;> simp [h01]
  · by_cases h02 : d 0 = d 2
    · refine frame_of_diag hω (mul_mem hP (swap12GL_mem hF)) (mul_ne_zero ha0 (hd0 0))
        (fun h => h01 (mul_left_cancel₀ ha0 h)) (by rw [mul_pow, mul_pow, hd3, hd3]) ?_
      rw [Units.val_mul, ← Matrix.mul_assoc, hgP]
      change (P : Matrix (Fin 3) (Fin 3) K) * diagonal (fun i => a * d i) * swap12 =
        (P : Matrix (Fin 3) (Fin 3) K) * swap12 * _
      rw [Matrix.mul_assoc, Matrix.mul_assoc]
      congr 1
      calc diagonal (fun i => a * d i) * swap12 =
          swap12 * swap12 * diagonal (fun i => a * d i) * swap12 := by
            rw [swap12_mul_self, Matrix.one_mul]
        _ = swap12 * (swap12 * diagonal (fun i => a * d i) * swap12) := by
            simp only [Matrix.mul_assoc]
        _ = swap12 * diagonal ![a * d 0, a * d 0, a * d 1] := by
            rw [swap12_conj_diagonal]
            congr 2
            funext i
            fin_cases i <;> simp [h02]
    · have h12 : d 1 = d 2 := by
        by_contra h12
        exact hndist ⟨h01, h02, h12⟩
      refine frame_of_diag hω (mul_mem hP (swap02GL_mem hF)) (mul_ne_zero ha0 (hd0 1))
        (fun h => h01 (mul_left_cancel₀ ha0 h).symm) (by rw [mul_pow, mul_pow, hd3, hd3]) ?_
      rw [Units.val_mul, ← Matrix.mul_assoc, hgP]
      change (P : Matrix (Fin 3) (Fin 3) K) * diagonal (fun i => a * d i) * swap02 =
        (P : Matrix (Fin 3) (Fin 3) K) * swap02 * _
      rw [Matrix.mul_assoc, Matrix.mul_assoc]
      congr 1
      calc diagonal (fun i => a * d i) * swap02 =
          swap02 * swap02 * diagonal (fun i => a * d i) * swap02 := by
            rw [swap02_mul_self, Matrix.one_mul]
        _ = swap02 * (swap02 * diagonal (fun i => a * d i) * swap02) := by
            simp only [Matrix.mul_assoc]
        _ = swap02 * diagonal ![a * d 1, a * d 1, a * d 0] := by
            rw [swap02_conj_diagonal]
            congr 2
            funext i
            fin_cases i <;> simp [h12]

@[expose] def dOmega (ζ : Kˣ) : GL (Fin 3) K where
  val := diagonal ![1, 1, (ζ : K)]
  inv := diagonal ![1, 1, ((ζ⁻¹ : Kˣ) : K)]
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp

theorem coe_dOmega (ζ : Kˣ) :
    ((dOmega ζ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![1, 1, (ζ : K)] := rfl

theorem dOmega_sq {ζ : Kˣ} (hζ : (ζ : K) ^ 3 = 1) : dOmega (ζ ^ 2) = (dOmega ζ)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
  rw [Units.val_mul, coe_dOmega, coe_dOmega, diagonal_mul_diagonal, Units.val_one,
    ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp
  rw [← pow_succ]
  exact hζ

theorem dOmega_mem {π : Bool} {m : ℕ} (hF : Sec4.PiField π 2 m K) (hmod : Sec4.ModThree π (2 ^ m))
    {ζ : Kˣ} (hζ : (ζ : K) ^ 3 = 1) : dOmega ζ ∈ Sec4.glPi π 3 (2 ^ m) K := by
  cases π
  · rw [Sec4.mem_glPi_false hF.unitary, coe_dOmega]
    have h3q : 3 ∣ 2 ^ m + 1 := by
      have h : 2 ^ m % 3 = 2 := hmod
      omega
    obtain ⟨k, hk⟩ := h3q
    have hζq : (ζ : K) ^ (2 ^ m) * ζ = 1 := by
      rw [← pow_succ, hk, pow_mul, hζ, one_pow]
    rw [diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [UnitaryFieldData.bar_apply, hζq]
  · exact Sec4.mem_glPi_true _ _

theorem exists_conj_delta {π : Bool} {m : ℕ} (hF : Sec4.PiField π 2 m K)
    (hmod : Sec4.ModThree π (2 ^ m)) {ω : Kˣ} (hω : (ω : K) ^ 2 + ω + 1 = 0)
    (u : projImage (Sec4.glPi π 3 (2 ^ m) K)) (hu : orderOf u = 3)
    (hs : ∃ s, s ≠ 1 ∧ s ^ 2 = 1 ∧ s * u = u * s) :
    ∃ x : projImage (Sec4.glPi π 3 (2 ^ m) K),
      (u : PGL(3, K)) = x * ProjGenLinGroup.mk (dOmega ω) * (x : PGL(3, K))⁻¹ ∨
        (u : PGL(3, K)) = x * (ProjGenLinGroup.mk (dOmega ω))⁻¹ * (x : PGL(3, K))⁻¹ := by
  obtain ⟨s, hs1, hs2, hsu⟩ := hs
  obtain ⟨g, hg, hgu⟩ := u.2
  obtain ⟨S, hS, hSs⟩ := s.2
  have hu3 : u ^ 3 = 1 := by
    have h := pow_orderOf_eq_one u
    rwa [hu] at h
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu
    exact absurd hu (by norm_num)
  have hg3 : g ^ 3 ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [← ProjGenLinGroup.mk_eq_one, map_pow, hgu, ← Subgroup.coe_pow, hu3]
    rfl
  have hgc : g ∉ Subgroup.center (GL (Fin 3) K) := by
    rw [← ProjGenLinGroup.mk_eq_one, hgu]
    intro h
    exact hu1 (Subtype.ext h)
  have hS2 : S ^ 2 ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [← ProjGenLinGroup.mk_eq_one, map_pow, hSs, ← Subgroup.coe_pow, hs2]
    rfl
  have hSc : S ∉ Subgroup.center (GL (Fin 3) K) := by
    rw [← ProjGenLinGroup.mk_eq_one, hSs]
    intro h
    exact hs1 (Subtype.ext h)
  have hSg : ProjGenLinGroup.mk (S * g) = ProjGenLinGroup.mk (g * S) := by
    rw [map_mul, map_mul, hSs, hgu]
    exact congrArg Subtype.val hsu
  obtain ⟨Q, hQ, ζ, hζ, c, hc0, hgQ⟩ := exists_frame hF hmod hω hg hg3 hgc hS2 hSc hSg
  have hω3 : (ω : K) ^ 3 = 1 := cube_eq_one_of_sq_add hω
  have key : ∀ ζu : Kˣ, (ζu : K) = ζ →
      (u : PGL(3, K)) = ProjGenLinGroup.mk Q * ProjGenLinGroup.mk (dOmega ζu) *
        (ProjGenLinGroup.mk Q)⁻¹ := by
    intro ζu hζu
    rw [← hgu, ← map_inv, ← map_mul, ← map_mul, ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨(Units.mk0 c hc0)⁻¹, Units.ext ?_⟩
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    have e : (g : Matrix (Fin 3) (Fin 3) K) = (Q : Matrix (Fin 3) (Fin 3) K) *
        diagonal ![c, c, c * ζ] * ((Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [← hgQ, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.mul_one]
    have hd : diagonal ![c, c, c * ζ] = c • diagonal ![1, 1, ζ] := by
      rw [← Matrix.diagonal_smul]
      congr 1
      funext i
      fin_cases i <;> simp
    calc (g : Matrix (Fin 3) (Fin 3) K) * diagonal (fun _ => (((Units.mk0 c hc0)⁻¹ : Kˣ) : K))
        = c⁻¹ • (g : Matrix (Fin 3) (Fin 3) K) := by
          rw [← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
            Units.val_inv_eq_inv_val, Units.val_mk0]
      _ = (Q : Matrix (Fin 3) (Fin 3) K) * diagonal ![1, 1, ζ] *
          ((Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [e, hd, Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = _ := by rw [Units.val_mul, Units.val_mul, coe_dOmega, hζu]
  set x : projImage (Sec4.glPi π 3 (2 ^ m) K) := ⟨ProjGenLinGroup.mk Q, Q, hQ, rfl⟩
  refine ⟨x, ?_⟩
  rcases hζ with rfl | rfl
  · exact Or.inl (key ω rfl)
  · refine Or.inr ?_
    rw [key (ω ^ 2) (by rw [Units.val_pow_eq_pow_val]), dOmega_sq hω3, map_inv]

theorem kFPGL3Ord3Classes_holds : KFPGL3Ord3Classes := by
  intro π m K _ hF hmod u u' hu hu' hs hs'
  have : Finite K := hF.finite
  have : CharP K 2 := charP_two_of_piField hF
  obtain ⟨ω, hω⟩ := exists_primitive_cube_root (three_dvd_card_sub_one hF hmod)
  have hω3 : (ω : K) ^ 3 = 1 := cube_eq_one_of_sq_add hω
  set δ : projImage (Sec4.glPi π 3 (2 ^ m) K) :=
    ⟨ProjGenLinGroup.mk (dOmega ω), dOmega ω, dOmega_mem hF hmod hω3, rfl⟩
  have hsub : ∀ v : projImage (Sec4.glPi π 3 (2 ^ m) K), orderOf v = 3 →
      (∃ s, s ≠ 1 ∧ s ^ 2 = 1 ∧ s * v = v * s) →
        ∃ x, v = x * δ * x⁻¹ ∨ v = x * δ⁻¹ * x⁻¹ := by
    intro v hv hsv
    obtain ⟨x, hx⟩ := exists_conj_delta hF hmod hω v hv hsv
    refine ⟨x, ?_⟩
    rcases hx with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  obtain ⟨x, hx⟩ := hsub u hu hs
  obtain ⟨x', hx'⟩ := hsub u' hu' hs'
  refine ⟨x * x'⁻¹, ?_⟩
  rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl
  · left; group
  · right; group
  · right; group
  · left; group

end CFSG.RankThree.PartTwo.Sec8.LangTwisted3Proof
