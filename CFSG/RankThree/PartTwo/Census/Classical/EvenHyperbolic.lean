module

public import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness

public section

namespace CFSG.RankThree.PartTwo.Census

open Matrix CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

section Plane

variable {K : Type} [Field K] [CharP K 2]

@[expose] def hypP (ω : K) : Matrix (Fin 2) (Fin 2) K := !![1, ω; 1, ω ^ 2]
@[expose] def hypP' (ω : K) : Matrix (Fin 2) (Fin 2) K := !![ω ^ 2, ω; 1, 1]
@[expose] def hypJ (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]
@[expose] def hypE (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; 0, 0]
@[expose] def hypN (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![1, 1; 1, 1]

variable {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
include hω

theorem hypP_mul_hypP' : hypP ω * hypP' ω = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hypP, hypP', Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
    | linear_combination hω - h2
    | linear_combination ω * h2
    | linear_combination ω ^ 2 * h2

theorem hypP'_mul_hypP : hypP' ω * hypP ω = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hypP, hypP', Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
    | linear_combination hω - h2
    | linear_combination h2
    | linear_combination ω ^ 3 * h2

omit [CharP K 2] hω in
theorem hypP_mul_hypE_mul : hypP ω * hypE K * hypP' ω = hypN K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hypP, hypP', hypE, hypN, Matrix.mul_apply, Fin.sum_univ_two]

omit [CharP K 2] in
theorem cube_eq_one : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω

variable {φ : K →+* K} (hφ : φ ω = ω ^ 2)
include hφ

omit [CharP K 2] in
theorem map_sq_eq : φ (ω ^ 2) = ω := by
  rw [map_pow, hφ, ← pow_mul]
  linear_combination (ω ^ 2 - ω) * hω

theorem hypP_unitary : ((hypP ω).map φ)ᵀ * hypP ω = hypJ K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hφ2 := map_sq_eq hω hφ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hypP, hypJ, Matrix.mul_apply, Fin.sum_univ_two, hφ, hφ2] <;>
    first
    | linear_combination h2
    | linear_combination hω - h2
    | linear_combination ω ^ 3 * h2

theorem hypP'_unitary : ((hypP' ω).map φ)ᵀ * hypJ K * hypP' ω = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hφ2 := map_sq_eq hω hφ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hypP', hypJ, Matrix.mul_apply, Fin.sum_univ_two, hφ, hφ2] <;>
    first
    | linear_combination hω - h2
    | linear_combination ω * h2
    | linear_combination ω ^ 2 * h2


@[expose] def hypD (a : Kˣ) : Matrix (Fin 2) (Fin 2) K := diagonal ![(a : K), ((a⁻¹ : Kˣ) : K)]

omit [CharP K 2] hω hφ in
theorem hypD_mul (a b : Kˣ) : hypD a * hypD b = hypD (a * b) := by
  rw [hypD, hypD, hypD, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [mul_comm]

omit [CharP K 2] hω hφ in
theorem hypD_one : hypD (1 : Kˣ) = 1 := by
  rw [hypD, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

omit [CharP K 2] hω hφ in
theorem det_hypD (a : Kˣ) : (hypD a).det = 1 := by
  rw [hypD, det_diagonal, Fin.prod_univ_two]
  simp

omit [CharP K 2] hω hφ in
theorem hypD_mul_hypE (a : Kˣ) : hypD a * hypE K = (a : K) • hypE K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hypD, hypE]

omit [CharP K 2] hω hφ in
theorem hypE_mul_hypD (a : Kˣ) : hypE K * hypD a = ((a⁻¹ : Kˣ) : K) • hypE K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hypD, hypE]

omit [CharP K 2] hω hφ in
theorem hypD_mul_hypJ_mul (a : Kˣ) : hypD a * hypJ K * hypD a = hypJ K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hypD, hypJ, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def hypM (ω : K) (a : Kˣ) : Matrix (Fin 2) (Fin 2) K := hypP ω * hypD a * hypP' ω

omit hφ in
theorem hypM_mul (a b : Kˣ) : hypM ω a * hypM ω b = hypM ω (a * b) := by
  rw [hypM, hypM, hypM, ← hypD_mul]
  calc hypP ω * hypD a * hypP' ω * (hypP ω * hypD b * hypP' ω) =
      hypP ω * hypD a * (hypP' ω * hypP ω) * hypD b * hypP' ω := by noncomm_ring
    _ = _ := by rw [hypP'_mul_hypP hω, mul_one, mul_assoc (hypP ω)]

omit hφ in
theorem hypM_one : hypM ω 1 = 1 := by
  rw [hypM, hypD_one, mul_one, hypP_mul_hypP' hω]

omit hφ in
theorem det_hypM (a : Kˣ) : (hypM ω a).det = 1 := by
  rw [hypM, det_mul, det_mul, det_hypD, mul_one, ← det_mul, hypP_mul_hypP' hω, det_one]

omit hφ in
theorem hypM_mul_hypN (a : Kˣ) : hypM ω a * hypN K = (a : K) • hypN K := by
  rw [← hypP_mul_hypE_mul (ω := ω), hypM]
  calc hypP ω * hypD a * hypP' ω * (hypP ω * hypE K * hypP' ω) =
      hypP ω * hypD a * (hypP' ω * hypP ω) * hypE K * hypP' ω := by noncomm_ring
    _ = _ := by
      rw [hypP'_mul_hypP hω, mul_one, mul_assoc (hypP ω), hypD_mul_hypE, mul_smul_comm,
        smul_mul_assoc]

omit hφ in
theorem hypN_mul_hypM (a : Kˣ) : hypN K * hypM ω a = ((a⁻¹ : Kˣ) : K) • hypN K := by
  rw [← hypP_mul_hypE_mul (ω := ω), hypM]
  calc hypP ω * hypE K * hypP' ω * (hypP ω * hypD a * hypP' ω) =
      hypP ω * hypE K * (hypP' ω * hypP ω) * hypD a * hypP' ω := by noncomm_ring
    _ = _ := by
      rw [hypP'_mul_hypP hω, mul_one, mul_assoc (hypP ω), hypE_mul_hypD, mul_smul_comm,
        smul_mul_assoc]

theorem hypM_unitary {a : Kˣ} (ha : φ a = a) :
    ((hypM ω a).map φ)ᵀ * hypM ω a = 1 := by
  have hD : ((hypD a).map φ)ᵀ = hypD a := by
    rw [hypD, diagonal_map (map_zero φ), diagonal_transpose]
    congr 1
    funext i
    fin_cases i <;> simp [ha]
  rw [hypM, Matrix.map_mul, Matrix.map_mul, transpose_mul, transpose_mul, hD]
  calc ((hypP' ω).map φ)ᵀ * (hypD a * ((hypP ω).map φ)ᵀ) * (hypP ω * hypD a * hypP' ω) =
      ((hypP' ω).map φ)ᵀ * (hypD a * (((hypP ω).map φ)ᵀ * hypP ω) * hypD a) * hypP' ω := by
        noncomm_ring
    _ = 1 := by
      rw [hypP_unitary hω hφ, hypD_mul_hypJ_mul, hypP'_unitary hω hφ]

end Plane

section Six

variable {K : Type} [Field K]

abbrev sixEquiv : Fin 2 × Fin 3 ≃ Fin 6 := finProdFinEquiv.trans (finCongr (by norm_num))

@[expose] def blk6 (M : Fin 3 → Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 6) (Fin 6) K :=
  (blockDiagonal M).submatrix sixEquiv.symm sixEquiv.symm

theorem blk6_mul (M M' : Fin 3 → Matrix (Fin 2) (Fin 2) K) :
    blk6 M * blk6 M' = blk6 (M * M') := by
  rw [blk6, blk6, blk6, submatrix_mul_equiv, ← blockDiagonal_mul]
  rfl

theorem blk6_one : blk6 (1 : Fin 3 → Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [blk6, blockDiagonal_one, submatrix_one_equiv]

theorem blk6_map (M : Fin 3 → Matrix (Fin 2) (Fin 2) K) (φ : K →+* K) :
    (blk6 M).map φ = blk6 fun i => (M i).map φ := by
  rw [blk6, blk6, ← submatrix_map, blockDiagonal_map _ _ (map_zero φ)]

theorem blk6_transpose (M : Fin 3 → Matrix (Fin 2) (Fin 2) K) :
    (blk6 M)ᵀ = blk6 fun i => (M i)ᵀ := by
  rw [blk6, blk6, transpose_submatrix, blockDiagonal_transpose]

theorem det_blk6 (M : Fin 3 → Matrix (Fin 2) (Fin 2) K) : (blk6 M).det = ∏ i, (M i).det := by
  rw [blk6, det_submatrix_equiv_self, det_blockDiagonal]

theorem blk6_apply (M : Fin 3 → Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) (b : Fin 3) :
    blk6 M (sixEquiv (i, b)) (sixEquiv (j, b)) = M b i j := by
  simp [blk6, blockDiagonal_apply]

theorem blk6_injective : Function.Injective (blk6 (K := K)) := by
  intro M M' h
  funext b
  ext i j
  have := congrFun (congrFun h (sixEquiv (i, b))) (sixEquiv (j, b))
  rwa [blk6_apply, blk6_apply] at this

theorem blk6_unitary (M : Fin 3 → Matrix (Fin 2) (Fin 2) K) (φ : K →+* K)
    (hM : ∀ i, ((M i).map φ)ᵀ * M i = 1) : ((blk6 M).map φ)ᵀ * blk6 M = 1 := by
  rw [blk6_map, blk6_transpose, blk6_mul, ← blk6_one]
  congr 1
  funext i
  exact hM i

end Six

section Witness

variable {K : Type} [Field K] [CharP K 2]

@[expose] def hypU (x : K) : Matrix (Fin 2) (Fin 2) K := 1 + x • hypN K

theorem hypN_mul_self : hypN K * hypN K = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hypN, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination h2

theorem hypU_mul (x y : K) : hypU x * hypU y = hypU (x + y) := by
  rw [hypU, hypU, hypU, add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul,
    hypN_mul_self, smul_zero, add_zero, add_smul]
  abel

omit [CharP K 2] in
theorem hypU_zero : hypU (0 : K) = 1 := by rw [hypU, zero_smul, add_zero]

theorem det_hypU (x : K) : (hypU x).det = 1 := by
  have hxx : x + x = 0 := CharTwo.add_self_eq_zero x
  refine eq_one_of_mul_self_eq_one ?_
  rw [← det_mul, hypU_mul, hxx, hypU_zero, det_one]

theorem hypU_unitary {φ : K →+* K} {x : K} (hx : φ x = x) :
    ((hypU x).map φ)ᵀ * hypU x = 1 := by
  have hU : ((hypU x).map φ)ᵀ = hypU x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hypU, hypN, hx]
  rw [hU, hypU_mul, CharTwo.add_self_eq_zero, hypU_zero]

theorem hypM_mul_hypU {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (a : Kˣ) (x : K) :
    hypM ω a * hypU x = hypU ((a : K) ^ 2 * x) * hypM ω a := by
  rw [hypU, hypU, mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc,
    hypM_mul_hypN hω, hypN_mul_hypM hω, smul_smul, smul_smul, add_right_inj]
  congr 1
  rw [Units.val_inv_eq_inv_val]
  field_simp

theorem three_le_localRank_statedSU_six_eight [Finite K] (h : UnitaryFieldData 2 3 K) :
    3 ≤ localRank 7 (StatedProj (StatedSU 6 (2 ^ 3) K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card Kˣ = 63 := by
    rw [Nat.card_units, h.card]
    norm_num
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [hK]; norm_num)
  set ω : K := (ζ : K)
  have hω3 : ω ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hζ, pow_orderOf_eq_one, Units.val_one]
  have hω1 : ω ≠ 1 := by
    intro h1
    have : ζ = 1 := Units.ext h1
    rw [this, orderOf_one] at hζ
    exact absurd hζ (by norm_num)
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hω1)
  have hbar : h.bar ω = ω ^ 2 := by
    rw [h.bar_apply, show 2 ^ 3 = 3 * 2 + 2 by norm_num, pow_add, pow_mul, hω3, one_pow,
      one_mul]
  have hμ := card_rootsOfUnity_of_dvd (K := K) (r := 7) (by norm_num) (by rw [hK]; norm_num)
  set μ := rootsOfUnity 7 K
  have hbarμ : ∀ a : μ, h.bar ((a : Kˣ) : K) = ((a : Kˣ) : K) := by
    intro a
    have ha7 : ((a : Kˣ) : K) ^ 7 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, rootsOfUnity_pow_eq_one,
        OneMemClass.coe_one, Units.val_one]
    rw [h.bar_apply, show 2 ^ 3 = 7 + 1 by norm_num, pow_succ, ha7, one_mul]
  set SU := StatedSU 6 (2 ^ 3) K
  have hMinj : ∀ a b : Kˣ, hypM ω a = hypM ω b → a = b := by
    intro a b hab
    have hD : ∀ c : Kˣ, hypP' ω * hypM ω c * hypP ω = hypD c := fun c => by
      rw [hypM]
      calc hypP' ω * (hypP ω * hypD c * hypP' ω) * hypP ω =
          (hypP' ω * hypP ω) * hypD c * (hypP' ω * hypP ω) := by noncomm_ring
        _ = hypD c := by rw [hypP'_mul_hypP hω, one_mul, mul_one]
    have := congrFun (congrFun ((hD a).symm.trans (hab ▸ hD b)) 0) 0
    simp only [hypD, diagonal_apply_eq, Matrix.cons_val_zero] at this
    exact Units.ext this
  let ψ₀ : (Fin 3 → μ) →* GL (Fin 6) K :=
    { toFun := fun t => ⟨blk6 fun i => hypM ω (t i), blk6 fun i => hypM ω (t i)⁻¹, by
          rw [blk6_mul, ← blk6_one]
          congr 1
          funext i
          rw [Pi.mul_apply, hypM_mul hω, mul_inv_cancel, hypM_one hω]
          rfl, by
          rw [blk6_mul, ← blk6_one]
          congr 1
          funext i
          rw [Pi.mul_apply, hypM_mul hω, inv_mul_cancel, hypM_one hω]
          rfl⟩
      map_one' := Units.ext (by
        change (blk6 fun i => hypM ω ((1 : Fin 3 → μ) i)) = 1
        rw [← blk6_one]
        congr 1
        funext i
        rw [Pi.one_apply, OneMemClass.coe_one, hypM_one hω]
        rfl)
      map_mul' := fun s t => Units.ext (by
        change (blk6 fun i => hypM ω ((s * t) i)) =
          (blk6 fun i => hypM ω (s i)) * blk6 fun i => hypM ω (t i)
        rw [blk6_mul]
        congr 1
        funext i
        rw [Pi.mul_apply, Pi.mul_apply, Subgroup.coe_mul, hypM_mul hω]) }
  have hcoeψ : ∀ t, ((ψ₀ t : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      blk6 fun i => hypM ω (t i) := fun _ => rfl
  have hmemψ : ∀ t, ψ₀ t ∈ SU := by
    intro t
    refine (mem_unitarySU_iff h).mpr ⟨?_, ?_⟩
    · rw [hcoeψ, det_blk6]
      exact Finset.prod_eq_one fun i _ => det_hypM hω _
    · rw [hcoeψ]
      exact blk6_unitary _ h.bar fun i => hypM_unitary hω hbar (hbarμ (t i))
  set ψ : (Fin 3 → μ) →* SU := ψ₀.codRestrict SU hmemψ
  have hψ : Function.Injective ψ := by
    intro s t hst
    have h1 : blk6 (fun i => hypM ω (s i)) = blk6 fun i => hypM ω (t i) := by
      rw [← hcoeψ, ← hcoeψ]
      exact congrArg (fun g : SU => ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) hst
    funext i
    exact Subtype.ext (hMinj _ _ (congrFun (blk6_injective h1) i))
  let χ₀ : Multiplicative h.fixedField →* GL (Fin 6) K :=
    { toFun := fun x => ⟨blk6 (Pi.mulSingle 0 (hypU (x.toAdd : K))),
          blk6 (Pi.mulSingle 0 (hypU (x.toAdd : K))), by
          rw [blk6_mul, ← Pi.mulSingle_mul, hypU_mul, CharTwo.add_self_eq_zero, hypU_zero,
            Pi.mulSingle_one, blk6_one], by
          rw [blk6_mul, ← Pi.mulSingle_mul, hypU_mul, CharTwo.add_self_eq_zero, hypU_zero,
            Pi.mulSingle_one, blk6_one]⟩
      map_one' := Units.ext (by
        change blk6 (Pi.mulSingle 0 (hypU ((0 : h.fixedField) : K))) = 1
        rw [ZeroMemClass.coe_zero, hypU_zero, Pi.mulSingle_one, blk6_one])
      map_mul' := fun x y => Units.ext (by
        change blk6 (Pi.mulSingle 0 (hypU ((x.toAdd + y.toAdd : h.fixedField) : K))) =
          blk6 (Pi.mulSingle 0 (hypU (x.toAdd : K))) * blk6 (Pi.mulSingle 0 (hypU (y.toAdd : K)))
        rw [blk6_mul, ← Pi.mulSingle_mul, hypU_mul, AddMemClass.coe_add]) }
  have hcoeχ : ∀ x, ((χ₀ x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      blk6 (Pi.mulSingle 0 (hypU (x.toAdd : K))) := fun _ => rfl
  have hmemχ : ∀ x, χ₀ x ∈ SU := by
    intro x
    refine (mem_unitarySU_iff h).mpr ⟨?_, ?_⟩
    · rw [hcoeχ, det_blk6]
      refine Finset.prod_eq_one fun i _ => ?_
      by_cases hi : i = 0
      · subst hi
        rw [Pi.mulSingle_eq_same, det_hypU]
      · rw [Pi.mulSingle_eq_of_ne hi, det_one]
    · rw [hcoeχ]
      refine blk6_unitary _ h.bar fun i => ?_
      by_cases hi : i = 0
      · subst hi
        rw [Pi.mulSingle_eq_same]
        exact hypU_unitary x.toAdd.2
      · rw [Pi.mulSingle_eq_of_ne hi, Matrix.map_one _ (map_zero _) (map_one _), transpose_one,
          mul_one]
  set χ : Multiplicative h.fixedField →* SU := χ₀.codRestrict SU hmemχ
  set Z := (StatedScalars (Fin 6) K).subgroupOf SU
  refine le_localRank_quotient_of_le_normalizer Z (by norm_num) (E := ψ.range) (P := χ.range)
    (isElemAbelian_range (fun t => funext fun i => rootsOfUnity_pow_eq_one (t i)) ψ) ?_ ?_ ?_
    ?_ ?_
  · rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv]
    exact card_fun_rootsOfUnity hμ
  · rw [eq_bot_iff]
    rintro y ⟨⟨t, rfl⟩, hyZ⟩
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hyZ
    have hdetc := ((mem_unitarySU_iff h).mp (ψ t).2)
    rw [← hc, GeneralLinearGroup.coe_scalar] at hdetc
    have hc6 : (c : K) ^ 6 = 1 := by
      have := hdetc.1
      rwa [scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        at this
    have hc9 : (c : K) ^ 9 = 1 := by
      have := congrFun (congrFun hdetc.2 0) 0
      simp only [scalar_apply, diagonal_map (map_zero h.bar), diagonal_transpose,
        diagonal_mul_diagonal, diagonal_apply_eq, Matrix.one_apply_eq, h.bar_apply] at this
      rw [← this]
      ring
    have hc3 : c ^ 3 = 1 := by
      have : (c : K) ^ Nat.gcd 6 9 = 1 := pow_gcd_eq_one.mpr ⟨hc6, hc9⟩
      exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact this)
    have hy3 : ψ t ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hc, ← map_pow, hc3, map_one, OneMemClass.coe_one]
    have hy7 : ψ t ^ 7 = 1 := by
      rw [← map_pow, show t ^ 7 = 1 from funext fun i => rootsOfUnity_pow_eq_one (t i), map_one]
    have hg : ψ t ^ Nat.gcd 7 3 = 1 := pow_gcd_eq_one.mpr ⟨hy7, hy3⟩
    rw [Subgroup.mem_bot]
    simpa using hg
  · intro y
    obtain ⟨x, hx⟩ := y.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, pow_two, Subgroup.coe_mul, ← hx, ← map_mul, OneMemClass.coe_one]
    have hxx : x * x = 1 := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      rw [toAdd_mul, AddMemClass.coe_add, CharTwo.add_self_eq_zero, toAdd_one,
        ZeroMemClass.coe_zero]
    rw [hxx, map_one]
  · intro hP
    have h1 : χ (Multiplicative.ofAdd 1) ∈ χ.range := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp (hP h1)
    have := congrFun (congrFun (congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K))
      hc) (sixEquiv ((0 : Fin 2), (0 : Fin 3)))) (sixEquiv ((1 : Fin 2), (0 : Fin 3)))
    change (GeneralLinearGroup.scalar (Fin 6) c : Matrix (Fin 6) (Fin 6) K) _ _ =
      blk6 (Pi.mulSingle 0 (hypU ((1 : h.fixedField) : K))) _ _ at this
    rw [blk6_apply, GeneralLinearGroup.coe_scalar, scalar_apply,
      diagonal_apply_ne _ (by decide)] at this
    simp [hypU, hypN] at this
  · refine le_normalizer_of_conj_mem ?_
    rintro _ ⟨t, rfl⟩ _ ⟨x, rfl⟩
    set a : Kˣ := ((t 0 : μ) : Kˣ)
    have hx' : (a : K) ^ 2 * (x.toAdd : K) ∈ h.fixedField := by
      change h.bar _ = _
      rw [map_mul, map_pow, hbarμ (t 0), x.toAdd.2]
      rfl
    refine ⟨Multiplicative.ofAdd ⟨_, hx'⟩, ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    refine Subtype.ext (Units.ext ?_)
    change blk6 (Pi.mulSingle 0 (hypU ((a : K) ^ 2 * (x.toAdd : K)))) *
        (blk6 fun i => hypM ω (t i)) =
      (blk6 fun i => hypM ω (t i)) * blk6 (Pi.mulSingle 0 (hypU (x.toAdd : K)))
    rw [blk6_mul, blk6_mul]
    congr 1
    funext i
    by_cases hi : i = 0
    · subst hi
      rw [Pi.mul_apply, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same,
        hypM_mul_hypU hω]
    · rw [Pi.mul_apply, Pi.mul_apply, Pi.mulSingle_eq_of_ne hi, Pi.mulSingle_eq_of_ne hi,
        one_mul, mul_one]

end Witness

end CFSG.RankThree.PartTwo.Census
