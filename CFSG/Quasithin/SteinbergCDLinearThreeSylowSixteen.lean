module

public import CFSG.Quasithin.SteinbergCDSemidihedralSixteen
public import CFSG.LieType.SteinbergBROddLinearThreeParabolic
public import CFSG.LieType.Steinberg.CentralExt.UnitaryThreeSylow

public section

namespace CFSG.Quasithin.SteinbergCD

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Arith

variable {q : ℕ}

theorem two_le_ordProj_two {n : ℕ} (hn : n ≠ 0) (h2 : 2 ∣ n) : 2 ≤ ordProj[2] n := by
  have h := (Nat.prime_two.pow_dvd_iff_dvd_ordProj (k := 1) hn).1 (by rwa [pow_one])
  rw [pow_one] at h
  exact Nat.le_of_dvd (Nat.ordProj_pos n 2) h

theorem eight_le_ordProj_mul (hq : Odd q) (hq1 : 1 < q) :
    8 ≤ ordProj[2] (q - 1) * ordProj[2] (q + 1) := by
  obtain ⟨m, rfl⟩ := hq
  have hm : m ≠ 0 := by omega
  have h8 : 2 ^ 3 ∣ (2 * m + 1 - 1) * (2 * m + 1 + 1) := by
    obtain ⟨k, hk⟩ := Nat.even_mul_succ_self m
    refine ⟨k, ?_⟩
    rw [show 2 * m + 1 - 1 = 2 * m by omega, show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
    calc 2 * m * (2 * (m + 1)) = 4 * (m * (m + 1)) := by ring
      _ = 2 ^ 3 * k := by rw [hk]; ring
  have hne : (2 * m + 1 - 1) * (2 * m + 1 + 1) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have h := (Nat.prime_two.pow_dvd_iff_dvd_ordProj hne).1 h8
  rw [Nat.ordProj_mul 2 (by omega) (by omega)] at h
  exact Nat.le_of_dvd (Nat.mul_pos (Nat.ordProj_pos _ 2) (Nat.ordProj_pos _ 2)) h

theorem sixteen_le_sq_mul (hq : Odd q) (hq1 : 1 < q) :
    16 ≤ ordProj[2] (q - 1) ^ 2 * ordProj[2] (q + 1) := by
  have h8 := eight_le_ordProj_mul hq hq1
  have hr := two_le_ordProj_two (n := q - 1) (by omega) (by
    obtain ⟨m, rfl⟩ := hq
    exact ⟨m, by omega⟩)
  nlinarith

theorem mod_eight_of_sq_mul_eq (hq : Odd q) (hq1 : 1 < q)
    (h : ordProj[2] (q - 1) ^ 2 * ordProj[2] (q + 1) = 16) : q % 8 = 3 := by
  have h8 := eight_le_ordProj_mul hq hq1
  have hr := two_le_ordProj_two (n := q - 1) (by omega) (by
    obtain ⟨m, rfl⟩ := hq
    exact ⟨m, by omega⟩)
  set r := ordProj[2] (q - 1)
  set s := ordProj[2] (q + 1)
  have hr2 : r = 2 := by nlinarith
  have hs4 : s = 4 := by
    rw [hr2] at h
    omega
  have h4 : ¬ 2 ^ 2 ∣ q - 1 := fun hd => by
    have := (Nat.prime_two.pow_dvd_iff_dvd_ordProj (by omega)).1 hd
    rw [← show r = ordProj[2] (q - 1) from rfl, hr2] at this
    norm_num at this
  have h8' : ¬ 2 ^ 3 ∣ q + 1 := fun hd => by
    have := (Nat.prime_two.pow_dvd_iff_dvd_ordProj (by omega)).1 hd
    rw [← show s = ordProj[2] (q + 1) from rfl, hs4] at this
    norm_num at this
  obtain ⟨m, rfl⟩ := hq
  omega

theorem sixteen_le_mul_sq (hq : Odd q) (hq1 : 1 < q) :
    16 ≤ ordProj[2] (q - 1) * ordProj[2] (q + 1) ^ 2 := by
  have h8 := eight_le_ordProj_mul hq hq1
  have hs := two_le_ordProj_two (n := q + 1) (by omega) (by
    obtain ⟨m, rfl⟩ := hq
    exact ⟨m + 1, by omega⟩)
  nlinarith

theorem mod_eight_of_mul_sq_eq (hq : Odd q) (hq1 : 1 < q)
    (h : ordProj[2] (q - 1) * ordProj[2] (q + 1) ^ 2 = 16) : q % 8 = 5 := by
  have h8 := eight_le_ordProj_mul hq hq1
  have hs := two_le_ordProj_two (n := q + 1) (by omega) (by
    obtain ⟨m, rfl⟩ := hq
    exact ⟨m + 1, by omega⟩)
  set r := ordProj[2] (q - 1)
  set s := ordProj[2] (q + 1)
  have hs2 : s = 2 := by nlinarith
  have hr4 : r = 4 := by
    rw [hs2] at h
    omega
  have h4 : ¬ 2 ^ 2 ∣ q + 1 := fun hd => by
    have := (Nat.prime_two.pow_dvd_iff_dvd_ordProj (by omega)).1 hd
    rw [← show s = ordProj[2] (q + 1) from rfl, hs2] at this
    norm_num at this
  have h8' : ¬ 2 ^ 3 ∣ q - 1 := fun hd => by
    have := (Nat.prime_two.pow_dvd_iff_dvd_ordProj (by omega)).1 hd
    rw [← show r = ordProj[2] (q - 1) from rfl, hr4] at this
    norm_num at this
  obtain ⟨m, rfl⟩ := hq
  omega

theorem ordProj_two_order_SL_three (hq : Odd q) (hq1 : 1 < q) :
    ordProj[2] (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) =
      ordProj[2] (q - 1) ^ 2 * ordProj[2] (q + 1) := by
  have e1 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hq1
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have e2 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hq1
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have hodd1 : Odd (q ^ 3) := hq.pow
  have hodd2 : Odd (q ^ 2 + q + 1) := by
    obtain ⟨m, rfl⟩ := hq
    exact ⟨2 * m ^ 2 + 3 * m + 1, by ring⟩
  have hq0 : q - 1 ≠ 0 := by omega
  rw [e1, e2, Nat.ordProj_mul 2 (by positivity) (by positivity),
    Nat.ordProj_mul 2 (by positivity) (by positivity),
    Nat.ordProj_mul 2 hq0 (by positivity), Nat.ordProj_mul 2 hq0 (by positivity),
    CFSG.LieType.Steinberg.ordProj_two_of_odd hodd1,
    CFSG.LieType.Steinberg.ordProj_two_of_odd hodd2]
  ring

end Arith

variable {K : Type*} [Field K]

theorem pow_three_eq_one_of_mem_scalars {A : SpecialLinearGroup (Fin 3) K}
    (hA : A ∈ scalars 3 K) : A ^ 3 = 1 := by
  obtain ⟨c, hc, hA⟩ := hA
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, hA, Matrix.SpecialLinearGroup.coe_one, ← map_pow,
    ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one]

theorem odd_card_of_pow_three {Z : Type*} [Group Z] [Finite Z] (hZ : ∀ z : Z, z ^ 3 = 1) :
    Odd (Nat.card Z) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 Z := fun z => ⟨1, by rw [pow_one, hZ]⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp
  rw [hn]
  exact Odd.pow (by decide)

theorem ordProj_two_card_projectiveSL_three [Finite K] (hq : Odd (Nat.card K)) :
    ordProj[2] (Nat.card (projectiveSL 3 K)) =
      ordProj[2] (Nat.card K - 1) ^ 2 * ordProj[2] (Nat.card K + 1) := by
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hZ : Odd (Nat.card (scalars 3 K)) :=
    odd_card_of_pow_three fun z => Subtype.ext (pow_three_eq_one_of_mem_scalars z.2)
  rw [CFSG.LieType.Steinberg.ordProj_two_card_quotient_of_odd (scalars 3 K) hZ,
    CFSG.LieType.SteinbergBR.BlockPar.card_SL_three', ordProj_two_order_SL_three hq hq1]

section Model

variable (x : K)

@[expose] def sdMatA : Matrix (Fin 3) (Fin 3) K := !![x, x, 0; -x, x, 0; 0, 0, -1]

@[expose] def sdMatB : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, -1, 0; 0, 0, -1]

variable {x}

theorem det_sdMatA (hx : 2 * x ^ 2 = -1) : (sdMatA x).det = 1 := by
  simp [sdMatA, det_fin_three]
  linear_combination -hx

theorem det_sdMatB : (sdMatB : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [sdMatB, det_fin_three]
  simp

theorem sdMatA_sq (hx : 2 * x ^ 2 = -1) :
    sdMatA x * sdMatA x = !![0, -1, 0; 1, 0, 0; 0, 0, 1] := by
  rw [sdMatA, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> first | linear_combination hx | linear_combination -hx

theorem sdMatA_cube :
    !![0, -1, 0; 1, 0, 0; 0, 0, 1] * sdMatA x = !![x, -x, 0; x, x, 0; 0, 0, -1] := by
  rw [sdMatA, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sdMatB_conj : sdMatB * sdMatA x * sdMatB = !![x, -x, 0; x, x, 0; 0, 0, -1] := by
  rw [sdMatA, sdMatB, mul_fin_three, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sdMatB_sq : (sdMatB : Matrix (Fin 3) (Fin 3) K) * sdMatB = 1 := by
  rw [sdMatB, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [one_apply]

theorem sdMat_fourth :
    (!![0, -1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) * !![0, -1, 0; 1, 0, 0; 0, 0, 1] =
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  rw [mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sdMat_eighth :
    (!![-1, 0, 0; 0, -1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] =
      1 := by
  rw [mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [one_apply]

@[expose] def sdA (hx : 2 * x ^ 2 = -1) : SpecialLinearGroup (Fin 3) K :=
  ⟨sdMatA x, det_sdMatA hx⟩

@[expose] def sdB : SpecialLinearGroup (Fin 3) K :=
  ⟨sdMatB, det_sdMatB⟩

theorem sd_relations (hx : 2 * x ^ 2 = -1) (h2 : (2 : K) ≠ 0) :
    orderOf (sdA hx) = 8 ∧ (sdB : SpecialLinearGroup (Fin 3) K) ^ 2 = 1 ∧
      sdB * sdA hx * sdB = sdA hx ^ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : ((sdA hx ^ 2 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![0, -1, 0; 1, 0, 0; 0, 0, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_pow, sq]
    exact sdMatA_sq hx
  have hA4 : ((sdA hx ^ 2 ^ 2 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
    rw [pow_two 2, pow_mul, Matrix.SpecialLinearGroup.coe_pow, hA2, sq, sdMat_fourth]
  have hA8 : sdA hx ^ 2 ^ (2 + 1) = 1 := by
    apply Subtype.ext
    rw [show 2 ^ (2 + 1) = 2 ^ 2 * 2 by norm_num, pow_mul, Matrix.SpecialLinearGroup.coe_pow,
      hA4, sq, sdMat_eighth, Matrix.SpecialLinearGroup.coe_one]
  have hA4' : ¬ sdA hx ^ 2 ^ 2 = 1 := by
    intro h
    have h1 := congrArg (fun g : SpecialLinearGroup (Fin 3) K =>
      (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
    simp only [hA4, Matrix.SpecialLinearGroup.coe_one, one_apply_eq] at h1
    apply h2
    simp only [of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one] at h1
    linear_combination -h1
  refine ⟨by rw [orderOf_eq_prime_pow hA4' hA8]; norm_num, ?_, ?_⟩
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, sq, Matrix.SpecialLinearGroup.coe_one]
    exact sdMatB_sq
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, pow_succ,
      Matrix.SpecialLinearGroup.coe_mul, hA2]
    exact (sdMatB_conj).trans sdMatA_cube.symm

end Model

theorem exists_semidihedral_projectiveSL_three [Finite K] (hK : Nat.card K % 8 = 3) :
    ∃ a b : projectiveSL 3 K, orderOf a = 8 ∧ b ^ 2 = 1 ∧ b * a * b = a ^ 3 := by
  have := Fintype.ofFinite K
  have hsq : IsSquare (-2 : K) :=
    FiniteField.isSquare_neg_two_iff.2 (by rw [← Nat.card_eq_fintype_card]; omega)
  have hc : ringChar K ≠ 2 := by
    rw [Ne, FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card]
    omega
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hc
  obtain ⟨s, hs⟩ := hsq
  set x : K := s / 2 with hxdef
  have hx : 2 * x ^ 2 = -1 := by
    rw [hxdef]
    field_simp
    linear_combination -hs
  obtain ⟨ha, hb, hrel⟩ := sd_relations hx h2
  obtain ⟨ha', hb', hrel'⟩ := semidihedral_quotient (Z := scalars 3 K)
    (fun z hz => pow_three_eq_one_of_mem_scalars hz) ha hb hrel
  exact ⟨_, _, ha', hb', hrel'⟩

theorem projectiveSL_three_two_part [Finite K] (hq : Odd (Nat.card K)) :
    16 ≤ ordProj[2] (Nat.card (projectiveSL 3 K)) ∧
      (ordProj[2] (Nat.card (projectiveSL 3 K)) = 16 →
        ∃ a b : projectiveSL 3 K, orderOf a = 8 ∧ b ^ 2 = 1 ∧ b * a * b = a ^ 3) := by
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  rw [ordProj_two_card_projectiveSL_three hq]
  exact ⟨sixteen_le_sq_mul hq hq1, fun h =>
    exists_semidihedral_projectiveSL_three (mod_eight_of_sq_mul_eq hq hq1 h)⟩

end CFSG.Quasithin.SteinbergCD
