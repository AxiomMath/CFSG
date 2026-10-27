module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Families
public import CFSG.Quasithin.Vol2.Ch12Sec8OneSix

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.C10KH

open CFSG.Assembly.LowTwoRank Matrix

variable {K : Type} [Field K]

theorem exists_omega_of_card_25 [Finite K] (hK : Nat.card K = 25) :
    ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card Kˣ = 24 := by rw [Nat.card_units, hK]
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [hcard]; norm_num)
  refine ⟨u, ?_, fun h => ?_⟩
  · have h1 := pow_orderOf_eq_one u
    rw [hu] at h1
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  · rw [show u = 1 from Units.ext h, orderOf_one] at hu
    norm_num at hu

@[expose] def tMat (ω : K) : Matrix (Fin 3) (Fin 3) K := !![ω, 0, 0; 0, ω ^ 2, 0; 0, 0, 1]

@[expose] def sMat : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem det_tMat {ω : K} (hω : ω ^ 3 = 1) : (tMat ω).det = 1 := by
  rw [tMat, det_fin_three]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
    cons_val_fin_one, head_cons, tail_cons, head_fin_const]
  linear_combination hω

theorem det_sMat : (sMat : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [sMat, det_fin_three]
  simp

theorem tMat_unitary {ω : K} (hω : ω ^ 3 = 1) :
    ((tMat ω).map (· ^ 5))ᵀ * tMat ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tMat, Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination (ω ^ 3 + 1) * hω
  · linear_combination (ω ^ 9 + ω ^ 6 + ω ^ 3 + 1) * hω

theorem sMat_unitary : ((sMat : Matrix (Fin 3) (Fin 3) K).map (· ^ 5))ᵀ * sMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem tMat_mul_sMat {ω : K} (hω : ω ^ 3 = 1) :
    tMat ω * sMat = ω • (sMat * tMat ω) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tMat, sMat, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals first | ring1 | linear_combination hω | linear_combination (-1 : K) * hω

theorem sMat_pow_three : (sMat : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sMat, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem tMat_pow_three {ω : K} (hω : ω ^ 3 = 1) : tMat ω ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tMat, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination hω
  · linear_combination (ω ^ 3 + 1) * hω

theorem tMat_apply_one_zero_pow {ω : K} (n : ℕ) (c : K) :
    (tMat ω ^ n * Matrix.scalar (Fin 3) c) 1 0 = 0 := by
  have h : tMat ω = diagonal ![ω, ω ^ 2, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [tMat]
  rw [h, diagonal_pow, Matrix.scalar_apply, diagonal_mul_diagonal]
  exact diagonal_apply_ne _ (by decide)

@[expose] noncomputable def tGL {ω : K} (hω : ω ^ 3 = 1) : GL (Fin 3) K :=
  GeneralLinearGroup.mk'' (tMat ω) (by rw [det_tMat hω]; exact isUnit_one)

@[expose] noncomputable def sGL : GL (Fin 3) K :=
  GeneralLinearGroup.mk'' sMat (by rw [det_sMat]; exact isUnit_one)

theorem two_le_pRank_statedProj_of_mem [Finite K] {H : Subgroup (GL (Fin 3) K)} {ω : K}
    (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (ht : tGL hω ∈ H) (hs : sGL ∈ H) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj H)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω
  let N := (StatedScalars (Fin 3) K).subgroupOf H
  let π := QuotientGroup.mk' N
  have : Finite (StatedProj H) := Finite.of_surjective π (QuotientGroup.mk'_surjective N)
  let t : H := ⟨tGL hω, ht⟩
  let s : H := ⟨sGL, hs⟩
  have coe_t : (((t : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) = tMat ω := rfl
  have coe_s : (((s : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) = sMat := rfl
  refine CFSG.QuasithinUnique.Vol2Native.two_le_pRank_of_gens (x := π t) (y := π s)
    ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow]
    convert map_one π
    exact Subtype.ext (Units.ext (by
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_t, tMat_pow_three hω]; rfl))
  · rw [← map_pow]
    convert map_one π
    exact Subtype.ext (Units.ext (by
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_s, sMat_pow_three]; rfl))
  · have key : ((s * t : H) : GL (Fin 3) K) =
        ((t * s : H) : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ω hω0)⁻¹ := by
      apply Units.ext
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Subgroup.coe_mul, Subgroup.coe_mul,
        Units.val_mul, Units.val_mul, coe_t, coe_s, tMat_mul_sMat hω, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, mul_one, smul_smul,
        Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hω0, one_smul]
    show π t * π s = π s * π t
    rw [← map_mul, ← map_mul]
    refine (QuotientGroup.eq).mpr ?_
    rw [Subgroup.mem_subgroupOf]
    refine ⟨(Units.mk0 ω hω0)⁻¹, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, key, inv_mul_cancel_left]
  · intro h
    have hm := (QuotientGroup.eq_one_iff _).mp h
    rw [Subgroup.mem_subgroupOf] at hm
    obtain ⟨c, hc⟩ := hm
    have hc' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hc
    simp only [GeneralLinearGroup.coe_scalar, coe_t] at hc'
    have e00 : Matrix.scalar (Fin 3) (c : K) 0 0 = tMat ω 0 0 := congrFun (congrFun hc' 0) 0
    have e22 : Matrix.scalar (Fin 3) (c : K) 2 2 = tMat ω 2 2 := congrFun (congrFun hc' 2) 2
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at e00 e22
    have t00 : tMat ω 0 0 = ω := by simp [tMat]
    have t22 : tMat ω 2 2 = 1 := by simp [tMat]
    rw [t00] at e00
    rw [t22] at e22
    exact hω1 (e00.symm.trans e22)
  · intro n h
    rw [← map_pow] at h
    have hm := (QuotientGroup.eq).mp h
    rw [Subgroup.mem_subgroupOf] at hm
    obtain ⟨c, hc⟩ := hm
    have h1 : ((s : H) : GL (Fin 3) K) =
        ((t ^ n : H) : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c := by
      rw [hc, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    have h2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 0) h1
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Subgroup.coe_pow,
      Units.val_pow_eq_pow_val, coe_t, coe_s, tMat_apply_one_zero_pow] at h2
    simp [sMat] at h2

theorem two_le_pRank_statedProj_su35 [Finite K] (hK : Nat.card K = 25) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU 3 5 K))) := by
  have : CharP K 5 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    (k := 2) Nat.prime_five (by norm_num) (by rw [hK]; norm_num)
  obtain ⟨ω, hω, hω1⟩ := exists_omega_of_card_25 hK
  exact two_le_pRank_statedProj_of_mem hω hω1
    (Subgroup.subset_closure ⟨det_tMat hω, tMat_unitary hω⟩)
    (Subgroup.subset_closure ⟨det_sMat, sMat_unitary⟩)

theorem two_le_pRank_statedProj_sl3 [Finite K] {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL 3 K))) :=
  two_le_pRank_statedProj_of_mem hω hω1 (Subgroup.subset_closure (det_tMat hω))
    (Subgroup.subset_closure det_sMat)

theorem two_le_pRank_psu35 {X : Type} [Group X] [Finite X] (h : IsPSU 3 5 1 X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
  exact two_le_pRank_statedProj_su35 (by rw [hK]; norm_num)

theorem two_le_pRank_su35 {X : Type} [Group X] [Finite X] (h : IsSU3 5 X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
  have : Finite (StatedProj (StatedSU 3 5 K)) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  exact CFSG.Quasithin.H13.L128P.two_le_pRank_of_surjective' Nat.prime_three (by norm_num)
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (two_le_pRank_statedProj_su35 (by rw [hK]; norm_num))

end CFSG.Quasithin.Vol2.Ch11.SecA.C10KH
