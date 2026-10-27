module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKDefs
public import CFSG.Goldschmidt.Steps.Rank2List
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.H13.L829NK

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

namespace NKL2In

@[expose] def wSL (K : Type) [Field K] : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩

@[expose] def tSL {K : Type} [Field K] (a : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two_of]⟩

@[expose] def wS (K : Type) [Field K] : StatedSL 2 K :=
  ⟨Matrix.SpecialLinearGroup.toGL (wSL K), mem_statedSL_of_det (wSL K).2⟩

@[expose] def tS {K : Type} [Field K] (a : Kˣ) : StatedSL 2 K :=
  ⟨Matrix.SpecialLinearGroup.toGL (tSL a), mem_statedSL_of_det (tSL a).2⟩

theorem val_wS (K : Type) [Field K] :
    (((wS K : StatedSL 2 K) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![0, 1; -1, 0] := rfl

theorem val_tS {K : Type} [Field K] (a : Kˣ) :
    (((tS a : StatedSL 2 K) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)] := rfl

theorem diag_pow {K : Type} [Field K] (a b : K) (k : ℕ) :
    (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) K) ^ k = !![a ^ k, 0; 0, b ^ k] := by
  induction k with
  | zero => simp [Matrix.one_fin_two]
  | succ k ih => rw [pow_succ, ih, Matrix.mul_fin_two]; simp [pow_succ]

theorem val_tS_pow {K : Type} [Field K] (a : Kˣ) (k : ℕ) :
    (((tS a ^ k : StatedSL 2 K) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(a : K) ^ k, 0; 0, ((a⁻¹ : Kˣ) : K) ^ k] := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, val_tS, diag_pow]

theorem mat_w_sq (K : Type) [Field K] :
    (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) * !![0, 1; -1, 0] =
      Matrix.scalar (Fin 2) (-1 : K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two, Matrix.scalar_apply]

theorem mat_wt_sq {K : Type} [Field K] (a b : K) (hab : a * b = 1) :
    ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) * !![a, 0; 0, b]) *
      ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) * !![a, 0; 0, b]) =
      Matrix.scalar (Fin 2) (-1 : K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two, Matrix.scalar_apply] <;>
    first | linear_combination hab | linear_combination (-1 : K) * hab

theorem mat_wt_entry {K : Type} [Field K] (a b : K) :
    ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) * !![a, 0; 0, b]) 0 1 = b := by
  simp [Matrix.mul_fin_two]

theorem mk_eq_one_iff {K : Type} [Field K] (x : StatedSL 2 K) :
    (QuotientGroup.mk x : StatedProj (StatedSL 2 K)) = 1 ↔
      ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) c = (x : GL (Fin 2) K) := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]

theorem mk_ne_one_of_entry {K : Type} [Field K] (x : StatedSL 2 K)
    (h : ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0) :
    (QuotientGroup.mk x : StatedProj (StatedSL 2 K)) ≠ 1 := by
  rw [Ne, mk_eq_one_iff]
  rintro ⟨c, hc⟩
  apply h
  have h01 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 0 1 = ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 := by
    rw [hc]
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h01.symm

theorem mk_w_mul_self (K : Type) [Field K] :
    (QuotientGroup.mk (wS K) : StatedProj (StatedSL 2 K)) * QuotientGroup.mk (wS K) = 1 := by
  rw [← QuotientGroup.mk_mul, mk_eq_one_iff]
  refine ⟨-1, Units.ext ?_⟩
  simp only [Subgroup.coe_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg,
    Units.val_one, val_wS]
  exact (mat_w_sq K).symm

theorem mk_wt_mul_self {K : Type} [Field K] (a : Kˣ) :
    (QuotientGroup.mk (wS K * tS a) : StatedProj (StatedSL 2 K)) *
      QuotientGroup.mk (wS K * tS a) = 1 := by
  rw [← QuotientGroup.mk_mul, mk_eq_one_iff]
  refine ⟨-1, Units.ext ?_⟩
  simp only [Subgroup.coe_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg,
    Units.val_one, val_wS, val_tS]
  exact (mat_wt_sq (a : K) ((a⁻¹ : Kˣ) : K) (by simp)).symm

theorem six_le_orderOf_mk_tS {K : Type} [Field K] [Finite K] (a : Kˣ) (ha : 11 ≤ orderOf a) :
    6 ≤ orderOf (QuotientGroup.mk (tS a) : StatedProj (StatedSL 2 K)) := by
  by_contra hlt
  rw [not_le] at hlt
  have hpos := orderOf_pos (QuotientGroup.mk (tS a) : StatedProj (StatedSL 2 K))
  have hpow := pow_orderOf_eq_one (QuotientGroup.mk (tS a) : StatedProj (StatedSL 2 K))
  rw [← QuotientGroup.mk_pow, mk_eq_one_iff] at hpow
  obtain ⟨c, hc⟩ := hpow
  set k := orderOf (QuotientGroup.mk (tS a) : StatedProj (StatedSL 2 K)) with hk
  have hmat : Matrix.scalar (Fin 2) (c : K) = !![(a : K) ^ k, 0; 0, ((a⁻¹ : Kˣ) : K) ^ k] := by
    have h : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) =
          (((tS a ^ k : StatedSL 2 K) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
      congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) hc
    rw [Matrix.GeneralLinearGroup.coe_scalar, val_tS_pow] at h
    exact h
  have h00 : (c : K) = (a : K) ^ k := by
    simpa [Matrix.scalar_apply] using congrFun (congrFun hmat 0) 0
  have h11 : (c : K) = ((a⁻¹ : Kˣ) : K) ^ k := by
    simpa [Matrix.scalar_apply] using congrFun (congrFun hmat 1) 1
  have hunit : a ^ k = (a⁻¹) ^ k := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    exact h00.symm.trans h11)
  have h2k : a ^ (2 * k) = 1 := by
    rw [two_mul, pow_add]
    nth_rewrite 2 [hunit]
    rw [← mul_pow, mul_inv_cancel, one_pow]
  have hle : orderOf a ≤ 2 * k := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one h2k)
  omega

theorem exists_involutions (K : Type) [Field K] [Finite K] (hK : 17 ≤ Nat.card K) :
    ∃ z₁ z₂ : StatedProj (StatedSL 2 K), orderOf z₁ = 2 ∧ orderOf z₂ = 2 ∧
      6 ≤ orderOf (z₁ * z₂) := by
  obtain ⟨a, ha⟩ : ∃ a : Kˣ, 11 ≤ orderOf a := by
    obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
    exact ⟨a, by rw [ha, Nat.card_units]; omega⟩
  refine ⟨QuotientGroup.mk (wS K), QuotientGroup.mk (wS K * tS a), ?_, ?_, ?_⟩
  · refine orderOf_eq_prime ?_ (mk_ne_one_of_entry _ ?_)
    · rw [sq]
      exact mk_w_mul_self K
    · simp [val_wS]
  · refine orderOf_eq_prime ?_ (mk_ne_one_of_entry _ ?_)
    · rw [sq]
      exact mk_wt_mul_self a
    · simp only [Subgroup.coe_mul, Units.val_mul, val_wS, val_tS]
      rw [mat_wt_entry]
      exact Units.ne_zero _
  · have hprod : (QuotientGroup.mk (wS K) : StatedProj (StatedSL 2 K)) *
        QuotientGroup.mk (wS K * tS a) = QuotientGroup.mk (tS a) := by
      have h2 : (QuotientGroup.mk (wS K * tS a) : StatedProj (StatedSL 2 K)) =
          QuotientGroup.mk (wS K) * QuotientGroup.mk (tS a) := rfl
      rw [h2, ← mul_assoc, mk_w_mul_self K, one_mul]
    rw [hprod]
    exact six_le_orderOf_mk_tS a ha

theorem seventeen_le (p e : ℕ) (hp : p.Prime) (h3 : 3 < p) (he : e = 1 ∨ e = 2)
    (h8 : p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) (h7 : p ^ e ≠ 7) (h25 : p ^ e ≠ 25) :
    17 ≤ p ^ e := by
  by_contra hlt
  rw [not_le] at hlt
  have hp16 : p ≤ 16 := by
    rcases he with rfl | rfl
    · rw [pow_one] at hlt
      omega
    · nlinarith
  interval_cases p <;> rcases he with rfl | rfl <;> revert hp h8 h7 h25 hlt <;> norm_num

end NKL2In

theorem nk_l2_uin (p e : ℕ) (hp : p.Prime) (h3 : 3 < p) (he : e = 1 ∨ e = 2)
    (h8 : p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) (h7 : p ^ e ≠ 7) (h25 : p ^ e ≠ 25)
    (X : Type) [Group X] (hX : IsPSL 2 p e X) : UIn X := by
  have hX' := hX
  obtain ⟨-, K, hK, hKf, hcard, ⟨φ⟩⟩ := hX'
  haveI : Finite X := Finite.of_equiv (StatedProj (StatedSL 2 K)) φ.symm.toEquiv
  have hconj := (CFSG.Goldschmidt.Rank2List.psl2_concl X hp (by omega) (by omega) h8 hX).1
  have h17 : 17 ≤ Nat.card K := by
    rw [hcard]
    exact NKL2In.seventeen_le p e hp h3 he h8 h7 h25
  obtain ⟨z₁, z₂, h1, h2, h6⟩ := NKL2In.exists_involutions K h17
  have hz₁ : orderOf (φ.symm z₁) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact h1
  have hz₂ : orderOf (φ.symm z₂) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact h2
  obtain ⟨g, hg⟩ := isConj_iff.1 (hconj _ _ hz₁ hz₂)
  unfold UIn
  refine ⟨hconj, φ.symm z₁, g⁻¹, hz₁, ?_⟩
  rw [inv_inv, hg, ← map_mul φ.symm, MulEquiv.orderOf_eq]
  exact h6

end CFSG.Quasithin.H13.L829NK
