module

public import CFSG.Foundations.Basic
public import CFSG.LieType.Chevalley.RankOneGaussian
import CFSG.LinearAlgebra.SteinbergBQEvenSL2OddCyclic
import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup
import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents

public noncomputable section

namespace CFSG.LocalAnalysis.SteinbergCA

open Matrix CFSG.LieType.Chevalley

theorem mul_add_mul_fin_two {K : Type*} [CommRing K] (X Y : Matrix (Fin 2) (Fin 2) K) :
    X * Y + Y * X = X.trace • Y + Y.trace • X + ((X * Y).trace - X.trace * Y.trace) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;> ring

theorem trace_eq_zero_of_mul_self_eq_zero {K : Type*} [Field K] {N : Matrix (Fin 2) (Fin 2) K}
    (hN : N ≠ 0) (hNN : N * N = 0) : N.trace = 0 ∧ N.det = 0 := by
  have hdet : N.det = 0 := by
    by_contra h
    have hu : IsUnit N := (Matrix.isUnit_iff_isUnit_det N).2 (isUnit_iff_ne_zero.2 h)
    apply hN
    obtain ⟨u, rfl⟩ := hu
    have := congrArg (fun M => (↑u⁻¹ : Matrix (Fin 2) (Fin 2) K) * M) hNN
    simp [← Matrix.mul_assoc] at this
  refine ⟨?_, hdet⟩
  have h := CFSG.LinearAlgebra.SteinbergBQ.mul_self_fin_two N
  rw [hNN, hdet, zero_smul, sub_zero] at h
  by_contra htr
  apply hN
  have := congrArg (fun M => (N.trace)⁻¹ • M) h
  simpa [smul_smul, inv_mul_cancel₀ htr] using this.symm

theorem mul_self_eq_one_of_commute_involution {K : Type*} [Field K] [CharP K 2]
    {A B : SpecialLinearGroup (Fin 2) K} (hA : A * A = 1) (hA1 : A ≠ 1)
    (hAB : A * B = B * A) : B * B = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set a := (A : Matrix (Fin 2) (Fin 2) K) with ha_def
  set b := (B : Matrix (Fin 2) (Fin 2) K) with hb_def
  have ha : a * a = 1 := by
    have := congrArg (fun M : SpecialLinearGroup (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K)) hA
    simpa using this
  have hab : a * b = b * a := by
    have := congrArg (fun M : SpecialLinearGroup (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K)) hAB
    simpa using this
  have hdetb : b.det = 1 := B.2
  have h11 : (1 : Matrix (Fin 2) (Fin 2) K) + 1 = 0 := by
    rw [← two_smul K (1 : Matrix (Fin 2) (Fin 2) K), h2, zero_smul]
  set N := a + 1 with hN_def
  have hN0 : N ≠ 0 := by
    intro h
    apply hA1
    have : a = 1 := by
      have : a = -1 := eq_neg_of_add_eq_zero_left h
      rw [this, neg_eq_iff_add_eq_zero, h11]
    exact Subtype.ext this
  have hNN : N * N = 0 := by
    rw [hN_def, add_mul, mul_add, mul_add, ha, mul_one, one_mul, one_mul]
    rw [show (1 : Matrix (Fin 2) (Fin 2) K) + a + (a + 1) = (a + a) + (1 + 1) by abel]
    rw [h11, ← two_smul K a, h2, zero_smul, add_zero]
  have hbN : b * N = N * b := by
    rw [hN_def, mul_add, add_mul, hab, mul_one, one_mul]
  obtain ⟨htrN, -⟩ := trace_eq_zero_of_mul_self_eq_zero hN0 hNN
  have hbN0 : b * N ≠ 0 := by
    intro h
    apply hN0
    have hbu : IsUnit b := (Matrix.isUnit_iff_isUnit_det b).2 (by rw [hdetb]; exact isUnit_one)
    obtain ⟨u, hu⟩ := hbu
    have := congrArg (fun M => (↑u⁻¹ : Matrix (Fin 2) (Fin 2) K) * M) h
    simpa [← hu, ← Matrix.mul_assoc] using this
  have hbNbN : (b * N) * (b * N) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc N, ← hbN, Matrix.mul_assoc, hNN,
      Matrix.mul_zero, Matrix.mul_zero]
  obtain ⟨htrbN, -⟩ := trace_eq_zero_of_mul_self_eq_zero hbN0 hbNbN
  have hpol := mul_add_mul_fin_two b N
  rw [← hbN, htrN, htrbN, zero_smul, add_zero, mul_zero, sub_zero, zero_smul, add_zero,
    ← two_smul K (b * N), h2, zero_smul] at hpol
  have htrb : b.trace = 0 := by
    by_contra htr
    apply hN0
    have := congrArg (fun M => (b.trace)⁻¹ • M) hpol
    simpa [smul_smul, inv_mul_cancel₀ htr] using this.symm
  have hbb : b * b = 1 := by
    rw [CFSG.LinearAlgebra.SteinbergBQ.mul_self_fin_two, htrb, hdetb, zero_smul, one_smul,
      zero_sub, neg_eq_iff_add_eq_zero, h11]
  exact Subtype.ext hbb

theorem orderOf_ne_two_mul_of_charTwo {K : Type*} [Field K] [CharP K 2] {m : ℕ} (hm : 3 ≤ m)
    (g : SpecialLinearGroup (Fin 2) K) : orderOf g ≠ 2 * m := by
  intro hg
  have hx : g ^ m * g ^ m = 1 := by rw [← pow_add, ← two_mul, ← hg, pow_orderOf_eq_one]
  have hx1 : g ^ m ≠ 1 := by
    intro h
    have := orderOf_le_of_pow_eq_one (by omega) h
    omega
  have hcomm : g ^ m * g ^ 2 = g ^ 2 * g ^ m := by rw [← pow_add, ← pow_add, add_comm]
  have hy := mul_self_eq_one_of_commute_involution hx hx1 hcomm
  rw [← pow_add] at hy
  have := orderOf_dvd_of_pow_eq_one hy
  rw [hg] at this
  have h4 : 2 * m ≤ 4 := Nat.le_of_dvd (by norm_num) this
  omega

theorem orderOf_ne_two_mul_of_mulEquiv_SL2 {S : Type*} [Group S] {K : Type*} [Field K]
    [CharP K 2] (eS : S ≃* SpecialLinearGroup (Fin 2) K) {m : ℕ} (hm : 3 ≤ m) (g : S) :
    orderOf g ≠ 2 * m := by
  rw [← MulEquiv.orderOf_eq eS g]
  exact orderOf_ne_two_mul_of_charTwo hm (eS g)

theorem uSL_zero_eq_one_of_SL2 {F : Type*} [Field F] : uSL (0 : F) = 1 := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [coe_uSL]

theorem uSL_mul_uSL {F : Type*} [Field F] (a b : F) : uSL a * uSL b = uSL (a + b) := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_uSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      add_comm]

theorem uSL_pow {F : Type*} [Field F] (a : F) (n : ℕ) : uSL a ^ n = uSL (n * a) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, uSL_zero_eq_one_of_SL2]
  | succ n ih =>
    rw [pow_succ, ih, uSL_mul_uSL]
    congr 1
    push_cast
    ring

theorem uSL_one_ne_one_and_ne_neg_one {F : Type*} [Field F] :
    uSL (1 : F) ≠ 1 ∧ uSL (1 : F) ≠ -1 := by
  constructor
  · intro h
    have := congrArg (fun M : SpecialLinearGroup (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 0 1)
      h
    simp [coe_uSL] at this
  · intro h
    have := congrArg (fun M : SpecialLinearGroup (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 0 1)
      h
    simp [coe_uSL] at this

theorem two_dvd_card_of_mulEquiv_SL2 {S : Type*} [Group S] {K : Type*} [Field K] [CharP K 2]
    (eS : S ≃* SpecialLinearGroup (Fin 2) K) : 2 ∣ Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu2 : uSL (1 : K) ^ 2 = 1 := by
    rw [uSL_pow]
    have : ((2 : ℕ) : K) * 1 = 0 := by rw [mul_one]; exact CharP.cast_eq_zero K 2
    rw [this, uSL_zero_eq_one_of_SL2]
  have hord : orderOf (eS.symm (uSL 1)) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hu2 uSL_one_ne_one_and_ne_neg_one.1
  rw [← hord]
  exact orderOf_dvd_natCard _

theorem orderOf_neg_one_mul_uSL_one {F G : Type*} [Field F] [Group G] {p : ℕ} [Fact p.Prime]
    [CharP F p] (hp2 : p ≠ 2) (φ : SpecialLinearGroup (Fin 2) F →* G) (hneg : φ (-1) ≠ 1)
    (hu : φ (uSL 1) ≠ 1) : orderOf (φ (-1) * φ (uSL 1)) = 2 * p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : orderOf (φ (-1)) = 2 :=
    orderOf_eq_prime (by rw [← map_pow, neg_one_sq, map_one]) hneg
  have hp : orderOf (φ (uSL 1)) = p := by
    refine orderOf_eq_prime ?_ hu
    rw [← map_pow, uSL_pow, mul_one, CharP.cast_eq_zero F p, uSL_zero_eq_one_of_SL2, map_one]
  have hcomm : Commute (φ (-1)) (φ (uSL 1)) := by
    change φ (-1) * φ (uSL 1) = φ (uSL 1) * φ (-1)
    rw [← map_mul, ← map_mul, neg_one_mul, mul_neg_one]
  rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by
    rw [h2, hp, Nat.coprime_two_left]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2), h2, hp]

theorem false_of_mulEquiv_SL2_of_hom {G : Type*} [Group G] {S : Subgroup G} {K : Type*} [Field K]
    [CharP K 2] (eS : S ≃* SpecialLinearGroup (Fin 2) K) {F : Type*} [Field F] {p : ℕ}
    [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) (φ : SpecialLinearGroup (Fin 2) F →* G)
    (hφS : ∀ A, φ A ∈ S) (hneg : φ (-1) ≠ 1) (hu : φ (uSL 1) ≠ 1) : False := by
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have h := orderOf_neg_one_mul_uSL_one hp2 φ hneg hu
  have hmem : φ (-1) * φ (uSL 1) ∈ S := mul_mem (hφS _) (hφS _)
  apply orderOf_ne_two_mul_of_mulEquiv_SL2 eS hp3 ⟨_, hmem⟩
  rw [Subgroup.orderOf_mk, h]

theorem isPComponent_two_of_normal_simple {N : Type*} [Group N] [Finite N] (S : Subgroup N)
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a)
    (h2 : 2 ∣ Nat.card S) : CFSG.IsPComponent 2 S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hSs
  refine CFSG.LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2
    ⟨CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_of_isSimpleGroup hSnab, hSn.isSubnormal⟩
    fun hle => ?_
  have hdvd : 2 ∣ Nat.card (CFSG.pPrimeCore 2 N) := h2.trans (Subgroup.card_dvd_of_le hle)
  exact absurd (Nat.Coprime.eq_one_of_dvd CFSG.pPrimeCore_coprime_card hdvd) (by norm_num)

theorem isPComponent_two_of_mulEquiv_SL2 {N : Type*} [Group N] [Finite N] (S : Subgroup N)
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a) {K : Type*}
    [Field K] [CharP K 2] (eS : S ≃* SpecialLinearGroup (Fin 2) K) : CFSG.IsPComponent 2 S :=
  isPComponent_two_of_normal_simple S hSn hSs hSnab (two_dvd_card_of_mulEquiv_SL2 eS)

end CFSG.LocalAnalysis.SteinbergCA
