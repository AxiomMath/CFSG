module

public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Even
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoGeneration
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.Quasithin.E6

open Matrix CFSG.LocalAnalysis.ComponentInitial

theorem ringEquiv_pow_eq_one {K : Type} [Field K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (σ : K ≃+* K) : σ ^ n = 1 := by
  have hcard : Nat.card (K ≃+* K) = n :=
    (finite_field_automorphism_fixed_field_cardinality Nat.prime_two hn hK).choose_spec.2.2.2.1
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have h := pow_card_eq_one' (G := K ≃+* K) (x := σ)
  rwa [hcard] at h

section Linear

open LinearFlag

variable {K : Type} [Field K] [Finite K]

theorem sq_mem_semilinearAutGroup (α : MulAut (projectiveSL 3 K)) :
    α ^ 2 ∈ semilinearAutGroup 3 K := by
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) (n := 3) le_rfl
  obtain ⟨-, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (n := 3) (K := K)
  have hidx' : (semilinearAutGroup 3 K).index ≤ 2 := by
    have h2 : (semilinearAutGroup 3 K).relIndex (standardAutGroup 3 K) ≤ 2 := hidx
    rwa [hgenTop, Subgroup.relIndex_top_right] at h2
  have h0 : (semilinearAutGroup 3 K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (by omega : (semilinearAutGroup 3 K).index = 1 ∨ (semilinearAutGroup 3 K).index = 2)
    with h1 | h2
  · rw [Subgroup.index_eq_one.mp h1]
    exact Subgroup.mem_top _
  · rw [sq]
    exact Subgroup.mul_self_mem_of_index_two h2 α

omit [Finite K] in
theorem exists_pow_conjAut_mul_fieldAut (B : GL (Fin 3) K) (τ : K ≃+* K) (k : ℕ) :
    ∃ C : GL (Fin 3) K, (conjAut 3 K B * fieldAut 3 K τ) ^ k =
      conjAut 3 K C * fieldAut 3 K (τ ^ k) := by
  induction k with
  | zero => exact ⟨1, by rw [pow_zero, pow_zero, map_one, map_one, one_mul]⟩
  | succ k ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨C * GeneralLinearGroup.map ((τ ^ k : K ≃+* K) : K →+* K) B, ?_⟩
    rw [pow_succ, hC, conjAut_mul_fieldAut_mul, pow_succ]

omit [Finite K] in
theorem conjAut_pow_three_mem_inner (C : GL (Fin 3) K) :
    conjAut 3 K C ^ 3 ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  set d := GeneralLinearGroup.det C with hd
  set S : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) d⁻¹ * C ^ 3 with hSdef
  have hdetS : GeneralLinearGroup.det S = 1 := by
    have h1 : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) d⁻¹) = d⁻¹ ^ 3 := by
      ext
      simp [GeneralLinearGroup.scalar]
    rw [hSdef, map_mul, map_pow, ← hd, h1, ← mul_pow, inv_mul_cancel, one_pow]
  have hS : (S : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hdetS
    simpa using this
  let s : SpecialLinearGroup (Fin 3) K := ⟨(S : Matrix (Fin 3) (Fin 3) K), hS⟩
  have hs : SpecialLinearGroup.toGL s = S := by
    ext1
    rfl
  refine ⟨proj 3 K s, ?_⟩
  rw [← conjAut_toGL, hs, hSdef, map_mul, conjAut_scalar, one_mul, map_pow]

theorem pow_six_mul_mem_inner_projectiveSL {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (α : MulAut (projectiveSL 3 K)) :
    α ^ (6 * n) ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  obtain ⟨B, τ, hB⟩ := mem_semilinearAutGroup_iff.mp (sq_mem_semilinearAutGroup α)
  obtain ⟨C, hC⟩ := exists_pow_conjAut_mul_fieldAut B τ n
  rw [ringEquiv_pow_eq_one hn hK τ, map_one, mul_one] at hC
  have e : α ^ (6 * n) = ((α ^ 2) ^ n) ^ 3 := by
    rw [← pow_mul, ← pow_mul]
    ring_nf
  rw [e, hB, hC]
  exact conjAut_pow_three_mem_inner C

theorem mem_linearAutGroup_of_card_four (hK : Nat.card K = 2 ^ 2)
    {α : MulAut (projectiveSL 3 K)} {a : ℕ} (hα : α ^ 3 ^ a = 1) :
    α ∈ linearAutGroup 3 K := by
  obtain ⟨B, τ, hB⟩ := mem_semilinearAutGroup_iff.mp (sq_mem_semilinearAutGroup α)
  obtain ⟨C, hC⟩ := exists_pow_conjAut_mul_fieldAut B τ 2
  rw [ringEquiv_pow_eq_one (by norm_num) hK τ, map_one, mul_one] at hC
  have h4 : α ^ 4 ∈ linearAutGroup 3 K := by
    rw [show α ^ 4 = (α ^ 2) ^ 2 by rw [← pow_mul], hB, hC]
    exact conjAut_mem_linearAutGroup C
  have hcop : Nat.Coprime 4 (orderOf α) :=
    (Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 4 3)).coprime_dvd_right
      (orderOf_dvd_of_pow_eq_one hα)
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hk]
  exact pow_mem h4 k

omit [Finite K] in
theorem conjAut_mem_inner_of_det_eq_one {A : GL (Fin 3) K} (hA : GeneralLinearGroup.det A = 1) :
    conjAut 3 K A ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  have hA' : (A : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hA
    simpa using this
  let s : SpecialLinearGroup (Fin 3) K := ⟨(A : Matrix (Fin 3) (Fin 3) K), hA'⟩
  have hs : SpecialLinearGroup.toGL s = A := by
    ext1
    rfl
  exact ⟨proj 3 K s, by rw [← conjAut_toGL, hs]⟩

theorem exists_mul_pow_mem_inner_L34 (hK : Nat.card K = 2 ^ 2) {α β : MulAut (projectiveSL 3 K)}
    {a b : ℕ} (hα : α ^ 3 ^ a = 1) (hβ : β ^ 3 ^ b = 1)
    (hαI : α ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) :
    ∃ k : ℕ, β * α ^ k ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp (mem_linearAutGroup_of_card_four hK hα)
  obtain ⟨B, rfl⟩ := mem_linearAutGroup_iff.mp (mem_linearAutGroup_of_card_four hK hβ)
  have hA1 : GeneralLinearGroup.det A ≠ 1 := fun h => hαI (conjAut_mem_inner_of_det_eq_one h)
  have hunits : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]; norm_num
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp
    (mem_powers_of_prime_card hunits hA1 (g' := (GeneralLinearGroup.det B)⁻¹))
  refine ⟨k, ?_⟩
  rw [← map_pow, ← map_mul]
  apply conjAut_mem_inner_of_det_eq_one
  rw [map_mul, map_pow, hk, mul_inv_cancel]

end Linear

section Symplectic

open SymplecticHigher CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.KFacts

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem exists_pow_spConjAut_mul_fieldAut (B : gsp 2 F) (τ : F ≃+* F) (k : ℕ) :
    ∃ C : gsp 2 F, (conjAut 2 F B * fieldAut 2 F τ) ^ k = conjAut 2 F C * fieldAut 2 F (τ ^ k) := by
  induction k with
  | zero => exact ⟨1, by rw [pow_zero, pow_zero, map_one, map_one, one_mul]⟩
  | succ k ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨C * gspFieldMap (τ ^ k) B, ?_⟩
    rw [pow_succ, hC, conjAut_mul_fieldAut_mul, pow_succ]

theorem pow_two_mul_mem_inner_sp4 {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (α : MulAut (StatedProj (StatedSp 2 F))) : IsInnerAut (α ^ (2 * n)) := by
  obtain ⟨-, -, -, hidx⟩ :=
    CFSG.ComponentClassification.CatalogueBSymplecticTwo.kernel_generation (K := F)
  have h0 : (spSemilinearAutGroup 2 F).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hα2 : α ^ 2 ∈ spSemilinearAutGroup 2 F := by
    rcases (by omega : (spSemilinearAutGroup 2 F).index = 1 ∨
      (spSemilinearAutGroup 2 F).index = 2) with h1 | h2
    · rw [Subgroup.index_eq_one.mp h1]
      exact Subgroup.mem_top _
    · rw [sq]
      exact Subgroup.mul_self_mem_of_index_two h2 α
  obtain ⟨B, τ, hB⟩ := mem_spSemilinearAutGroup_iff.mp hα2
  obtain ⟨C, hC⟩ := exists_pow_spConjAut_mul_fieldAut B τ n
  rw [ringEquiv_pow_eq_one hn hF τ, map_one, mul_one] at hC
  rw [pow_mul, hB, hC]
  exact conjAut_mem_inner_of_charTwo C

end Symplectic

end CFSG.Quasithin.E6
