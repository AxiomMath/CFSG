module

public import CFSG.Blueprint.ChevalleyInfinitesimals
public import CFSG.Blueprint.ChevalleyWeyl
import CFSG.CharacterTheory.Semidihedral.FixedFieldData

public section

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof

open CFSG.Blueprint.Chevalley Polynomial


variable {τ : Tag} {K L : Type} [Field K] [Field L]

theorem exists_frobenius_pow' {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (τ' : K ≃+* K) : ∃ k : ℕ, k < f ∧ ∀ a : K, τ' a = a ^ (p ^ k) := by
  obtain ⟨φ, hφ, hord, hzp, -⟩ :=
    CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality p f hp hf K
      hK
  have hτ : τ' ∈ Subgroup.zpowers φ := hzp ▸ Subgroup.mem_top τ'
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
  have hf0 : (f : ℤ) ≠ 0 := by exact_mod_cast (by omega : f ≠ 0)
  refine ⟨(m % (f : ℤ)).toNat, ?_, ?_⟩
  · have h1 : m % (f : ℤ) < f := Int.emod_lt_of_pos m (by exact_mod_cast hf)
    have h2 : 0 ≤ m % (f : ℤ) := Int.emod_nonneg m hf0
    omega
  · have hpow : ∀ (n : ℕ) (a : K), (φ ^ n) a = a ^ (p ^ n) := by
      intro n
      induction n with
      | zero => intro a; simp
      | succ n ih =>
        intro a
        rw [pow_succ', RingAut.mul_apply, ih, hφ, ← pow_mul, pow_succ]
    have h3 : φ ^ m = φ ^ ((m % (f : ℤ)).toNat) := by
      have := zpow_mod_orderOf φ m
      rw [hord] at this
      rw [← this]
      have h2 : 0 ≤ m % (f : ℤ) := Int.emod_nonneg m hf0
      rw [← zpow_natCast, Int.toNat_of_nonneg h2]
    intro a
    rw [h3, hpow]

theorem coeff_one_eq_zero_of_forall [Fintype K] (ι : K →+* L) {m : ℕ} (hm : 2 ≤ m)
    (hq : 3 * m < Fintype.card K) (x y : ℕ → L)
    (h : ∀ c : K, ∑ k ∈ Finset.range 4, (ι c ^ m) ^ k * y k =
      ∑ k ∈ Finset.range 4, ι c ^ k * x k) : x 1 = 0 := by
  set P : L[X] := ∑ k ∈ Finset.range 4, C (y k) * X ^ (m * k) -
    ∑ k ∈ Finset.range 4, C (x k) * X ^ k with hP
  have hdeg : P.natDegree ≤ 3 * m := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
      have hk' : k ≤ 3 := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hk
      refine (natDegree_C_mul_X_pow_le _ _).trans ?_
      nlinarith
    · refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
      have hk' : k ≤ 3 := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hk
      refine (natDegree_C_mul_X_pow_le _ _).trans ?_
      omega
  have hP0 : P = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero P ι.injective (fun c => ?_)
      (hdeg.trans_lt hq)
    simp only [hP, eval_sub, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [sub_eq_zero]
    calc ∑ k ∈ Finset.range 4, y k * ι c ^ (m * k)
        = ∑ k ∈ Finset.range 4, (ι c ^ m) ^ k * y k :=
          Finset.sum_congr rfl fun k _ => by rw [pow_mul, mul_comm]
      _ = ∑ k ∈ Finset.range 4, ι c ^ k * x k := h c
      _ = ∑ k ∈ Finset.range 4, x k * ι c ^ k :=
          Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hcoeff := congrArg (fun Q : L[X] => Q.coeff 1) hP0
  simp only [hP, coeff_sub, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at hcoeff
  have h1 : ∑ k ∈ Finset.range 4, (if 1 = m * k then y k else 0) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    have hne : 1 ≠ m * k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · omega
      · nlinarith
    simp [hne]
  rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero] at hcoeff
  simpa using hcoeff

theorem false_of_conj_xUnit_pow [Fintype K] (ι : K →+* L) (i : Fin τ.rank) {m : ℕ}
    (hm : 2 ≤ m) (hq : 3 * m < Fintype.card K) (T : ModGL τ L)
    (h : ∀ c : K, T * xUnit τ L i (ι c ^ m) * T⁻¹ = xUnit τ L i (ι c)) : False := by
  set w : RootModule τ L := rootVec τ L (-Pi.single i 1)
  set l : Label τ := Sum.inl i
  set Tm : Module.End L (RootModule τ L) := (T : Module.End L (RootModule τ L))
  set Ti : Module.End L (RootModule τ L) := ((T⁻¹ : ModGL τ L) : Module.End L (RootModule τ L))
  set y : ℕ → L := fun k => (Tm (xCoeff τ L i k (Ti w))) l
  set x : ℕ → L := fun k => (xCoeff τ L i k w) l
  have hx1 : x 1 = 1 := by
    simp only [x, w, l, xCoeff_rootVec_neg_single]
    simp [hVec]
  have key : ∀ c : K, ∑ k ∈ Finset.range 4, (ι c ^ m) ^ k * y k =
      ∑ k ∈ Finset.range 4, ι c ^ k * x k := by
    intro c
    have h1 := congrArg (fun g : ModGL τ L => ((g : Module.End L (RootModule τ L)) w) l) (h c)
    simp only [Units.val_mul, Module.End.mul_apply, coe_xUnit] at h1
    rw [xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff] at h1
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
      Finsupp.coe_finsetSum, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at h1
    exact h1
  have := coeff_one_eq_zero_of_forall ι hm hq x y key
  rw [hx1] at this
  exact one_ne_zero this

theorem eq_one_of_conj_xUnit [Finite K] (ι : K →+* L) (hK3 : ringChar K ≠ 3) (σ : K ≃+* K)
    (hσ : ∃ n : ℕ, σ ^ 3 ^ n = 1) (i : Fin τ.rank) (T : ModGL τ L)
    (h : ∀ c : K, T * xUnit τ L i (ι (σ c)) * T⁻¹ = xUnit τ L i (ι c)) : σ = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  by_contra hσ1
  set p := ringChar K with hpdef
  obtain ⟨f, hp, hcard⟩ := FiniteField.card K p
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  have hK : Nat.card K = p ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨k, hkf, hσk⟩ := exists_frobenius_pow' hp hf1 hK σ
  have hp2 : 2 ≤ p := hp.two_le
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hσ1
    ext a
    rw [hσk, pow_zero, pow_one]
    rfl
  have hσf : σ ^ (f : ℕ) = 1 := by
    have hpow : ∀ (n : ℕ) (a : K), (σ ^ n) a = a ^ (p ^ k) ^ n := by
      intro n
      induction n with
      | zero => intro a; simp
      | succ n ih =>
        intro a
        rw [pow_succ', RingAut.mul_apply, ih, hσk, ← pow_mul, ← pow_succ]
    ext a
    rw [hpow, ← pow_mul, mul_comm, pow_mul, ← hcard, FiniteField.pow_card_pow]
    rfl
  obtain ⟨n, hn⟩ := hσ
  have h3f : 3 ∣ (f : ℕ) := by
    have h1 : orderOf σ ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hn
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hσ1 hj
    have h2 : orderOf σ ∣ (f : ℕ) := orderOf_dvd_of_pow_eq_one hσf
    rw [hj] at h2
    exact (dvd_pow_self 3 hj0).trans h2
  have hf3 : 3 ≤ (f : ℕ) := Nat.le_of_dvd (by omega) h3f
  set m₁ := p ^ k with hm₁
  set m₂ := p ^ ((f : ℕ) - k) with hm₂
  have hm₁2 : 2 ≤ m₁ := hp2.trans (Nat.le_self_pow hk0 p)
  have hm₂2 : 2 ≤ m₂ := hp2.trans (Nat.le_self_pow (by omega) p)
  have hq : m₁ * m₂ = Fintype.card K := by
    rw [hm₁, hm₂, ← pow_add, Nat.add_sub_cancel' hkf.le, hcard]
  have hq8 : 8 ≤ Fintype.card K := by
    rw [hcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left hp2 3
      _ ≤ p ^ (f : ℕ) := Nat.pow_le_pow_right hp.pos hf3
  have hq9 : Fintype.card K ≠ 9 := by
    intro h9
    apply hK3
    have h3 : 3 ∣ p ^ (f : ℕ) := by rw [← hcard, h9]; norm_num
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  have hσinv : ∀ a : K, σ (a ^ m₂) = a := fun a => by
    rw [hσk, ← pow_mul, hm₂, ← pow_add, Nat.sub_add_cancel hkf.le, ← hcard, FiniteField.pow_card]
  by_cases h₁ : 3 * m₁ < Fintype.card K
  · refine false_of_conj_xUnit_pow ι i hm₁2 h₁ T fun c => ?_
    rw [← map_pow, ← hσk]
    exact h c
  · have h₂ : 3 * m₂ < Fintype.card K := by
      by_contra h₂
      push Not at h₁ h₂
      have h9 : Fintype.card K ≤ 9 := by nlinarith
      have h8 : Fintype.card K = 8 := by omega
      rw [h8] at h₁ h₂ hq
      have : 3 ≤ m₁ := by omega
      have : 3 ≤ m₂ := by omega
      nlinarith
    refine false_of_conj_xUnit_pow ι i hm₂2 h₂ T⁻¹ fun d => ?_
    have h1 := h (d ^ m₂)
    rw [hσinv, map_pow] at h1
    rw [inv_inv, ← h1]
    group

end CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof
