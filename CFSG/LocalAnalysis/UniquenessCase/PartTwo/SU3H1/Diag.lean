module

public import CFSG.Quasithin.EmptyFaithful.E22SUGen
public import CFSG.ClassicalGroups.Unitary.SUnThreeLocalDefs
public import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SU3H1

open CFSG.Open CFSG.Quasithin.E22S
open scoped Matrix

variable {K : Type} [Field K]

@[expose] def reflDiag (c : Kˣ) (k : Fin 3) : GL (Fin 3) K :=
  CFSG.ClassicalGroups.SUnThreeLocal.diagGL K 3 (Function.update (fun _ => c) k (c ^ 2)⁻¹)

theorem coe_reflDiag (c : Kˣ) (k : Fin 3) :
    ((reflDiag c k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal fun i => ((Function.update (fun _ => c) k (c ^ 2)⁻¹ i : Kˣ) : K) :=
  rfl

private theorem update_pow_eq_one {c : Kˣ} {k : Fin 3} {m : ℕ} (hc : c ^ m = 1) :
    (Function.update (fun _ : Fin 3 => c) k (c ^ 2)⁻¹) ^ m = 1 := by
  funext i
  rw [Pi.pow_apply, Pi.one_apply]
  by_cases hi : i = k
  · subst hi
    rw [Function.update_self, inv_pow]
    rw [show (c ^ 2) ^ m = 1 by rw [← pow_mul, mul_comm, pow_mul, hc, one_pow], inv_one]
  · rw [Function.update_of_ne hi]
    exact hc

private theorem prod_update_eq_one (c : Kˣ) (k : Fin 3) :
    ∏ i, Function.update (fun _ : Fin 3 => c) k (c ^ 2)⁻¹ i = 1 := by
  rw [Fin.prod_univ_three]
  fin_cases k <;> simp [Function.update] <;> group

theorem reflDiag_mem [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) {c : Kˣ}
    (hc : c ^ (q + 1) = 1) (k : Fin 3) : reflDiag c k ∈ StatedSU 3 q K := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at h1
    norm_num at h1
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [coe_reflDiag, Matrix.det_diagonal, ← Units.coe_prod, prod_update_eq_one c k,
      Units.val_one]
  · rw [coe_reflDiag, Matrix.diagonal_map (f := fun x : K => x ^ q) (zero_pow hq0),
      Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have h : (Function.update (fun _ : Fin 3 => c) k (c ^ 2)⁻¹ i) ^ (q + 1) = 1 := by
      simpa using congrFun (update_pow_eq_one (k := k) (m := q + 1) hc) i
    rw [← pow_succ, ← Units.val_pow_eq_pow_val, h, Units.val_one]

theorem reflDiag_pow_eq_one {c : Kˣ} {m : ℕ} (hc : c ^ m = 1) (k : Fin 3) :
    reflDiag c k ^ m = 1 := by
  rw [reflDiag, ← map_pow, update_pow_eq_one hc, map_one]

theorem commute_reflDiag (c : Kˣ) (j k : Fin 3) : Commute (reflDiag c j) (reflDiag c k) := by
  exact (Commute.all _ _).map (CFSG.ClassicalGroups.SUnThreeLocal.diagGL K 3)

theorem eq_zero_of_reflDiag_mulVec_eq {c : Kˣ} (hc : c ≠ 1) (hc2 : c ^ 2 ≠ 1) (k : Fin 3)
    {v : Fin 3 → K} (hv : (reflDiag c k : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v) : v = 0 := by
  funext i
  have hi : ((Function.update (fun _ : Fin 3 => c) k (c ^ 2)⁻¹ i : Kˣ) : K) * v i = v i := by
    have h := congrFun hv i
    rwa [coe_reflDiag, Matrix.mulVec_diagonal] at h
  have hd : Function.update (fun _ : Fin 3 => c) k (c ^ 2)⁻¹ i ≠ 1 := by
    by_cases hik : i = k
    · subst hik
      rw [Function.update_self]
      intro h
      exact hc2 (inv_eq_one.mp h)
    · rw [Function.update_of_ne hik]
      exact hc
  have hzero : (((Function.update (fun _ : Fin 3 => c) k (c ^ 2)⁻¹ i : Kˣ) : K) - 1) *
      v i = 0 := by
    rw [sub_mul, one_mul, hi, sub_self]
  have hne : (((Function.update (fun _ : Fin 3 => c) k (c ^ 2)⁻¹ i : Kˣ) : K) - 1) ≠ 0 := by
    intro h
    exact hd (Units.ext (sub_eq_zero.mp h))
  exact (mul_eq_zero.mp hzero).resolve_left hne

theorem commute_reflDiag_of_mem_suStab [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) (c : Kˣ)
    {k : Fin 3} {x : StatedSU 3 q K} (hx : x ∈ suStab K q k) :
    Commute (x : GL (Fin 3) K) (reflDiag c k) := by
  obtain ⟨p, f, hp, hchar, rfl⟩ := su3_exists_prime_pow hK
  let σ := CFSG.LieType.BorelTits.unitaryInvolution K p f
  let A : Matrix (Fin 3) (Fin 3) K := ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hxSU : (x : GL (Fin 3) K) ∈
      CFSG.LieType.Universal.Unitary.SUid σ 3 := by
    rw [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 3]
    exact x.2
  have hunit : CFSG.LieType.Universal.Unitary.conjTr σ A * A = 1 := by
    exact (CFSG.LieType.Universal.Unitary.mem_SUid.mp hxSU).2
  have hx' : A *ᵥ (Pi.single k 1 : Fin 3 → K) = Pi.single k 1 := mem_suStab.mp hx
  have hcol : ∀ i, A i k = if i = k then 1 else 0 := by
    intro i
    have h := congrFun hx' i
    simpa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] using h
  have hrow : ∀ j, A k j = if k = j then 1 else 0 := by
    intro j
    have h1 : (CFSG.LieType.Universal.Unitary.conjTr σ A * A) k j =
        (1 : Matrix (Fin 3) (Fin 3) K) k j := by rw [hunit]
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    have hsum : ∑ i, CFSG.LieType.Universal.Unitary.conjTr σ A k i * A i j = A k j := by
      have h := Finset.sum_eq_single_of_mem (s := Finset.univ)
        (f := fun i => CFSG.LieType.Universal.Unitary.conjTr σ A k i * A i j) k
        (Finset.mem_univ k) (fun i _ hi => by
          rw [show CFSG.LieType.Universal.Unitary.conjTr σ A k i = σ (A i k) by rfl,
            hcol i, if_neg hi, map_zero, zero_mul])
      simpa [show CFSG.LieType.Universal.Unitary.conjTr σ A k k = σ (A k k) by rfl,
        hcol k] using h
    rw [hsum] at h1
    exact h1
  have hmul : A * (reflDiag c k : Matrix (Fin 3) (Fin 3) K) =
      (reflDiag c k : Matrix (Fin 3) (Fin 3) K) * A := by
    rw [coe_reflDiag]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hi : i = k
    · subst i
      by_cases hj : j = k
      · subst j
        ring
      · rw [hrow j, if_neg (Ne.symm hj)]
        simp
    · by_cases hj : j = k
      · subst j
        rw [hcol i, if_neg hi]
        simp
      · rw [Function.update_of_ne hi, Function.update_of_ne hj]
        ring
  exact Units.ext hmul

theorem exists_pow_two_pow_add_one_eq_one [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∃ c : Kˣ, c ^ (2 ^ n + 1) = 1 ∧ c ≠ 1 ∧ c ^ 2 ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hcard : Nat.card Kˣ = (2 ^ n - 1) * (2 ^ n + 1) := by
    rw [Nat.card_units, hK, CFSG.ClassicalGroups.Unitary.sq_sub_one_eq (2 ^ n)
      Nat.one_le_two_pow]
    rw [mul_comm]
  have h2n : 2 ≤ 2 ^ n := by
    simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
  have ha : 0 < 2 ^ n - 1 := by omega
  have hb : 1 < 2 ^ n + 1 := by omega
  refine ⟨g ^ (2 ^ n - 1), ?_, ?_, ?_⟩
  · rw [← pow_mul, ← hcard, ← hg, pow_orderOf_eq_one]
  · intro h
    have hlt : 2 ^ n - 1 < orderOf g := by
      rw [hg, hcard]
      exact (Nat.lt_mul_iff_one_lt_right ha).mpr hb
    exact pow_ne_one_of_lt_orderOf (by omega) hlt h
  · intro h
    have hlt : (2 ^ n - 1) * 2 < orderOf g := by
      rw [hg, hcard]
      exact (Nat.mul_lt_mul_left ha).mpr (by omega : 2 < 2 ^ n + 1)
    rw [← pow_mul] at h
    exact pow_ne_one_of_lt_orderOf (by omega) hlt h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SU3H1
