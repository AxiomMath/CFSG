module

public import CFSG.RankThree.PartOne.N143.JSL2
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.PartOne.HESS

open Polynomial
open CFSG.RankThree.PartOne.N143

theorem odd_of_two_pow_mod_three {f : ℕ} (h : 2 ^ f % 3 = 2) : Odd f := by
  rcases Nat.even_or_odd f with ⟨m, rfl⟩ | ho
  · exfalso
    have h4 : 2 ^ (m + m) = 4 ^ m := by rw [← two_mul, pow_mul]; norm_num
    rw [h4, Nat.pow_mod] at h
    norm_num at h
  · exact ho

theorem no_neg_pow_two_cube {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ f - 1)
    (hodd : 2 ^ f % 3 = 2) {n k : ℕ} (hn : n ^ 3 % p = 1) (hk : (n + 2 ^ k) % p = 0) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hf : Odd f := odd_of_two_pow_mod_three hodd
  have h2f : (2 : ZMod p) ^ f = 1 := by
    have h1 : ((2 ^ f - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
    have hle : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    rw [Nat.cast_sub hle] at h1
    push_cast at h1
    exact sub_eq_zero.1 h1
  have hn3 : (n : ZMod p) ^ 3 = 1 := by
    have h1 : ((n ^ 3 : ℕ) : ZMod p) = ((n ^ 3 % p : ℕ) : ZMod p) := (ZMod.natCast_mod _ _).symm
    rw [hn] at h1
    simpa using h1
  have hnk : (n : ZMod p) + 2 ^ k = 0 := by
    have h1 := (ZMod.natCast_eq_zero_iff (n + 2 ^ k) p).2 (Nat.dvd_of_mod_eq_zero hk)
    push_cast at h1
    exact h1
  have hneg : (n : ZMod p) = -2 ^ k := eq_neg_of_add_eq_zero_left hnk
  rw [hneg] at hn3
  have h3 : ((2 : ZMod p) ^ k) ^ 3 = -1 := by
    have : (-(2 : ZMod p) ^ k) ^ 3 = -((2 : ZMod p) ^ k) ^ 3 := by ring
    rw [this] at hn3
    exact eq_neg_of_add_eq_zero_left (by linear_combination (-1 : ZMod p) * hn3 : ((2 : ZMod p) ^ k) ^ 3 + 1 = 0)
  have h4 : (((2 : ZMod p) ^ k) ^ 3) ^ f = 1 := by
    have : (((2 : ZMod p) ^ k) ^ 3) ^ f = ((2 : ZMod p) ^ f) ^ (k * 3) := by ring
    rw [this, h2f, one_pow]
  rw [h3, hf.neg_one_pow] at h4
  have h5 : (2 : ZMod p) = 0 := by linear_combination -h4
  have h6 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h5)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h6)

section Frob

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_frob_pow_of_additive_twist (μ m : K) (β : K →+ K) (hβ1 : β 1 ≠ 0)
    (hβ : ∀ (j : ℕ) (c : K), β (μ ^ j * c) = m ^ j * β c) : ∃ k : ℕ, m = μ ^ 2 ^ k := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨n, -, hq⟩ := FiniteField.card K 2
  have hμ : μ ^ 2 ^ (n : ℕ) = μ := by
    rw [← hq]
    exact FiniteField.pow_card μ
  let f : ℕ → K[X] := fun i => X - C (μ ^ 2 ^ i)
  let Q : K[X] := ∏ i ∈ Finset.range n, f i
  have hfn : f n = f 0 := by
    simp only [f, hμ, pow_zero, pow_one]
  have hQmap : Q.map (frobenius K 2) = Q := by
    have h1 : Q.map (frobenius K 2) = ∏ i ∈ Finset.range n, f (i + 1) := by
      simp only [Q, Polynomial.map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [f, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, frobenius_def]
      rw [← pow_mul, ← pow_succ]
    rw [h1]
    have h2 := Finset.prod_range_succ f n
    have h3 := Finset.prod_range_succ' f n
    have hne : f 0 ≠ 0 := X_sub_C_ne_zero _
    have : (∏ i ∈ Finset.range n, f (i + 1)) * f 0 = (∏ i ∈ Finset.range n, f i) * f 0 := by
      rw [← h3, h2, hfn]
    exact mul_right_cancel₀ hne this
  have hcoef : ∀ j, Q.coeff j = 0 ∨ Q.coeff j = 1 := by
    intro j
    have h1 := congrArg (fun P : K[X] => P.coeff j) hQmap
    simp only [Polynomial.coeff_map, frobenius_def] at h1
    have h2 : Q.coeff j * (Q.coeff j - 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  have hQμ : Q.eval μ = 0 := by
    have hn0 : 0 < (n : ℕ) := n.pos
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_range.2 hn0) (by simp [f])
  have hsum : ∀ x : K, Q.eval x = ∑ j ∈ Finset.range (Q.natDegree + 1), Q.coeff j * x ^ j := fun x =>
    Polynomial.eval_eq_sum_range x
  have hkey : β (Q.eval μ) = Q.eval m * β 1 := by
    rw [hsum μ, hsum m, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases hcoef j with h | h
    · simp [h]
    · simp only [h, one_mul]
      have := hβ j 1
      rwa [mul_one] at this
  rw [hQμ, map_zero] at hkey
  have hQm : Q.eval m = 0 := by
    rcases mul_eq_zero.1 hkey.symm with h | h
    · exact h
    · exact absurd h hβ1
  rw [Polynomial.eval_prod] at hQm
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 hQm
  exact ⟨i, by simpa [f, sub_eq_zero] using hi⟩

end Frob


section SL2

variable {K : Type} [Field K]

@[expose] def xp (c : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def xm (c : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two_of]⟩

theorem e2_xp_00 (c : K) : e2 (xp c) 0 0 = 1 := by simp [e2, xp]
theorem e2_xp_01 (c : K) : e2 (xp c) 0 1 = c := by simp [e2, xp]
theorem e2_xp_10 (c : K) : e2 (xp c) 1 0 = 0 := by simp [e2, xp]
theorem e2_xp_11 (c : K) : e2 (xp c) 1 1 = 1 := by simp [e2, xp]
theorem e2_xm_00 (c : K) : e2 (xm c) 0 0 = 1 := by simp [e2, xm]
theorem e2_xm_01 (c : K) : e2 (xm c) 0 1 = 0 := by simp [e2, xm]
theorem e2_xm_10 (c : K) : e2 (xm c) 1 0 = c := by simp [e2, xm]
theorem e2_xm_11 (c : K) : e2 (xm c) 1 1 = 1 := by simp [e2, xm]

theorem xp_mul (a b : K) : xp a * xp b = xp (a + b) := by
  apply e2_ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    (simp [e2_mul, e2_xp_00, e2_xp_01, e2_xp_10, e2_xp_11]; try ring)

theorem xm_mul (a b : K) : xm a * xm b = xm (a + b) := by
  apply e2_ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [e2_mul, e2_xm_00, e2_xm_01, e2_xm_10, e2_xm_11]

theorem xp_mem (c : K) : xp c ∈ Uplus K := mem_Uplus.2 ⟨e2_xp_00 c, e2_xp_10 c, e2_xp_11 c⟩

theorem eq_xm_of_mem_Uminus {M : Matrix.SpecialLinearGroup (Fin 2) K} (hM : M ∈ Uminus K) :
    M = xm (e2 M 1 0) := by
  obtain ⟨h00, h01, h11⟩ := mem_Uminus.1 hM
  apply e2_ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [e2_xm_00, e2_xm_01, e2_xm_10, e2_xm_11, h00, h01, h11]

theorem xm_mem (c : K) : xm c ∈ Uminus K := mem_Uminus.2 ⟨e2_xm_00 c, e2_xm_01 c, e2_xm_11 c⟩

theorem eq_xp_of_mem_Uplus {M : Matrix.SpecialLinearGroup (Fin 2) K} (hM : M ∈ Uplus K) :
    M = xp (e2 M 0 1) := by
  obtain ⟨h00, h10, h11⟩ := mem_Uplus.1 hM
  apply e2_ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [e2_xp_00, e2_xp_01, e2_xp_10, e2_xp_11, h00, h10, h11]

theorem xp_injective : Function.Injective (xp : K → Matrix.SpecialLinearGroup (Fin 2) K) := fun a b h => by
  simpa [e2_xp_01] using congrArg (fun M => e2 M 0 1) h

theorem xm_injective : Function.Injective (xm : K → Matrix.SpecialLinearGroup (Fin 2) K) := fun a b h => by
  simpa [e2_xm_10] using congrArg (fun M => e2 M 1 0) h

theorem xp_zero : xp (0 : K) = 1 := by
  apply e2_ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [e2_xp_00, e2_xp_01, e2_xp_10, e2_xp_11, e2_one]

theorem xm_zero : xm (0 : K) = 1 := by
  apply e2_ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [e2_xm_00, e2_xm_01, e2_xm_10, e2_xm_11, e2_one]

theorem hmat_mul (a b : Kˣ) : (hmat a : Matrix.SpecialLinearGroup (Fin 2) K) * hmat b = hmat (a * b) := by
  apply e2_ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    (simp [e2_mul, e2_hmat_00, e2_hmat_01, e2_hmat_10, e2_hmat_11, Units.val_mul]; try ring)

theorem hmat_pow (a : Kˣ) (j : ℕ) :
    (hmat a : Matrix.SpecialLinearGroup (Fin 2) K) ^ j = hmat (a ^ j) := by
  induction j with
  | zero =>
    apply e2_ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [e2_hmat_00, e2_hmat_01, e2_hmat_10, e2_hmat_11, e2_one]
  | succ j ih => rw [pow_succ, ih, hmat_mul, ← pow_succ]

theorem conj_hmat_xp (ζ : Kˣ) (c : K) :
    hmat ζ * xp c * (hmat ζ)⁻¹ = xp ((ζ : K) ^ 2 * c) := by
  obtain ⟨c00, c01, c10, c11⟩ := e2_conj_hmat ζ (xp c)
  apply e2_ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [c00, c01, c10, c11, e2_xp_00, e2_xp_01, e2_xp_10, e2_xp_11]

theorem conj_hmat_xm (ζ : Kˣ) (c : K) :
    hmat ζ * xm c * (hmat ζ)⁻¹ = xm (((ζ : K)⁻¹) ^ 2 * c) := by
  obtain ⟨c00, c01, c10, c11⟩ := e2_conj_hmat ζ (xm c)
  apply e2_ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [c00, c01, c10, c11, e2_xm_00, e2_xm_01, e2_xm_10, e2_xm_11]

theorem card_Uplus : Nat.card (Uplus K) = Nat.card K := by
  have hb : Function.Bijective (fun c : K => (⟨xp c, xp_mem c⟩ : Uplus K)) :=
    ⟨fun a b h => xp_injective (congrArg Subtype.val h),
      fun M => ⟨e2 M.1 0 1, Subtype.ext (eq_xp_of_mem_Uplus M.2).symm⟩⟩
  exact (Nat.card_congr (Equiv.ofBijective _ hb)).symm

theorem card_Uminus : Nat.card (Uminus K) = Nat.card K := by
  have hb : Function.Bijective (fun c : K => (⟨xm c, xm_mem c⟩ : Uminus K)) :=
    ⟨fun a b h => xm_injective (congrArg Subtype.val h),
      fun M => ⟨e2 M.1 1 0, Subtype.ext (eq_xm_of_mem_Uminus M.2).symm⟩⟩
  exact (Nat.card_congr (Equiv.ofBijective _ hb)).symm

variable [Finite K] [CharP K 2]

theorem sl2_no_swap_core (ζ : Kˣ)
    (α : Matrix.SpecialLinearGroup (Fin 2) K →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hαinj : Function.Injective α) (n : ℕ)
    (hα : α (hmat ζ) = hmat ζ ^ n) (hU : ∀ M ∈ Uplus K, α M ∈ Uminus K) :
    ∃ k : ℕ, ((ζ : K) ^ 2)⁻¹ ^ n = ((ζ : K) ^ 2) ^ 2 ^ k := by
  have hαx : ∀ c : K, α (xp c) = xm (e2 (α (xp c)) 1 0) := fun c =>
    eq_xm_of_mem_Uminus (hU _ (xp_mem c))
  let β : K → K := fun c => e2 (α (xp c)) 1 0
  have hβ : ∀ c, α (xp c) = xm (β c) := hαx
  have hβadd : ∀ a b, β (a + b) = β a + β b := by
    intro a b
    have h1 : xm (β (a + b)) = xm (β a + β b) := by
      rw [← hβ, ← xp_mul, map_mul, hβ, hβ, xm_mul]
    exact xm_injective h1
  have hβ0 : β 0 = 0 := by
    have := hβadd 0 0
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  have hβ1 : β 1 ≠ 0 := by
    intro h
    have h1 : α (xp 1) = α 1 := by rw [hβ, h, xm_zero, map_one]
    have h2 : xp (1 : K) = 1 := hαinj h1
    have h3 : (1 : K) = 0 := xp_injective (h2.trans xp_zero.symm)
    exact one_ne_zero h3
  have hβmul : ∀ c, β ((ζ : K) ^ 2 * c) = (((ζ : K) ^ 2)⁻¹) ^ n * β c := by
    intro c
    have h1 := congrArg α (conj_hmat_xp ζ c)
    rw [map_mul, map_mul, map_inv, hα, hβ, hβ, hmat_pow, conj_hmat_xm] at h1
    have h2 := xm_injective h1
    rw [Units.val_pow_eq_pow_val] at h2
    rw [← h2]
    congr 1
    rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm]
  have hβpow : ∀ (j : ℕ) (c : K),
      β (((ζ : K) ^ 2) ^ j * c) = ((((ζ : K) ^ 2)⁻¹) ^ n) ^ j * β c := by
    intro j
    induction j with
    | zero => intro c; simp
    | succ j ih =>
      intro c
      have : ((ζ : K) ^ 2) ^ (j + 1) * c = (ζ : K) ^ 2 * (((ζ : K) ^ 2) ^ j * c) := by ring
      rw [this, hβmul, ih, pow_succ]
      ring
  exact exists_frob_pow_of_additive_twist ((ζ : K) ^ 2) ((((ζ : K) ^ 2)⁻¹) ^ n)
    (AddMonoidHom.mk' β hβadd) hβ1 hβpow

omit [Finite K] [CharP K 2] in
theorem zeta_pow_of_inv_pow_eq {ζ : Kˣ} {n k : ℕ}
    (h : ((ζ : K) ^ 2)⁻¹ ^ n = ((ζ : K) ^ 2) ^ 2 ^ k) : (ζ : K) ^ (2 * (n + 2 ^ k)) = 1 := by
  have hz : (ζ : K) ≠ 0 := ζ.ne_zero
  have h1 : ((ζ : K) ^ 2) ^ n * ((ζ : K) ^ 2) ^ 2 ^ k = 1 := by
    rw [← h, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hz))]
  rw [← pow_add] at h1
  rw [pow_mul]
  exact h1

end SL2

end CFSG.RankThree.PartOne.HESS
