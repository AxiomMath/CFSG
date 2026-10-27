module

public import CFSG.Permutation.BurnsideSchur.SchurRing
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Lagrange

public section

namespace CFSG

open Polynomial
open scoped Finset

namespace BurnsideSchur

private theorem exists_sum_pow_ne_zero {K : Type*} [Field K] {U : Finset K}
    (hU : U.Nonempty) (h0 : (0 : K) ∉ U) : ∃ r, 1 ≤ r ∧ r ≤ #U ∧ ∑ u ∈ U, u ^ r ≠ 0 := by
  classical
  by_contra! h
  obtain ⟨u₀, hu₀⟩ := hU
  let Q : K[X] := X * Lagrange.basis U id u₀
  have hQ : Q.natDegree < #U + 1 := by
    have := Lagrange.natDegree_basis (Set.injOn_id _) hu₀
    have := natDegree_mul_le (p := (X : K[X])) (q := Lagrange.basis U id u₀)
    rw [natDegree_X] at this
    have := Finset.card_pos.2 ⟨u₀, hu₀⟩
    change (X * Lagrange.basis U id u₀).natDegree < _
    omega
  have h₁ : ∑ u ∈ U, Q.eval u = u₀ := by
    rw [Finset.sum_eq_single_of_mem u₀ hu₀ fun u hu hne => ?_]
    · have := Lagrange.eval_basis_self (v := id) (Set.injOn_id _) hu₀
      simp_all [Q]
    · simpa [Q] using Or.inr (Lagrange.eval_basis_of_ne (v := id) hne.symm hu)
  have h₂ : ∑ u ∈ U, Q.eval u = 0 := by
    simp_rw [eval_eq_sum_range' hQ]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [← Finset.mul_sum]
    rcases k with _ | k
    · simp [Q]
    · rw [h (k + 1) (by omega) (by simpa [Nat.lt_succ_iff] using hk), mul_zero]
  exact h0 (h₁.symm.trans h₂ ▸ hu₀)

section ShiftSub

variable {K : Type*} [Field K] (U : Finset K)

private noncomputable def shiftSub : K[X] →ₗ[K] K[X] :=
  ∑ u ∈ U, (taylor u - LinearMap.id)

private theorem shiftSub_apply (Q : K[X]) : shiftSub U Q = ∑ u ∈ U, (taylor u Q - Q) := by
  simp [shiftSub]

private theorem eval_shiftSub (Q : K[X]) (x : K) :
    (shiftSub U Q).eval x = ∑ u ∈ U, (Q.eval (x + u) - Q.eval x) := by
  simp [shiftSub_apply, eval_finsetSum, taylor_eval]

private theorem natDegree_shiftSub_le (Q : K[X]) : (shiftSub U Q).natDegree ≤ Q.natDegree := by
  rw [shiftSub_apply]
  exact natDegree_sum_le_of_forall_le _ _ fun u _ =>
    (natDegree_sub_le _ _).trans (by simp [natDegree_taylor])

private theorem coeff_shiftSub_X_pow (m i : ℕ) :
    (shiftSub U (X ^ m)).coeff i = if i < m then (∑ u ∈ U, u ^ (m - i)) * m.choose i else 0 := by
  simp only [shiftSub_apply, taylor_apply, X_pow_comp, finsetSum_coeff, coeff_sub,
    coeff_X_add_C_pow, coeff_X_pow]
  rcases lt_trichotomy i m with him | rfl | him
  · simp [him, him.ne, Finset.sum_mul]
  · simp
  · simp [him.not_gt, him.ne', Nat.choose_eq_zero_of_lt him]

variable {U}

private theorem natDegree_shiftSub_X_pow_le {r : ℕ} (hr : ∀ j, 1 ≤ j → j < r → ∑ u ∈ U, u ^ j = 0)
    (m : ℕ) : (shiftSub U (X ^ m)).natDegree ≤ m - r := by
  refine natDegree_le_iff_coeff_eq_zero.2 fun i hi => ?_
  rw [coeff_shiftSub_X_pow]
  split_ifs with him
  · rw [hr (m - i) (by omega) (by omega), zero_mul]
  · rfl

private theorem coeff_shiftSub_natDegree_sub {r : ℕ} (hr : ∀ j, 1 ≤ j → j < r → ∑ u ∈ U, u ^ j = 0)
    (hr₁ : 1 ≤ r) {Q : K[X]} (hrQ : r ≤ Q.natDegree) :
    (shiftSub U Q).coeff (Q.natDegree - r) =
      Q.leadingCoeff * (∑ u ∈ U, u ^ r) * Q.natDegree.choose r := by
  have hterm (m : ℕ) : (shiftSub U (C (Q.coeff m) * X ^ m)).coeff (Q.natDegree - r) =
      Q.coeff m * (shiftSub U (X ^ m)).coeff (Q.natDegree - r) := by
    rw [← smul_eq_C_mul, map_smul, coeff_smul, smul_eq_mul]
  rw [congrArg (shiftSub U) Q.as_sum_range_C_mul_X_pow, map_sum, finsetSum_coeff,
    Finset.sum_eq_single_of_mem Q.natDegree (by simp)]
  · rw [hterm, coeff_shiftSub_X_pow, ite_eq_left (by omega), Nat.sub_sub_self hrQ,
      Nat.choose_symm hrQ, leadingCoeff, mul_assoc]
  · intro m hm hmn
    have hm' : m < Q.natDegree := by
      have := Finset.mem_range.1 hm
      omega
    rw [hterm, coeff_shiftSub_X_pow]
    split_ifs with h
    · rw [hr _ (by omega) (by omega), zero_mul, mul_zero]
    · rw [mul_zero]

end ShiftSub

section Permutation

variable {p : ℕ} [Fact p.Prime]

private theorem degree_lt_of_natDegree_lt {Q : (ZMod p)[X]} {n : ℕ} (h : Q.natDegree < n) :
    Q.degree < n :=
  degree_le_natDegree.trans_lt (by exact_mod_cast h)

private theorem image_sub_eq {U : Finset (ZMod p)} {σ : Equiv.Perm (ZMod p)}
    (hσ : ∀ x, ∀ u ∈ U, σ (x + u) - σ x ∈ U) (x : ZMod p) :
    U.image (fun u => σ (x + u) - σ x) = U :=
  Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.2 (hσ x)) <|
    (Finset.card_image_of_injective _ fun _ _ h =>
      add_left_cancel (σ.injective (sub_left_inj.1 h))).ge

private theorem sum_comp_sub_eq {M : Type*} [AddCommMonoid M] {U : Finset (ZMod p)}
    {σ : Equiv.Perm (ZMod p)} (hσ : ∀ x, ∀ u ∈ U, σ (x + u) - σ x ∈ U) (x : ZMod p)
    (f : ZMod p → M) : ∑ u ∈ U, f (σ (x + u) - σ x) = ∑ u ∈ U, f u := by
  rw [← Finset.sum_image fun _ _ _ _ h => add_left_cancel (σ.injective (sub_left_inj.1 h)),
    image_sub_eq hσ x]

private theorem natDegree_interpolate_eq_one {U : Finset (ZMod p)} (hU : U.Nonempty)
    (h0 : (0 : ZMod p) ∉ U) (hcard : 2 * #U ≤ p - 1) {σ : Equiv.Perm (ZMod p)}
    (hσ : ∀ x, ∀ u ∈ U, σ (x + u) - σ x ∈ U) :
    (Lagrange.interpolate Finset.univ id σ).natDegree = 1 := by
  set P := Lagrange.interpolate Finset.univ id σ
  have hP (x : ZMod p) : P.eval x = σ x :=
    Lagrange.eval_interpolate_at_node (r := σ) (Set.injOn_id _) (Finset.mem_univ x)
  have hp := (Fact.out : p.Prime).two_le
  set d := P.natDegree
  have hd₁ : 1 ≤ d := by
    refine Nat.one_le_iff_ne_zero.2 fun hd => zero_ne_one (σ.injective ?_)
    rw [← hP, ← hP, eq_C_of_natDegree_eq_zero hd, eval_C, eval_C]
  have hd : d < p := by
    have := Lagrange.degree_interpolate_lt (s := Finset.univ) (v := id) σ (Set.injOn_id _)
    rw [Finset.card_univ, ZMod.card] at this
    exact (natDegree_lt_iff_degree_lt (ne_zero_of_natDegree_gt hd₁)).2 this
  set w := (p - 1) / d
  set n := d * w
  have hn : n ≤ p - 1 := by simpa [n, mul_comm] using Nat.div_mul_le_self (p - 1) d
  have hUn : #U < n := by
    have h₁ : p - 1 < n + d := by
      have := Nat.lt_div_mul_add (a := p - 1) (b := d) (by omega)
      simpa [n, w, mul_comm] using this
    have h₂ : d ≤ n := Nat.le_mul_of_pos_right d (Nat.div_pos (by omega) (by omega))
    omega
  have hex : ∃ r, 1 ≤ r ∧ r ≤ #U ∧ ∑ u ∈ U, u ^ r ≠ 0 := exists_sum_pow_ne_zero hU h0
  set r := Nat.find hex
  obtain ⟨hr₁, hrU, hr⟩ := Nat.find_spec hex
  have hr_min (j : ℕ) (hj₁ : 1 ≤ j) (hjr : j < r) : ∑ u ∈ U, u ^ j = 0 := by
    by_contra h
    exact Nat.find_min hex hjr ⟨hj₁, by omega, h⟩
  have hPw : (P ^ w).natDegree = n := by rw [natDegree_pow, mul_comm]
  have hcomp : ((shiftSub U (X ^ w)).comp P).natDegree ≤ (w - r) * d :=
    natDegree_comp_le.trans (Nat.mul_le_mul_right d (natDegree_shiftSub_X_pow_le hr_min w))
  have hid : shiftSub U (P ^ w) = (shiftSub U (X ^ w)).comp P := by
    refine eq_of_degrees_lt_of_eval_finset_eq (s := Finset.univ) ?_ ?_ fun x _ => ?_
    · rw [Finset.card_univ, ZMod.card]
      exact degree_lt_of_natDegree_lt ((natDegree_shiftSub_le U _).trans_lt (by omega))
    · rw [Finset.card_univ, ZMod.card]
      refine degree_lt_of_natDegree_lt (hcomp.trans_lt ?_)
      have : (w - r) * d ≤ n := by rw [mul_comm]; exact Nat.mul_le_mul_left d (Nat.sub_le w r)
      omega
    · simp only [eval_shiftSub, eval_comp, eval_pow, eval_X, hP]
      simpa using sum_comp_sub_eq hσ x fun u => (σ x + u) ^ w - σ x ^ w
  have hcoeff : (shiftSub U (P ^ w)).coeff (n - r) ≠ 0 := by
    rw [← hPw, coeff_shiftSub_natDegree_sub hr_min hr₁ (by omega), hPw]
    refine mul_ne_zero (mul_ne_zero (leadingCoeff_ne_zero.2
      (pow_ne_zero _ (ne_zero_of_natDegree_gt hd₁))) hr) fun h => ?_
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.choose_mul_factorial_mul_factorial (by omega : r ≤ n) ▸
      (h.mul_right r.factorial).mul_right (n - r).factorial
    exact absurd ((Fact.out : p.Prime).dvd_factorial.1 this) (by omega)
  have hle := (le_natDegree_of_ne_zero hcoeff).trans (hid ▸ hcomp)
  by_contra hd₂
  have hwr : r ≤ w := by
    by_contra h
    rw [Nat.sub_eq_zero_of_le (show w ≤ r by omega), zero_mul] at hle
    omega
  have := Nat.mul_le_mul_left r (by omega : 2 ≤ d)
  have : w * d = n := mul_comm w d
  rw [Nat.sub_mul] at hle
  omega

private theorem exists_affine_of_sub_mem {U : Set (ZMod p)} (hU : U.Nonempty) (hU0 : (0 : ZMod p) ∉ U)
    (hUne : U ≠ {0}ᶜ) {σ : Equiv.Perm (ZMod p)} (hσ : ∀ x y, x - y ∈ U → σ x - σ y ∈ U) :
    ∃ a ≠ 0, ∃ b, ∀ x, σ x = a * x + b := by
  classical
  suffices ∃ V : Finset (ZMod p), V.Nonempty ∧ 0 ∉ V ∧ 2 * #V ≤ p - 1 ∧
      ∀ x, ∀ u ∈ V, σ (x + u) - σ x ∈ V by
    obtain ⟨V, hV, hV0, hVcard, hσV⟩ := this
    obtain ⟨a, ha, b, hab⟩ := natDegree_eq_one.1 (natDegree_interpolate_eq_one hV hV0 hVcard hσV)
    refine ⟨a, ha, b, fun x => ?_⟩
    have := Lagrange.eval_interpolate_at_node (r := σ) (Set.injOn_id _) (Finset.mem_univ x)
    rw [← hab] at this
    simpa using this.symm
  let V := U.toFinset
  let W := Finset.univ.erase 0 \ V
  have hσV (x : ZMod p) (u : ZMod p) (hu : u ∈ V) : σ (x + u) - σ x ∈ V := by
    simpa [V] using hσ (x + u) x (by simpa [V] using hu)
  have hσW (x : ZMod p) (u : ZMod p) (hu : u ∈ W) : σ (x + u) - σ x ∈ W := by
    simp only [W, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true] at hu ⊢
    refine ⟨sub_ne_zero.2 fun h => hu.1 (by simpa using σ.injective h), fun hv => hu.2 ?_⟩
    rw [← image_sub_eq hσV x] at hv
    obtain ⟨u', hu', h⟩ := Finset.mem_image.1 hv
    rwa [add_left_cancel (σ.injective (sub_left_inj.1 h))] at hu'
  have hV0 : (0 : ZMod p) ∉ V := by simpa [V] using hU0
  have hW0 : (0 : ZMod p) ∉ W := by simp [W]
  have hW : W.Nonempty := by
    by_contra h
    refine hUne (Set.ext fun y => ⟨fun hy hy0 => hU0 (hy0 ▸ hy), fun hy => by_contra fun hyU => ?_⟩)
    exact h ⟨y, by simpa [W, V] using ⟨hy, hyU⟩⟩
  have hcard : #V + #W = p - 1 := by
    have hVsub : V ⊆ Finset.univ.erase 0 := fun u hu =>
      Finset.mem_erase.2 ⟨fun h => hV0 (h ▸ hu), Finset.mem_univ u⟩
    rw [Finset.card_sdiff_of_subset hVsub, Finset.card_erase_of_mem (Finset.mem_univ 0),
      Finset.card_univ, ZMod.card]
    have := Finset.card_le_card hVsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card] at this
    omega
  by_cases h : 2 * #V ≤ p - 1
  · exact ⟨V, by simpa [V] using hU, hV0, h, hσV⟩
  · exact ⟨W, hW, hW0, by omega, hσW⟩

end Permutation

theorem exists_affine_of_not_isMultiplyPretransitive {p : ℕ} [Fact p.Prime]
    {G : Subgroup (Equiv.Perm (ZMod p))} (hG : ∀ c, Equiv.addRight c ∈ G)
    (h2 : ¬ MulAction.IsMultiplyPretransitive G (ZMod p) 2) {σ : Equiv.Perm (ZMod p)}
    (hσ : σ ∈ G) : ∃ a ≠ 0, ∃ b, ∀ x, σ x = a * x + b := by
  rw [isMultiplyPretransitive_two_iff hG] at h2
  push Not at h2
  obtain ⟨x, hx, hne⟩ := h2
  exact exists_affine_of_sub_mem ⟨x, mem_suborbit_self x⟩ (zero_notMem_suborbit hx) hne
    fun y z h => ((isStable_suborbit x).sub_mem_iff hG hσ y z).2 h

end BurnsideSchur

end CFSG
