module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.ASVolI

@[expose] def burnsideF48t_gf4Mul (a b : ℕ) : ℕ :=
  if a = 0 ∨ b = 0 then 0 else
  if a = 1 then b else if b = 1 then a else
  if a = 2 then (if b = 2 then 3 else 1) else (if b = 2 then 1 else 2)

@[expose] def burnsideF48t_gf4Sq (a : ℕ) : ℕ :=
  if a = 2 then 3 else if a = 3 then 2 else a

section Field

variable {K : Type} [Field K]

theorem burnsideF48t_gf4_exists_ω (hK : Nat.card K = 4) :
    (2 : K) = 0 ∧ ∃ ω : K, ω ^ 2 = ω + 1 := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Fintype.card K = 2 ^ 2 := by rw [← Nat.card_eq_fintype_card, hK]; norm_num
  haveI : CharP K 2 := charP_of_card_eq_prime_pow hc
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨h2, ?_⟩
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
    classical
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [h x hx]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, hc] at this
    have h2' : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    omega
  have h4 : ω ^ 4 = ω := by
    have := FiniteField.pow_card ω
    rwa [hc] at this
  have h3 : ω ^ 3 = 1 := by
    have : ω * (ω ^ 3 - 1) = 0 := by ring_nf; rw [h4]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hω0
    · exact sub_eq_zero.1 h
  refine ⟨ω, ?_⟩
  have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by ring_nf; rw [h3]; ring
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) hω1
  · linear_combination h - (ω + 1) * h2

variable (ω : K)

@[expose] def burnsideF48t_gf4D (c : ℕ) : K :=
  if c = 1 then 1 else if c = 2 then ω else if c = 3 then ω + 1 else 0

variable {ω}

theorem burnsideF48t_gf4D_xor (h2 : (2 : K) = 0) {a b : ℕ} (ha : a < 4) (hb : b < 4) :
    burnsideF48t_gf4D ω (a ^^^ b) = burnsideF48t_gf4D ω a + burnsideF48t_gf4D ω b := by
  interval_cases a <;> interval_cases b <;>
    simp only [burnsideF48t_gf4D, Nat.reduceXor] <;> norm_num <;> grind

theorem burnsideF48t_gf4D_mul (h2 : (2 : K) = 0) (hω : ω ^ 2 = ω + 1) {a b : ℕ} (ha : a < 4)
    (hb : b < 4) :
    burnsideF48t_gf4D ω (burnsideF48t_gf4Mul a b) =
      burnsideF48t_gf4D ω a * burnsideF48t_gf4D ω b := by
  interval_cases a <;> interval_cases b <;>
    simp only [burnsideF48t_gf4D, burnsideF48t_gf4Mul] <;> norm_num <;> grind

theorem burnsideF48t_gf4D_sq (h2 : (2 : K) = 0) (hω : ω ^ 2 = ω + 1) {a : ℕ} (ha : a < 4) :
    burnsideF48t_gf4D ω (burnsideF48t_gf4Sq a) = burnsideF48t_gf4D ω a ^ 2 := by
  interval_cases a <;> simp only [burnsideF48t_gf4D, burnsideF48t_gf4Sq] <;> norm_num <;> grind

end Field

section Trans

open Matrix

variable {K : Type} [Field K]

@[expose] def burnsideF48t_trans (bar : K →+* K) (u : Fin 5 → K) : Matrix (Fin 5) (Fin 5) K :=
  1 + vecMulVec u (fun j => bar (u j))

theorem burnsideF48t_trans_map_transpose (bar : K →+* K) (hbar : ∀ c, bar (bar c) = c)
    (u : Fin 5 → K) : ((burnsideF48t_trans bar u).map bar)ᵀ = burnsideF48t_trans bar u := by
  ext i j
  simp only [burnsideF48t_trans, transpose_apply, map_apply, Matrix.add_apply, Matrix.one_apply,
    vecMulVec_apply, map_add, map_mul, hbar]
  by_cases h : i = j
  · subst h
    simp only [if_true]
    rw [map_one, mul_comm]
  · rw [if_neg (Ne.symm h), if_neg h, map_zero, mul_comm]

theorem burnsideF48t_trans_sq (bar : K →+* K) (h2 : (2 : K) = 0) {u : Fin 5 → K}
    (hu : (fun j => bar (u j)) ⬝ᵥ u = 0) :
    burnsideF48t_trans bar u * burnsideF48t_trans bar u = 1 := by
  unfold burnsideF48t_trans
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, vecMulVec_mul_vecMulVec, hu,
    zero_smul, vecMulVec_zero, add_zero, add_assoc]
  have : vecMulVec u (fun j => bar (u j)) + vecMulVec u (fun j => bar (u j)) = 0 := by
    ext i j
    rw [Matrix.add_apply, Matrix.zero_apply, ← two_mul, h2, zero_mul]
  rw [this, add_zero]

theorem burnsideF48t_trans_det (bar : K →+* K) {u : Fin 5 → K}
    (hu : (fun j => bar (u j)) ⬝ᵥ u = 0) : (burnsideF48t_trans bar u).det = 1 := by
  unfold burnsideF48t_trans
  rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, hu, add_zero]

open Classical in
@[expose] noncomputable def burnsideF48t_transU (bar : K →+* K) (u : Fin 5 → K) : GL (Fin 5) K :=
  if h : burnsideF48t_trans bar u * burnsideF48t_trans bar u = 1 then
    ⟨burnsideF48t_trans bar u, burnsideF48t_trans bar u, h, h⟩
  else 1

theorem burnsideF48t_coe_transU (bar : K →+* K) {u : Fin 5 → K}
    (h : burnsideF48t_trans bar u * burnsideF48t_trans bar u = 1) :
    ((burnsideF48t_transU bar u : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      burnsideF48t_trans bar u := by
  rw [burnsideF48t_transU, dif_pos h]

theorem burnsideF48t_trans_mulVec (bar : K →+* K) (u v : Fin 5 → K) :
    burnsideF48t_trans bar u *ᵥ v = v + ((fun j => bar (u j)) ⬝ᵥ v) • u := by
  unfold burnsideF48t_trans
  rw [add_mulVec, one_mulVec, vecMulVec_mulVec]
  ext i
  simp [mul_comm]

theorem burnsideF48t_transU_mem (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K)
    {u : Fin 5 → K} (hu : (fun j => h.bar (u j)) ⬝ᵥ u = 0) :
    burnsideF48t_transU h.bar u ∈ CFSG.Open.StatedSU 5 (2 ^ 1) K := by
  have h2 : (2 : K) = 0 := by
    haveI := h.charP
    exact CharTwo.two_eq_zero
  have hsq := burnsideF48t_trans_sq h.bar h2 hu
  rw [show CFSG.Open.StatedSU 5 (2 ^ 1) K = CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 5
    from rfl, CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h, burnsideF48t_coe_transU _ hsq]
  exact ⟨burnsideF48t_trans_det h.bar hu,
    by rw [burnsideF48t_trans_map_transpose h.bar h.bar_bar, hsq]⟩

end Trans

end CFSG.ASVolI
