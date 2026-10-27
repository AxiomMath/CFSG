module

public import CFSG.Quasithin.Vol2.Ch10SecQ6SL2a

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Polynomial

variable {F : Type} [Field F]

@[expose] def sig (n : ℕ) (x : F) : F := x ^ 2 ^ n

theorem sig_add [CharP F 2] (n : ℕ) (x y : F) : sig n (x + y) = sig n x + sig n y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold sig
  exact add_pow_char_pow x y 2 n

theorem sig_mul (n : ℕ) (x y : F) : sig n (x * y) = sig n x * sig n y := by
  unfold sig
  exact mul_pow x y _

theorem sig_one (n : ℕ) : sig n (1 : F) = 1 := one_pow _

theorem sig_zero (n : ℕ) : sig n (0 : F) = 0 := zero_pow (by positivity)

theorem sig_neg [CharP F 2] (n : ℕ) (x : F) : sig n (-x) = -sig n x := by
  rw [CharTwo.neg_eq, CharTwo.neg_eq]

theorem sig_sig [Finite F] {n : ℕ} (hF : Nat.card F = 4 ^ n) (x : F) : sig n (sig n x) = x := by
  have := Fintype.ofFinite F
  unfold sig
  rw [← pow_mul, ← pow_add, show n + n = 2 * n by ring, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num,
    ← hF, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem sig_injective [Finite F] {n : ℕ} (hF : Nat.card F = 4 ^ n) :
    Function.Injective (sig n : F → F) := fun x y h => by
  rw [← sig_sig hF x, h, sig_sig hF y]

theorem card_fix_le [Finite F] {n : ℕ} (hn : 1 ≤ n) :
    Nat.card {x : F // sig n x = x} ≤ 2 ^ n := by
  classical
  have := Fintype.ofFinite F
  let P : F[X] := X ^ 2 ^ n - X
  have h2n : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  have hdeg : P.natDegree = 2 ^ n := FiniteField.X_pow_card_sub_X_natDegree_eq F h2n
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F h2n
  let Z : Finset F := Finset.univ.filter fun x => sig n x = x
  have hZ : Z.val ⊆ P.roots := by
    intro x hx
    rw [Finset.mem_val, Finset.mem_filter] at hx
    rw [mem_roots hP0, IsRoot.def]
    have h1 : x ^ 2 ^ n = x := hx.2
    simp only [P, eval_sub, eval_pow, eval_X, h1, sub_self]
  have h1 := card_le_degree_of_subset_roots hZ
  rw [hdeg] at h1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h1

theorem exists_sig_ne [Finite F] {n : ℕ} (hF : Nat.card F = 4 ^ n) (hn : 1 ≤ n) :
    ∃ t : F, sig n t ≠ t := by
  by_contra h
  push Not at h
  have h1 := card_fix_le (F := F) hn
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv h), hF] at h1
  have h2 : 2 ^ n < 4 ^ n := Nat.pow_lt_pow_left (by norm_num) (by omega)
  omega

theorem eq_of_add_eq_zero_char_two [CharP F 2] {a b : F} (h : a + b = 0) : a = b := by
  rw [eq_neg_of_add_eq_zero_left h, CharTwo.neg_eq]

theorem eq_zero_of_trace [CharP F 2] [Finite F] {n : ℕ} (hF : Nat.card F = 4 ^ n) (hn : 1 ≤ n)
    {β : F} (h : ∀ t, t * sig n β + sig n t * β = 0) : β = 0 := by
  have h1 := h 1
  rw [one_mul, sig_one, one_mul] at h1
  have hβ : sig n β = β := eq_of_add_eq_zero_char_two h1
  obtain ⟨t, ht⟩ := exists_sig_ne hF hn
  have h2 := h t
  rw [hβ, ← add_mul] at h2
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (eq_of_add_eq_zero_char_two h3).symm ht
  · exact h3

variable (F) in
@[expose] def fixSig [CharP F 2] (n : ℕ) : AddSubgroup F where
  carrier := {x | sig n x = x}
  zero_mem' := sig_zero n
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq] at *
    rw [sig_add, ha, hb]
  neg_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq] at *
    rw [sig_neg, ha]

theorem card_fixSig [CharP F 2] [Finite F] {n : ℕ} (hF : Nat.card F = 4 ^ n) (hn : 1 ≤ n) :
    Nat.card (fixSig F n) = 2 ^ n := by
  refine le_antisymm (card_fix_le hn) ?_
  let T : F →+ F :=
    { toFun := fun t => t + sig n t
      map_zero' := by rw [sig_zero, add_zero]
      map_add' := fun a b => by
        change a + b + sig n (a + b) = a + sig n a + (b + sig n b)
        rw [sig_add]
        ring }
  have hker : T.ker = fixSig F n := by
    ext t
    rw [AddMonoidHom.mem_ker]
    exact ⟨fun h => (eq_of_add_eq_zero_char_two h).symm, fun h => by
      change t + sig n t = 0
      rw [show sig n t = t from h]
      exact CharTwo.add_self_eq_zero t⟩
  have hrange : T.range ≤ fixSig F n := by
    rintro _ ⟨t, rfl⟩
    change sig n (t + sig n t) = t + sig n t
    rw [sig_add, sig_sig hF, add_comm]
  have hcard : Nat.card F = Nat.card T.range * Nat.card T.ker := by
    rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange T).toEquiv]
    exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup T.ker
  have h1 : Nat.card T.range ≤ Nat.card (fixSig F n) := AddSubgroup.card_le_of_le hrange
  rw [hker] at hcard
  have h2 : (2 ^ n) ^ 2 ≤ Nat.card (fixSig F n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num, ← hF, hcard, sq]
    exact Nat.mul_le_mul_right _ h1
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h2

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
