
module

public import CFSG.Sporadic.Co2Schreier.Tuples
public import CFSG.Sporadic.Co2Schreier.SylowCheckInputs
public import Mathlib.Algebra.Order.Ring.Star

public noncomputable section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.RuSchreier

@[expose] def prodList (gs : List (Equiv.Perm (Fin 2300))) (l : List ℕ) :
    Equiv.Perm (Fin 2300) :=
  (l.map fun i => gs.getD i 1).prod

theorem prodList_cons (gs : List (Equiv.Perm (Fin 2300))) (i : ℕ) (l : List ℕ) :
    prodList gs (i :: l) = gs.getD i 1 * prodList gs l := by
  simp [prodList]

theorem rep_foldl_prod {A : Array (Array ℕ)} {gs : List (Equiv.Perm (Fin 2300))}
    (hA : RepTuple 2300 A gs) :
    ∀ (l : List ℕ), (∀ i ∈ l, i < gs.length) → ∀ (acc : Array ℕ) (g : Equiv.Perm (Fin 2300)),
      Rep 2300 acc g →
        Rep 2300 (l.foldl (fun acc i => compA 2300 acc A[i]!) acc) (g * prodList gs l)
  | [], _, acc, g, h => by simpa [prodList] using h
  | i :: l, hl, acc, g, h => by
    rw [List.foldl_cons, prodList_cons, ← mul_assoc]
    exact rep_foldl_prod hA l (fun j hj => hl j (List.mem_cons_of_mem _ hj)) _ _
      (rep_compA h (hA.rep (hl i List.mem_cons_self)))

theorem rep_prodArr {A : Array (Array ℕ)} {gs : List (Equiv.Perm (Fin 2300))}
    (hA : RepTuple 2300 A gs) {l : List ℕ} (hl : ∀ i ∈ l, i < gs.length) :
    Rep 2300 (prodArr A l) (prodList gs l) := by
  have h := rep_foldl_prod hA l hl _ _ (rep_idA (n := 2300))
  rwa [one_mul] at h

theorem prodList_mem {gs : List (Equiv.Perm (Fin 2300))} {H : Subgroup (Equiv.Perm (Fin 2300))}
    (hgs : ∀ g ∈ gs, g ∈ H) (l : List ℕ) : prodList gs l ∈ H := by
  refine H.list_prod_mem fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  rw [List.getD_eq_getElem?_getD]
  cases h : gs[i]? with
  | none => exact H.one_mem
  | some g => exact hgs g (List.mem_of_getElem? h)

theorem chainArrays_rawOfArrays {n : ℕ} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} {hn : 1 ≤ n} {hle : O.size ≤ S.size}
    {hlt : ∀ i < base.size, base[i]! < n} {hnd : base.toList.Nodup}
    (hO : ∀ k < O.size, isInvA n O[k]! (invCand n O[k]!) = true)
    (hS : ∀ j < S.size, isInvA n S[j]! (invCand n S[j]!) = true) :
    ChainArrays (rawOfArrays n O S base W hn hle hlt hnd) O S base W :=
  { orig_size := rfl
    strong_size := rfl
    base_size := rfl
    orig := fun k => by
      rw [rawOfArrays_original_get]
      exact (rep_permOfArr (hO k k.2)).1
    strong := fun j => by
      rw [rawOfArrays_strong_get]
      exact (rep_permOfArr (hS j j.2)).1
    base_val := fun i => rawOfArrays_base_get i
    deriv := fun _ _ => rfl }

theorem sum_range_eq_list_sum (f : ℕ → ℕ) :
    ∀ n, ∑ a ∈ Finset.range n, f a = ((List.range n).map f).sum
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append,
      sum_range_eq_list_sum f n]
    simp

theorem count_map_eq_sum {α : Type*} (g : α → ℕ) (c : ℕ) :
    ∀ l : List α, (l.map g).count c = (l.map fun x => if g x = c then 1 else 0).sum
  | [] => by simp
  | x :: l => by
    rw [List.map_cons, List.count_cons, count_map_eq_sum g c l, List.map_cons, List.sum_cons]
    by_cases h : g x = c <;> simp [h, add_comm]

theorem count2_eq_count_keys2 (L : Array Level) (key : Array ℕ → ℕ) (c : ℕ) :
    count2 2300 L (fun t => key t == c) = (keys2 L key).count c := by
  rw [keys2, List.count_flatMap, count2, sum_range_eq_list_sum]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  rw [Function.comp_apply, count_map_eq_sum, sum_range_eq_list_sum]
  simp only [beq_iff_eq]

theorem keys2_map (L : Array Level) (key : Array ℕ → ℕ) (f : ℕ → ℕ) :
    (keys2 L key).map f = keys2 L (fun t => f (key t)) := by
  simp [keys2, List.map_flatMap, List.map_map, Function.comp_def]

theorem sqChain_length (x : Array ℕ) : ∀ n, (sqChain x n).length = n
  | 0 => rfl
  | n + 1 => by rw [sqChain, List.length_cons, sqChain_length _ n]

theorem rep_sqChain : ∀ (n : ℕ) {t : Array ℕ} {g : Equiv.Perm (Fin 2300)}, Rep 2300 t g →
    ∀ i < n, Rep 2300 (sqChain t n)[i]! (g ^ (2 ^ i))
  | 0, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, t, g, ht, i, hi => by
    cases i with
    | zero =>
      rw [getElem!_pos _ 0 (by rw [sqChain_length]; omega)]
      simpa [sqChain] using ht
    | succ i =>
      rw [getElem!_pos _ (i + 1) (by rw [sqChain_length]; omega)]
      have h := rep_sqChain n (rep_compA ht ht) i (by omega)
      rw [getElem!_pos _ i (by rw [sqChain_length]; omega)] at h
      have e : (g * g) ^ 2 ^ i = g ^ 2 ^ (i + 1) := by
        rw [← pow_two, ← pow_mul, pow_succ', mul_comm]
      rw [e] at h
      simpa [sqChain] using h

theorem firstIdx_le (p : Array ℕ → Bool) : ∀ l : List (Array ℕ), firstIdx p l ≤ l.length
  | [] => le_rfl
  | x :: l => by
    rw [firstIdx]
    split_ifs
    · exact Nat.zero_le _
    · rw [List.length_cons]
      exact Nat.succ_le_succ (firstIdx_le p l)

theorem firstIdx_eq_iff (p : Array ℕ → Bool) :
    ∀ (l : List (Array ℕ)) (e : ℕ), e < l.length →
      (firstIdx p l = e ↔ p l[e]! = true ∧ ∀ i < e, p l[i]! = false)
  | [], e, he => absurd he (Nat.not_lt_zero e)
  | x :: l, e, he => by
    by_cases hx : p x = true
    · have h0 : firstIdx p (x :: l) = 0 := by simp [firstIdx, hx]
      rw [h0]
      cases e with
      | zero =>
        rw [getElem!_pos _ 0 he]
        simp [hx]
      | succ e =>
        constructor
        · intro h
          omega
        · rintro ⟨-, h2⟩
          have := h2 0 (by omega)
          rw [getElem!_pos _ 0 (by simp), List.getElem_cons_zero, hx] at this
          exact absurd this (by decide)
    · have hx' : p x = false := by simpa using hx
      have h0 : firstIdx p (x :: l) = firstIdx p l + 1 := by simp [firstIdx, hx']
      rw [h0]
      cases e with
      | zero =>
        rw [getElem!_pos _ 0 he]
        simp [hx']
      | succ e =>
        have he' : e < l.length := by simp at he; omega
        rw [Nat.add_right_cancel_iff, firstIdx_eq_iff p l e he', getElem!_pos _ (e + 1) he,
          List.getElem_cons_succ, ← getElem!_pos l e he']
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun i hi => ?_⟩
          cases i with
          | zero =>
            rw [getElem!_pos _ 0 (by simp), List.getElem_cons_zero]
            exact hx'
          | succ i =>
            rw [getElem!_pos _ (i + 1) (by simp; omega), List.getElem_cons_succ,
              ← getElem!_pos l i (by omega)]
            exact h2 i (by omega)
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun i hi => ?_⟩
          have := h2 (i + 1) (by omega)
          rwa [getElem!_pos _ (i + 1) (by simp; omega), List.getElem_cons_succ,
            ← getElem!_pos l i (by omega)] at this

theorem firstIdx_sqChain_eq_iff {p : Array ℕ → Bool} {P : Equiv.Perm (Fin 2300) → Prop}
    (hp : ∀ t g, Rep 2300 t g → (p t = true ↔ P g)) {t : Array ℕ} {g : Equiv.Perm (Fin 2300)}
    (ht : Rep 2300 t g) {n e : ℕ} (he : e < n) :
    firstIdx p (sqChain t n) = e ↔ P (g ^ 2 ^ e) ∧ ∀ i < e, ¬ P (g ^ 2 ^ i) := by
  rw [firstIdx_eq_iff p _ e (by rw [sqChain_length]; exact he),
    hp _ _ (rep_sqChain n ht e he)]
  refine and_congr_right fun _ => forall₂_congr fun i hi => ?_
  rw [← hp _ _ (rep_sqChain n ht i (by omega)), Bool.not_eq_true]

theorem orderOf_eq_two_pow_iff {M : Type*} [Monoid M] (y : M) (e : ℕ) :
    orderOf y = 2 ^ e ↔ y ^ 2 ^ e = 1 ∧ ∀ i < e, ¬ y ^ 2 ^ i = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro h
    refine ⟨by rw [← h]; exact pow_orderOf_eq_one y, fun i hi h1 => ?_⟩
    have hd := orderOf_dvd_of_pow_eq_one h1
    rw [h, Nat.pow_dvd_pow_iff_le_right (by norm_num)] at hd
    omega
  · rintro ⟨h1, h2⟩
    cases e with
    | zero =>
      rw [pow_zero, pow_one] at h1
      rw [h1, orderOf_one, pow_zero]
    | succ f => exact orderOf_eq_prime_pow (h2 f (by omega)) h1

theorem ordCode_eq_iff {t : Array ℕ} {g : Equiv.Perm (Fin 2300)} (ht : Rep 2300 t g) {e : ℕ}
    (he : e < 6) : ordCode t = e ↔ orderOf g = 2 ^ e := by
  rw [orderOf_eq_two_pow_iff, ordCode]
  exact firstIdx_sqChain_eq_iff (P := fun g => g = 1) (fun t g ht => eqA_iff ht rep_idA) ht he

theorem ordZCode_le (z x : Array ℕ) : ordZCode z x ≤ 6 := by
  have h := firstIdx_le (fun y => eqA 2300 y (idA 2300) || eqA 2300 y z) (sqChain x 6)
  rwa [sqChain_length] at h

theorem profKey_div (z x : Array ℕ) : profKey z x / 8 = ordCode x := by
  have := ordZCode_le z x
  rw [profKey]
  omega

theorem profKey_mod (z x : Array ℕ) : profKey z x % 8 = ordZCode z x := by
  have := ordZCode_le z x
  rw [profKey]
  omega

end CFSG.Sporadic.Co2Schreier
