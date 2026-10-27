module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.Walter.Ree.Thompson1

open Finset

variable {K : Type*} [Field K] {m : ℕ}

@[expose] def fr (m : ℕ) (i : ZMod m) (x : K) : K := x ^ 3 ^ i.val

theorem fr_mul_arg (i : ZMod m) (x y : K) : fr m i (x * y) = fr m i x * fr m i y := mul_pow _ _ _

theorem fr_zero_arg (i : ZMod m) : fr m i (0 : K) = 0 := zero_pow (by positivity)

theorem fr_one_arg (i : ZMod m) : fr m i (1 : K) = 1 := one_pow _

theorem fr_zero_idx (x : K) : fr m 0 x = x := by simp [fr]

theorem fr_eq_zero_iff (i : ZMod m) (x : K) : fr m i x = 0 ↔ x = 0 :=
  pow_eq_zero_iff (by positivity)

theorem three_pow_val_injective (m : ℕ) [NeZero m] :
    Function.Injective fun i : ZMod m => 3 ^ i.val :=
  fun _ _ h => ZMod.val_injective m (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h)

section CharThree

variable [CharP K 3]

theorem fr_add_arg (i : ZMod m) (x y : K) : fr m i (x + y) = fr m i x + fr m i y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact add_pow_char_pow x y 3 i.val

theorem fr_neg_arg (i : ZMod m) (x : K) : fr m i (-x) = -fr m i x := by
  have h : fr m i (-x) + fr m i x = 0 := by rw [← fr_add_arg, neg_add_cancel, fr_zero_arg]
  linear_combination h

theorem fr_sub_arg (i : ZMod m) (x y : K) : fr m i (x - y) = fr m i x - fr m i y := by
  rw [sub_eq_add_neg, fr_add_arg, fr_neg_arg, ← sub_eq_add_neg]

theorem fr_sum_arg {ι : Type*} (s : Finset ι) (i : ZMod m) (g : ι → K) :
    fr m i (∑ k ∈ s, g k) = ∑ k ∈ s, fr m i (g k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fr_zero_arg]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, fr_add_arg, ih]

end CharThree

section Card

variable [Fintype K] (hK : Fintype.card K = 3 ^ m)
include hK

theorem pow_three_pow_mod (x : K) (k : ℕ) : x ^ 3 ^ k = x ^ 3 ^ (k % m) := by
  have hq : ∀ y : K, y ^ 3 ^ m = y := fun y => by rw [← hK]; exact FiniteField.pow_card y
  conv_lhs => rw [← Nat.mod_add_div k m]
  induction k / m with
  | zero => simp
  | succ t ih => rw [Nat.mul_succ, ← add_assoc, pow_add, pow_mul, ih, hq]

theorem fr_fr [NeZero m] (i j : ZMod m) (x : K) : fr m i (fr m j x) = fr m (i + j) x := by
  simp only [fr]
  rw [← pow_mul, ← pow_add, ZMod.val_add, ← pow_three_pow_mod hK, add_comm]

variable [CharP K 3] in
@[expose] def frE [NeZero m] (i : ZMod m) : K ≃+* K where
  toFun := fr m i
  invFun := fr m (-i)
  left_inv x := by rw [fr_fr hK, neg_add_cancel, fr_zero_idx]
  right_inv x := by rw [fr_fr hK, add_neg_cancel, fr_zero_idx]
  map_mul' := fr_mul_arg i
  map_add' := fr_add_arg i

variable [CharP K 3] in
theorem frE_apply [NeZero m] (i : ZMod m) (x : K) : frE hK i x = fr m i x := rfl

theorem lin_unique [NeZero m] {c : ZMod m → K} (h : ∀ x : K, ∑ i, c i * fr m i x = 0) :
    c = 0 := by
  classical
  let p : Polynomial K := ∑ i, Polynomial.C (c i) * Polynomial.X ^ (3 ^ i.val)
  have hp : p = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p Finset.univ
    · intro x _
      simpa [p, Polynomial.eval_finsetSum, fr] using h x
    · rw [Finset.card_univ, hK]
      have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
      calc p.natDegree ≤ 3 ^ (m - 1) := by
            apply Polynomial.natDegree_sum_le_of_forall_le
            intro i _
            refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
            exact Nat.pow_le_pow_right (by norm_num) (by have := ZMod.val_lt i; omega)
        _ < 3 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
  funext i
  have := congrArg (fun p => Polynomial.coeff p (3 ^ i.val)) hp
  have hinj : ∀ j : ZMod m, (3 ^ i.val = 3 ^ j.val ↔ j = i) := fun j =>
    ⟨fun h => (three_pow_val_injective m h).symm, fun h => by rw [h]⟩
  simpa [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, hinj] using this

theorem bilin_unique [NeZero m] {c : ZMod m → ZMod m → K}
    (h : ∀ x y : K, ∑ i, ∑ j, c i j * fr m i x * fr m j y = 0) : c = 0 := by
  have h1 : ∀ x : K, ∀ j, ∑ i, c i j * fr m i x = 0 := by
    intro x
    have := lin_unique hK (c := fun j => ∑ i, c i j * fr m i x) fun y => by
      rw [← h x y, Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
    exact fun j => congrFun this j
  funext i j
  exact congrFun (lin_unique hK (c := fun i => c i j) fun x => h1 x j) i

theorem trilin_unique [NeZero m] {c : ZMod m → ZMod m → ZMod m → K}
    (h : ∀ x y z : K, ∑ i, ∑ j, ∑ l, c i j l * fr m i x * fr m j y * fr m l z = 0) :
    c = 0 := by
  have h1 : ∀ x y : K, ∀ l, ∑ i, ∑ j, c i j l * fr m i x * fr m j y = 0 := by
    intro x y
    have := lin_unique hK (c := fun l => ∑ i, ∑ j, c i j l * fr m i x * fr m j y) fun z => by
      rw [← h x y z]
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
    exact fun l => congrFun this l
  funext i j l
  exact congrFun (congrFun (bilin_unique hK (c := fun i j => c i j l) fun x y => h1 x y l) i) j

variable [CharP K 3]

theorem lin_exists [NeZero m] {f : K → K} (hf : ∀ x y, f (x + y) = f x + f y) :
    ∃ c : ZMod m → K, ∀ x, f x = ∑ i, c i * fr m i x := by
  classical
  let Φ : (ZMod m → K) → (K →+ K) := fun c =>
    { toFun := fun x => ∑ i, c i * fr m i x
      map_zero' := by simp [fr_zero_arg]
      map_add' := fun x y => by simp [fr_add_arg, mul_add, Finset.sum_add_distrib] }
  have hinj : Function.Injective Φ := by
    intro c c' h
    have := lin_unique hK (c := c - c') fun x => by
      have hx := DFunLike.congr_fun h x
      simp only [Φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hx
      simp [sub_mul, Finset.sum_sub_distrib, hx]
    exact sub_eq_zero.1 this
  let _ : Algebra (ZMod 3) K := ZMod.algebra K 3
  have : Finite (K →+ K) := Finite.of_injective _ DFunLike.coe_injective
  have : Finite (K →ₗ[ZMod 3] K) := Finite.of_injective _ DFunLike.coe_injective
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Module.finrank (ZMod 3) K = m := by
    have h1 := FiniteField.pow_finrank_eq_natCard 3 K
    rw [Nat.card_eq_fintype_card, hK] at h1
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
  have hcard : Nat.card (K →+ K) ≤ Nat.card (ZMod m → K) := by
    rw [Nat.card_congr (AddMonoidHom.toZModLinearMapEquiv 3).toEquiv]
    rw [← FiniteField.pow_finrank_eq_natCard 3 (K →ₗ[ZMod 3] K), Module.finrank_linearMap,
      hfin, Nat.card_fun, Nat.card_eq_fintype_card (α := K), hK, Nat.card_zmod, ← pow_mul]
  obtain ⟨c, hc⟩ := (hinj.bijective_of_nat_card_le hcard).2 (AddMonoidHom.mk' f hf)
  exact ⟨c, fun x => (DFunLike.congr_fun hc x).symm⟩

theorem bilin_exists [NeZero m] {b : K → K → K} (hb1 : ∀ x x' y, b (x + x') y = b x y + b x' y)
    (hb2 : ∀ x y y', b x (y + y') = b x y + b x y') :
    ∃ c : ZMod m → ZMod m → K, ∀ x y, b x y = ∑ i, ∑ j, c i j * fr m i x * fr m j y := by
  choose d hd using fun x => lin_exists hK (f := b x) (hb2 x)
  have hdadd : ∀ j x x', d (x + x') j = d x j + d x' j := by
    intro j x x'
    have := lin_unique hK (c := fun j => d (x + x') j - d x j - d x' j) fun y => by
      have := hb1 x x' y
      rw [hd, hd, hd] at this
      simp only [sub_mul, Finset.sum_sub_distrib, this]
      ring
    have := congrFun this j
    simp only [Pi.zero_apply] at this
    linear_combination this
  choose e he using fun j => lin_exists hK (f := fun x => d x j) (hdadd j)
  refine ⟨fun i j => e j i, fun x y => ?_⟩
  rw [hd, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [he, Finset.sum_mul]

end Card

section Polarization

variable [Fintype K] [CharP K 3] (hK : Fintype.card K = 3 ^ m)
include hK

omit [Fintype K] [CharP K 3] hK in
theorem sum2_ite (f₁ f₂ : ZMod m → K) (a b : ZMod m) [Fintype (ZMod m)] :
    ∑ u, ∑ v, (if u = a ∧ v = b then (1 : K) else 0) * f₁ u * f₂ v = f₁ a * f₂ b := by
  classical
  rw [Finset.sum_eq_single a (fun u _ hu => by simp [hu]) (by simp)]
  rw [Finset.sum_eq_single b (fun v _ hv => by simp [hv]) (by simp)]
  simp

omit [Fintype K] [CharP K 3] hK in
theorem sum3_ite (f₁ f₂ f₃ : ZMod m → K) (a b c : ZMod m) [Fintype (ZMod m)] :
    ∑ u, ∑ v, ∑ w, (if u = a ∧ v = b ∧ w = c then (1 : K) else 0) * f₁ u * f₂ v * f₃ w =
      f₁ a * f₂ b * f₃ c := by
  classical
  rw [Finset.sum_eq_single a (fun u _ hu => by simp [hu]) (by simp)]
  rw [Finset.sum_eq_single b (fun v _ hv => by simp [hv]) (by simp)]
  rw [Finset.sum_eq_single c (fun w _ hw => by simp [hw]) (by simp)]
  simp

omit [Fintype K] hK in
theorem two_ne_zero' : (2 : K) ≠ 0 := by
  intro h
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have : (1 : K) = 0 := by linear_combination h3 - h
  exact one_ne_zero this

theorem pair_perm [NeZero m] {i j i' j' : ZMod m}
    (h : ∀ κ : K, fr m i κ * fr m j κ = fr m i' κ * fr m j' κ) :
    (i = i' ∧ j = j') ∨ (i = j' ∧ j = i') := by
  classical
  have hpol : ∀ α β : K, fr m i α * fr m j β + fr m j α * fr m i β =
      fr m i' α * fr m j' β + fr m j' α * fr m i' β := by
    intro α β
    have h1 := h (α + β)
    simp only [fr_add_arg] at h1
    linear_combination h1 - h α - h β
  let c : ZMod m → ZMod m → K := fun u v =>
    (if u = i ∧ v = j then 1 else 0) + (if u = j ∧ v = i then 1 else 0)
      - (if u = i' ∧ v = j' then 1 else 0) - (if u = j' ∧ v = i' then 1 else 0)
  have hc := bilin_unique hK (c := c) fun α β => by
    simp only [c, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      sum2_ite (fun u => fr m u α) (fun v => fr m v β)]
    linear_combination hpol α β
  have := congrFun (congrFun hc i) j
  by_contra hcon
  push Not at hcon
  have e3 : ¬ (i = i' ∧ j = j') := fun h => hcon.1 h.1 h.2
  have e4 : ¬ (i = j' ∧ j = i') := fun h => hcon.2 h.1 h.2
  simp only [c, Pi.zero_apply, e3, e4, and_self, ite_true, ite_false, sub_zero] at this
  by_cases hij : i = j
  · simp only [hij, and_self, ite_true] at this
    exact two_ne_zero' (by linear_combination this)
  · simp only [Ne.symm hij, hij, false_and, ite_false, add_zero] at this
    exact one_ne_zero this

omit [Fintype K] [CharP K 3] hK in
@[expose] def IsPerm3 (a b c a' b' c' : ZMod m) : Prop :=
  (a = a' ∧ b = b' ∧ c = c') ∨ (a = a' ∧ b = c' ∧ c = b') ∨ (a = b' ∧ b = a' ∧ c = c') ∨
    (a = b' ∧ b = c' ∧ c = a') ∨ (a = c' ∧ b = a' ∧ c = b') ∨ (a = c' ∧ b = b' ∧ c = a')

omit [Fintype K] hK in
theorem polarize3 (a b c : ZMod m) (α β γ : K) :
    fr m a (α + β + γ) * fr m b (α + β + γ) * fr m c (α + β + γ)
      - fr m a (α + β) * fr m b (α + β) * fr m c (α + β)
      - fr m a (α + γ) * fr m b (α + γ) * fr m c (α + γ)
      - fr m a (β + γ) * fr m b (β + γ) * fr m c (β + γ)
      + fr m a α * fr m b α * fr m c α + fr m a β * fr m b β * fr m c β
      + fr m a γ * fr m b γ * fr m c γ =
    fr m a α * fr m b β * fr m c γ + fr m a α * fr m c β * fr m b γ
      + fr m b α * fr m a β * fr m c γ + fr m b α * fr m c β * fr m a γ
      + fr m c α * fr m a β * fr m b γ + fr m c α * fr m b β * fr m a γ := by
  simp only [fr_add_arg]
  ring

theorem triple_perm [NeZero m] {a b c a' b' c' : ZMod m} (hne : ¬(a = b ∧ b = c))
    (h : ∀ κ : K, fr m a κ * fr m b κ * fr m c κ = fr m a' κ * fr m b' κ * fr m c' κ) :
    IsPerm3 a b c a' b' c' := by
  classical
  have hpol : ∀ α β γ : K,
      fr m a α * fr m b β * fr m c γ + fr m a α * fr m c β * fr m b γ
        + fr m b α * fr m a β * fr m c γ + fr m b α * fr m c β * fr m a γ
        + fr m c α * fr m a β * fr m b γ + fr m c α * fr m b β * fr m a γ =
      fr m a' α * fr m b' β * fr m c' γ + fr m a' α * fr m c' β * fr m b' γ
        + fr m b' α * fr m a' β * fr m c' γ + fr m b' α * fr m c' β * fr m a' γ
        + fr m c' α * fr m a' β * fr m b' γ + fr m c' α * fr m b' β * fr m a' γ :=
    fun α β γ => by
      rw [← polarize3 a b c α β γ, ← polarize3 a' b' c' α β γ, h, h, h, h, h, h, h]
  let I : ZMod m → ZMod m → ZMod m → ZMod m → ZMod m → ZMod m → K := fun u v w p q r =>
    if u = p ∧ v = q ∧ w = r then 1 else 0
  let cf : ZMod m → ZMod m → ZMod m → K := fun u v w =>
    (I u v w a b c + I u v w a c b + I u v w b a c + I u v w b c a + I u v w c a b
      + I u v w c b a) - (I u v w a' b' c' + I u v w a' c' b' + I u v w b' a' c'
      + I u v w b' c' a' + I u v w c' a' b' + I u v w c' b' a')
  have hcf := trilin_unique hK (c := cf) fun α β γ => by
    simp only [cf, I, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      sum3_ite (fun u => fr m u α) (fun v => fr m v β) (fun w => fr m w γ)]
    linear_combination hpol α β γ
  have := congrFun (congrFun (congrFun hcf a) b) c
  by_contra hcon
  have n1 : ¬ (a = a' ∧ b = b' ∧ c = c') := fun h => hcon (Or.inl h)
  have n2 : ¬ (a = a' ∧ b = c' ∧ c = b') := fun h => hcon (Or.inr (Or.inl h))
  have n3 : ¬ (a = b' ∧ b = a' ∧ c = c') := fun h => hcon (Or.inr (Or.inr (Or.inl h)))
  have n4 : ¬ (a = b' ∧ b = c' ∧ c = a') := fun h => hcon (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have n5 : ¬ (a = c' ∧ b = a' ∧ c = b') :=
    fun h => hcon (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  have n6 : ¬ (a = c' ∧ b = b' ∧ c = a') :=
    fun h => hcon (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  simp only [cf, I, Pi.zero_apply, n1, n2, n3, n4, n5, n6, ite_false, add_zero, sub_zero,
    and_self, ite_true] at this
  by_cases hab : a = b
  · have hbc : b ≠ c := fun h => hne ⟨hab, h⟩
    have hac : a ≠ c := fun h => hbc (hab ▸ h)
    simp [hab, hbc, Ne.symm hbc] at this
    exact two_ne_zero' (by linear_combination this)
  · by_cases hbc : b = c
    · have hac : a ≠ c := fun h => hab (h.trans hbc.symm)
      simp [hbc, hac, Ne.symm hac] at this
      exact two_ne_zero' (by linear_combination this)
    · by_cases hac : a = c
      · simp [hbc, hac, Ne.symm hbc] at this
        exact two_ne_zero' (by linear_combination this)
      · simp [hab, hbc, hac, Ne.symm hab, Ne.symm hbc, Ne.symm hac] at this

end Polarization

end CFSG.Walter.Ree.Thompson1
