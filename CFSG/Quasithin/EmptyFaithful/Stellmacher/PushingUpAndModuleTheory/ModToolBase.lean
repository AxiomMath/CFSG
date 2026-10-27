module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.Quasithin.F53Mod

section Generic

variable {W : Type*} [CommGroup W]

@[expose] def delHom (φ : MulAut W) : W →* W where
  toFun w := φ w * w⁻¹
  map_one' := by simp
  map_mul' u v := by
    simp only [map_mul, mul_inv_rev]
    rw [mul_comm v⁻¹ u⁻¹, mul_mul_mul_comm]

theorem delHom_apply (φ : MulAut W) (w : W) : delHom φ w = φ w * w⁻¹ := rfl

theorem mem_ker_delHom {φ : MulAut W} {w : W} : w ∈ (delHom φ).ker ↔ φ w = w := by
  rw [MonoidHom.mem_ker, delHom_apply]
  exact mul_inv_eq_one

theorem inv_eq_self_of_sq (hsq : ∀ w : W, w * w = 1) (x : W) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (hsq x)

theorem delHom_delHom (hsq : ∀ w : W, w * w = 1) (ψ : MulAut W) (w : W) :
    delHom ψ (delHom ψ w) = delHom (ψ * ψ) w := by
  have hinv := inv_eq_self_of_sq hsq
  simp only [delHom_apply, map_mul, hinv, MulAut.mul_apply]
  have h1 := hsq (ψ w)
  calc ψ (ψ w) * ψ w * (ψ w * w) = ψ (ψ w) * (ψ w * ψ w) * w := by
        simp only [mul_assoc]
    _ = ψ (ψ w) * w := by rw [h1, mul_one]

theorem delHom_iterate_two_pow (hsq : ∀ w : W, w * w = 1) (φ : MulAut W) (s : ℕ) :
    (⇑(delHom φ))^[2 ^ s] = ⇑(delHom (φ ^ 2 ^ s)) := by
  induction s with
  | zero => funext w; simp
  | succ s ih =>
    funext w
    rw [pow_succ, mul_two, Function.iterate_add_apply, ih, delHom_delHom hsq, ← two_mul,
      pow_mul', sq]

theorem delHom_delHom_eq_one {hsq : ∀ w : W, w * w = 1} {φ : MulAut W} (h : φ * φ = 1)
    (w : W) : delHom φ (delHom φ w) = 1 := by
  rw [delHom_delHom hsq, h]
  simp [delHom_apply]

theorem pow_succ_apply (φ : MulAut W) (i : ℕ) (w : W) : (φ ^ (i + 1)) w = φ ((φ ^ i) w) := by
  rw [pow_succ', MulAut.mul_apply]

theorem pow_apply_succ (φ : MulAut W) (i : ℕ) (w : W) : (φ ^ (i + 1)) w = (φ ^ i) (φ w) := by
  rw [pow_succ, MulAut.mul_apply]

theorem pow_apply_of_fixed {φ : MulAut W} {w : W} (h : φ w = w) (i : ℕ) : (φ ^ i) w = w := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ_apply, ih, h]

@[expose] def normHom (φ : MulAut W) (m : ℕ) : W →* W :=
  ∏ i ∈ Finset.range m, ((φ ^ i : MulAut W) : W ≃* W).toMonoidHom

theorem normHom_apply (φ : MulAut W) (m : ℕ) (w : W) :
    normHom φ m w = ∏ i ∈ Finset.range m, (φ ^ i) w := by
  unfold normHom
  rw [MonoidHom.finsetProd_apply]
  rfl

theorem apply_normHom (φ : MulAut W) (m : ℕ) (w : W) :
    φ (normHom φ m w) = normHom φ m (φ w) := by
  rw [normHom_apply, normHom_apply, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_succ_apply, pow_apply_succ]

theorem normHom_apply_aut {φ : MulAut W} {m : ℕ} (hm : φ ^ m = 1) (w : W) :
    normHom φ m (φ w) = normHom φ m w := by
  rw [normHom_apply, normHom_apply]
  have h1 : ∏ i ∈ Finset.range m, (φ ^ i) (φ w) = ∏ i ∈ Finset.range m, (φ ^ (i + 1)) w :=
    Finset.prod_congr rfl fun i _ => (pow_apply_succ φ i w).symm
  rw [h1]
  have h2 := Finset.prod_range_succ (fun i => (φ ^ i) w) m
  have h3 := Finset.prod_range_succ' (fun i => (φ ^ i) w) m
  simp only [hm, MulAut.one_apply, pow_zero] at h2 h3
  exact mul_right_cancel (h3.symm.trans h2)

theorem apply_normHom_eq {φ : MulAut W} {m : ℕ} (hm : φ ^ m = 1) (w : W) :
    φ (normHom φ m w) = normHom φ m w := by
  rw [apply_normHom, normHom_apply_aut hm]

theorem pow_odd_eq_self (hsq : ∀ w : W, w * w = 1) {m : ℕ} (hm : Odd m) (w : W) : w ^ m = w := by
  obtain ⟨k, rfl⟩ := hm
  rw [pow_succ, pow_mul, sq, hsq, one_pow, one_mul]

theorem normHom_of_fixed (hsq : ∀ w : W, w * w = 1) {φ : MulAut W} {m : ℕ} (hm : Odd m) {w : W}
    (h : φ w = w) : normHom φ m w = w := by
  rw [normHom_apply]
  simp only [pow_apply_of_fixed h, Finset.prod_const, Finset.card_range]
  exact pow_odd_eq_self hsq hm w

theorem normHom_delHom {φ : MulAut W} {m : ℕ} (hm : φ ^ m = 1) (w : W) :
    normHom φ m (delHom φ w) = 1 := by
  rw [delHom_apply, map_mul, map_inv, normHom_apply_aut hm, mul_inv_cancel]

theorem range_delHom_invariant (φ : MulAut W) {x : W} (hx : x ∈ (delHom φ).range) :
    φ x ∈ (delHom φ).range := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨φ y, ?_⟩
  simp only [delHom_apply, map_mul, map_inv]

theorem pow_apply_mul_inv_mem (φ : MulAut W) (K : Subgroup W) (hK : ∀ x ∈ K, φ x ∈ K) {v : W}
    (hv : φ v * v⁻¹ ∈ K) (i : ℕ) : (φ ^ i) v * v⁻¹ ∈ K := by
  induction i with
  | zero => simp
  | succ i ih =>
    have : (φ ^ (i + 1)) v * v⁻¹ = φ ((φ ^ i) v * v⁻¹) * (φ v * v⁻¹) := by
      rw [pow_succ_apply, map_mul, map_inv]
      simp only [mul_assoc, inv_mul_cancel_left]
    rw [this]
    exact K.mul_mem (hK _ ih) hv

theorem normHom_mul_inv_mem (hsq : ∀ w : W, w * w = 1) {φ : MulAut W} {m : ℕ} (hm : Odd m)
    (K : Subgroup W) (hK : ∀ x ∈ K, φ x ∈ K) {v : W} (hv : φ v * v⁻¹ ∈ K) :
    normHom φ m v * v⁻¹ ∈ K := by
  have h1 : normHom φ m v * v⁻¹ = ∏ i ∈ Finset.range m, ((φ ^ i) v * v⁻¹) := by
    rw [normHom_apply, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      pow_odd_eq_self hsq hm]
  rw [h1]
  exact Subgroup.prod_mem _ fun i _ => pow_apply_mul_inv_mem φ K hK hv i

theorem exists_fixed_mul_mem_of_odd (hsq : ∀ w : W, w * w = 1) {φ : MulAut W} {m : ℕ}
    (hm : Odd m) (hφm : φ ^ m = 1) (K : Subgroup W) (hK : ∀ x ∈ K, φ x ∈ K) {v : W}
    (hv : φ v * v⁻¹ ∈ K) : ∃ c : W, φ c = c ∧ v * c⁻¹ ∈ K := by
  refine ⟨normHom φ m v, apply_normHom_eq hφm v, ?_⟩
  have := K.inv_mem (normHom_mul_inv_mem hsq hm K hK hv)
  simpa [mul_comm] using this

theorem isCompl_ker_range_delHom_of_odd (hsq : ∀ w : W, w * w = 1) {φ : MulAut W} {m : ℕ}
    (hm : Odd m) (hφm : φ ^ m = 1) : IsCompl (delHom φ).ker (delHom φ).range := by
  rw [isCompl_iff]
  constructor
  · rw [Subgroup.disjoint_def]
    intro x hx hx'
    have h1 := normHom_of_fixed hsq hm (mem_ker_delHom.mp hx)
    obtain ⟨y, rfl⟩ := hx'
    rw [← h1, normHom_delHom hφm]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    rw [Subgroup.mem_sup]
    obtain ⟨c, hc, hr⟩ := exists_fixed_mul_mem_of_odd hsq hm hφm (delHom φ).range
      (fun x hx => range_delHom_invariant φ hx) (v := v) ⟨v, rfl⟩
    refine ⟨c, mem_ker_delHom.mpr hc, v * c⁻¹, hr, by rw [mul_comm v, mul_inv_cancel_left]⟩

theorem exists_mem_ker_range_of_odd (hsq : ∀ w : W, w * w = 1) {φ : MulAut W} {m : ℕ}
    (hm : Odd m) (hφm : φ ^ m = 1) (U : Subgroup W) (hU : ∀ x ∈ U, φ x ∈ U) {u : W}
    (hu : u ∈ U) : ∃ c ∈ U ⊓ (delHom φ).ker, ∃ r ∈ U ⊓ (delHom φ).range, c * r = u := by
  have hUφ : ∀ i : ℕ, ∀ x ∈ U, (φ ^ i) x ∈ U := by
    intro i
    induction i with
    | zero => intro x hx; simpa using hx
    | succ i ih => intro x hx; rw [pow_succ_apply]; exact hU _ (ih x hx)
  have hN : normHom φ m u ∈ U := by
    rw [normHom_apply]
    exact Subgroup.prod_mem _ fun i _ => hUφ i u hu
  have huδ : φ u * u⁻¹ ∈ U := U.mul_mem (hU u hu) (U.inv_mem hu)
  have hr : normHom φ m u * u⁻¹ ∈ (delHom φ).range := by
    have := normHom_mul_inv_mem hsq hm (delHom φ).range
      (fun x hx => range_delHom_invariant φ hx) (v := u) ⟨u, rfl⟩
    exact this
  refine ⟨normHom φ m u, ⟨hN, mem_ker_delHom.mpr (apply_normHom_eq hφm u)⟩,
    u * (normHom φ m u)⁻¹, ⟨U.mul_mem hu (U.inv_mem hN), ?_⟩, by rw [mul_comm u, mul_inv_cancel_left]⟩
  have := (delHom φ).range.inv_mem hr
  simpa [mul_comm] using this

theorem map_delHom_range_of_odd (hsq : ∀ w : W, w * w = 1) {φ : MulAut W} {m : ℕ}
    (hm : Odd m) (hφm : φ ^ m = 1) :
    (delHom φ).range.map (delHom φ) = (delHom φ).range := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨y, rfl⟩, rfl⟩
    exact ⟨delHom φ y, rfl⟩
  · intro x hx
    set K : Subgroup W := (delHom φ).range.map (delHom φ) with hKdef
    have hK : ∀ x ∈ K, φ x ∈ K := by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨φ y, range_delHom_invariant φ hy, ?_⟩
      simp only [delHom_apply, map_mul, map_inv]
    have hxK : φ x * x⁻¹ ∈ K := ⟨x, hx, rfl⟩
    have h1 := normHom_mul_inv_mem hsq hm K hK hxK
    obtain ⟨y, rfl⟩ := hx
    rw [normHom_delHom hφm, one_mul] at h1
    simpa using K.inv_mem h1

theorem eq_of_iterate_delHom_eq_one_of_odd (hsq : ∀ w : W, w * w = 1) {φ : MulAut W}
    (hodd : Odd (orderOf φ)) {v : W} {k : ℕ} (hk : (⇑(delHom φ))^[k] v = 1) : φ v = v := by
  have h1 : (⇑(delHom φ))^[2 ^ k] v = 1 := by
    have : 2 ^ k = (2 ^ k - k) + k := by have := Nat.lt_two_pow_self (n := k); omega
    rw [this, Function.iterate_add_apply, hk]
    exact Function.iterate_fixed (by simp [delHom_apply]) _
  rw [delHom_iterate_two_pow hsq] at h1
  have h2 : (φ ^ 2 ^ k) v = v := mem_ker_delHom.mp h1
  have hcop : Nat.Coprime (2 ^ k) (orderOf φ) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hj]
  exact pow_apply_of_fixed h2 j

end Generic

end CFSG.Quasithin.F53Mod
