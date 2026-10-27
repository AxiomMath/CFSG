module

public import CFSG.Assembly.Defs

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly Matrix

section ElemAbelian

variable {W : Type*} [AddCommGroup W] {G : Type*} [Group G]

theorem isElemAbelian_range_of_nsmul {p : ℕ} (hW : ∀ w : W, p • w = 0)
    (φ : Multiplicative W →* G) : IsElemAbelian p φ.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨v, rfl⟩ := hx
    rw [← map_pow]
    have : v ^ p = 1 := by
      change Multiplicative.ofAdd (p • Multiplicative.toAdd v) = 1
      rw [hW, ofAdd_zero]
    rw [this, map_one]

theorem card_range_of_injective {φ : Multiplicative W →* G} (hφ : Function.Injective φ) :
    Nat.card φ.range = Nat.card W :=
  (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm.trans
    (Nat.card_congr Multiplicative.toAdd)

end ElemAbelian

section Unipotent

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] {W : Type*}
  [AddCommGroup W]

@[expose] def unipotentHom (X : W →+ Matrix ι ι K) (hX : ∀ a b, X a * X b = 0) :
    Multiplicative W →* GL ι K where
  toFun a := ⟨1 + X a.toAdd, 1 - X a.toAdd, by simp [mul_sub, add_mul, hX],
    by simp [sub_mul, mul_add, hX]⟩
  map_one' := Units.ext (by simp)
  map_mul' a b := Units.ext (by
    change 1 + X (Multiplicative.toAdd (a * b)) =
      (1 + X (Multiplicative.toAdd a)) * (1 + X (Multiplicative.toAdd b))
    rw [toAdd_mul, map_add, add_mul, one_mul, mul_add, mul_one, hX, add_zero, add_assoc,
      add_comm (X (Multiplicative.toAdd b))])

theorem coe_unipotentHom (X : W →+ Matrix ι ι K) (hX : ∀ a b, X a * X b = 0)
    (a : Multiplicative W) :
    ((unipotentHom X hX a : GL ι K) : Matrix ι ι K) = 1 + X a.toAdd :=
  rfl

theorem unipotentHom_injective {X : W →+ Matrix ι ι K} (hX : ∀ a b, X a * X b = 0)
    (hXi : Function.Injective X) : Function.Injective (unipotentHom X hX) := by
  intro a b h
  have h' := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) h
  simp only [coe_unipotentHom, add_right_inj] at h'
  exact Multiplicative.toAdd.injective (hXi h')

theorem one_add_pow_of_mul_self_eq_zero {R : Type*} [Ring R] {N : R} (hN : N * N = 0) (n : ℕ) :
    (1 + N) ^ n = 1 + n • N := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hN, smul_zero, add_zero,
      succ_nsmul]
    abel

theorem det_one_add_of_mul_self_eq_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    {N : Matrix ι ι K} (hN : N * N = 0) : (1 + N).det = 1 := by
  have h1 : (1 + N) ^ p = 1 := by
    rw [one_add_pow_of_mul_self_eq_zero hN, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero K p,
      zero_smul, add_zero]
  have h2 : (1 + N).det ^ p = 1 ^ p := by rw [← det_pow, h1, det_one, one_pow]
  exact frobenius_inj K p h2

@[expose] def unipotentSL (X : W →+ Matrix ι ι K) (hX : ∀ a b, X a * X b = 0)
    (hdet : ∀ a, (1 + X a).det = 1) : Multiplicative W →* SpecialLinearGroup ι K where
  toFun a := ⟨1 + X a.toAdd, hdet _⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    change 1 + X (Multiplicative.toAdd (a * b)) =
      (1 + X (Multiplicative.toAdd a)) * (1 + X (Multiplicative.toAdd b))
    rw [toAdd_mul, map_add, add_mul, one_mul, mul_add, mul_one, hX, add_zero, add_assoc,
      add_comm (X (Multiplicative.toAdd b))])

theorem coe_unipotentSL (X : W →+ Matrix ι ι K) (hX : ∀ a b, X a * X b = 0)
    (hdet : ∀ a, (1 + X a).det = 1) (a : Multiplicative W) :
    ((unipotentSL X hX hdet a : SpecialLinearGroup ι K) : Matrix ι ι K) = 1 + X a.toAdd :=
  rfl

theorem unipotentSL_injective {X : W →+ Matrix ι ι K} (hX : ∀ a b, X a * X b = 0)
    (hdet : ∀ a, (1 + X a).det = 1) (hXi : Function.Injective X) :
    Function.Injective (unipotentSL X hX hdet) := by
  intro a b h
  have h' := congrArg (fun g : SpecialLinearGroup ι K => (g : Matrix ι ι K)) h
  simp only [coe_unipotentSL, add_right_inj] at h'
  exact Multiplicative.toAdd.injective (hXi h')

theorem eq_zero_of_one_add_eq_scalar {N : Matrix ι ι K} (hN : ∀ i, N i i = 0) {c : K} (i : ι)
    (h : 1 + N = scalar ι c) : N = 0 := by
  have hc : c = 1 := by
    have := congrFun (congrFun h i) i
    simp [hN i] at this
    exact this.symm
  rw [hc, map_one] at h
  simpa using h

theorem one_add_mul_diagonal_comm {N : Matrix ι ι K} {d : ι → K}
    (h : ∀ i j, N i j ≠ 0 → d i = d j) : (1 + N) * diagonal d = diagonal d * (1 + N) := by
  rw [add_mul, mul_add, one_mul, mul_one, add_right_inj]
  ext i j
  rw [mul_diagonal, diagonal_mul]
  by_cases hN : N i j = 0
  · simp [hN]
  · rw [h i j hN, mul_comm]

end Unipotent

end CFSG.RankThree.PartTwo.Census
