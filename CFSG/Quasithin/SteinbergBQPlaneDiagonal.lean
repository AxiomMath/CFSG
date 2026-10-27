module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.SteinbergBQ

open Matrix

variable {F : Type*} [Field F] {p : ℕ}

theorem pow_eq_pow_mod_of_pow_eq_one {M : Type*} [Monoid M] {x : M} (hx : x ^ p = 1) (n : ℕ) :
    x ^ n = x ^ (n % p) := by
  conv_lhs => rw [← Nat.mod_add_div n p, pow_add, pow_mul, hx, one_pow, mul_one]

theorem pow_val_add [NeZero p] {M : Type*} [Monoid M] {x : M} (hx : x ^ p = 1) (a b : ZMod p) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod_of_pow_eq_one hx, pow_add]

theorem pow_val_mul {M : Type*} [Monoid M] {x : M} (hx : x ^ p = 1) (a b : ZMod p) :
    x ^ (a * b).val = (x ^ a.val) ^ b.val := by
  rw [ZMod.val_mul, ← pow_eq_pow_mod_of_pow_eq_one hx, pow_mul]

theorem pow_val_natCast {M : Type*} [Monoid M] {x : M} (hx : x ^ p = 1) (n : ℕ) :
    x ^ (n : ZMod p).val = x ^ n := by
  rw [ZMod.val_natCast, ← pow_eq_pow_mod_of_pow_eq_one hx]

theorem pow_val_injective [NeZero p] {ζ : F} (hζ : IsPrimitiveRoot ζ p) {a b : ZMod p}
    (h : ζ ^ a.val = ζ ^ b.val) : a = b :=
  ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)

variable (p) in
@[expose] def sumZeroPlane : Submodule (ZMod p) (Fin 3 → ZMod p) where
  carrier := {v | v 0 + v 1 + v 2 = 0}
  add_mem' {v w} hv hw := by
    have h1 : v 0 + v 1 + v 2 = 0 := hv
    have h2 : w 0 + w 1 + w 2 = 0 := hw
    change v 0 + w 0 + (v 1 + w 1) + (v 2 + w 2) = 0
    linear_combination h1 + h2
  zero_mem' := by
    change (0 : ZMod p) + 0 + 0 = 0
    simp
  smul_mem' c v hv := by
    have h1 : v 0 + v 1 + v 2 = 0 := hv
    change c * v 0 + c * v 1 + c * v 2 = 0
    linear_combination c * h1

theorem mem_sumZeroPlane {v : Fin 3 → ZMod p} : v ∈ sumZeroPlane p ↔ v 0 + v 1 + v 2 = 0 :=
  Iff.rfl

theorem card_sumZeroPlane : Nat.card (sumZeroPlane p) = p ^ 2 := by
  have e : sumZeroPlane p ≃ ZMod p × ZMod p :=
    { toFun := fun v => ((v : Fin 3 → ZMod p) 0, (v : Fin 3 → ZMod p) 1)
      invFun := fun ab => ⟨![ab.1, ab.2, -ab.1 - ab.2], by
        change ab.1 + ab.2 + (-ab.1 - ab.2) = 0
        ring⟩
      left_inv := fun v => by
        have hv : (v : Fin 3 → ZMod p) 0 + (v : Fin 3 → ZMod p) 1 + (v : Fin 3 → ZMod p) 2 = 0 :=
          v.2
        apply Subtype.ext
        funext i
        fin_cases i
        · rfl
        · rfl
        · change -(v : Fin 3 → ZMod p) 0 - (v : Fin 3 → ZMod p) 1 = (v : Fin 3 → ZMod p) 2
          linear_combination -hv
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_zmod, sq]

theorem sum_comp_perm_three {M : Type*} [AddCommMonoid M] (v : Fin 3 → M)
    (w : Equiv.Perm (Fin 3)) : v (w 0) + v (w 1) + v (w 2) = v 0 + v 1 + v 2 := by
  have h := Equiv.sum_comp w v
  simpa [Fin.sum_univ_three] using h

@[expose] def permPlane (w : Equiv.Perm (Fin 3)) : sumZeroPlane p →ₗ[ZMod p] sumZeroPlane p where
  toFun v := ⟨fun i => (v : Fin 3 → ZMod p) (w i), by
    change (v : Fin 3 → ZMod p) (w 0) + (v : Fin 3 → ZMod p) (w 1) +
      (v : Fin 3 → ZMod p) (w 2) = 0
    rw [sum_comp_perm_three]
    exact v.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coe_permPlane (w : Equiv.Perm (Fin 3)) (v : sumZeroPlane p) :
    ((permPlane w v : sumZeroPlane p) : Fin 3 → ZMod p) = fun i => (v : Fin 3 → ZMod p) (w i) :=
  rfl

@[expose] def diagPow (ζ : F) (v : Fin 3 → ZMod p) : Matrix (Fin 3) (Fin 3) F :=
  diagonal fun i => ζ ^ (v i).val

theorem diagPow_add [NeZero p] {ζ : F} (hζ : ζ ^ p = 1) (v w : Fin 3 → ZMod p) :
    diagPow ζ (v + w) = diagPow ζ v * diagPow ζ w := by
  rw [diagPow, diagPow, diagPow, diagonal_mul_diagonal]
  congr 1
  funext i
  exact pow_val_add hζ _ _

theorem diagPow_zero (ζ : F) : diagPow ζ (0 : Fin 3 → ZMod p) = 1 := by
  rw [diagPow]
  simp

theorem det_diagPow [NeZero p] {ζ : F} (hζ : ζ ^ p = 1) {v : Fin 3 → ZMod p}
    (hv : v ∈ sumZeroPlane p) : (diagPow ζ v).det = 1 := by
  rw [diagPow, det_diagonal, Fin.prod_univ_three, ← pow_add, ← pow_add]
  have h : (((v 0).val + (v 1).val + (v 2).val : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    exact hv
  obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff _ _).1 h
  rw [hk, pow_mul, hζ, one_pow]

@[expose] def planeHom [NeZero p] (ζ : F) (hζ : ζ ^ p = 1) :
    Multiplicative (sumZeroPlane p) →* SpecialLinearGroup (Fin 3) F where
  toFun v := ⟨diagPow ζ ((Multiplicative.toAdd v : sumZeroPlane p) : Fin 3 → ZMod p),
    det_diagPow hζ (Multiplicative.toAdd v).2⟩
  map_one' := Subtype.ext (diagPow_zero ζ)
  map_mul' _ _ := Subtype.ext (diagPow_add hζ _ _)

abbrev planeElem [NeZero p] (ζ : F) (hζ : ζ ^ p = 1) (v : sumZeroPlane p) :
    SpecialLinearGroup (Fin 3) F :=
  planeHom ζ hζ (Multiplicative.ofAdd v)

theorem coe_planeElem [NeZero p] (ζ : F) (hζ : ζ ^ p = 1) (v : sumZeroPlane p) :
    (planeElem ζ hζ v : Matrix (Fin 3) (Fin 3) F) = diagPow ζ (v : Fin 3 → ZMod p) :=
  rfl

theorem planeElem_neg [NeZero p] (ζ : F) (hζ : ζ ^ p = 1) (v : sumZeroPlane p) :
    planeElem ζ hζ (-v) = (planeElem ζ hζ v)⁻¹ :=
  (planeHom ζ hζ).map_inv (Multiplicative.ofAdd v)

theorem planeElem_smul [NeZero p] (ζ : F) (hζ : ζ ^ p = 1) (n : ℕ) (v : sumZeroPlane p) :
    planeElem ζ hζ ((n : ZMod p) • v) = planeElem ζ hζ v ^ n := by
  rw [← (planeHom ζ hζ).map_pow, ← ofAdd_nsmul, Nat.cast_smul_eq_nsmul]

variable (p) in
@[expose] def diagPlane [NeZero p] (ζ : F) (hζ : ζ ^ p = 1) :
    Subgroup (SpecialLinearGroup (Fin 3) F) :=
  (planeHom ζ hζ).range

theorem mem_diagPlane [NeZero p] {ζ : F} {hζ : ζ ^ p = 1} {A : SpecialLinearGroup (Fin 3) F} :
    A ∈ diagPlane p ζ hζ ↔ ∃ v : sumZeroPlane p, planeElem ζ hζ v = A :=
  ⟨fun ⟨v, hv⟩ => ⟨Multiplicative.toAdd v, hv⟩, fun ⟨v, hv⟩ => ⟨Multiplicative.ofAdd v, hv⟩⟩

theorem planeElem_mem [NeZero p] (ζ : F) (hζ : ζ ^ p = 1) (v : sumZeroPlane p) :
    planeElem ζ hζ v ∈ diagPlane p ζ hζ :=
  mem_diagPlane.2 ⟨v, rfl⟩

theorem planeElem_injective [NeZero p] {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    Function.Injective (planeElem ζ hζ.pow_eq_one) := by
  intro v w h
  have h1 := congrArg (fun A : SpecialLinearGroup (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) h
  apply Subtype.ext
  funext i
  have h2 := congrFun (congrFun h1 i) i
  simp only [coe_planeElem, diagPow, diagonal_apply_eq] at h2
  exact pow_val_injective hζ h2

theorem pow_eq_one_of_mem_diagPlane [NeZero p] {ζ : F} {hζ : ζ ^ p = 1}
    {A : SpecialLinearGroup (Fin 3) F} (hA : A ∈ diagPlane p ζ hζ) : A ^ p = 1 := by
  obtain ⟨v, rfl⟩ := mem_diagPlane.1 hA
  rw [← planeElem_smul, ZMod.natCast_self, zero_smul]
  exact (planeHom ζ hζ).map_one

theorem mem_diagPlane_of_diagonal [NeZero p] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (A : SpecialLinearGroup (Fin 3) F) (d : Fin 3 → F)
    (hA : (A : Matrix (Fin 3) (Fin 3) F) = diagonal d) (hd : ∀ i, d i ^ p = 1) :
    A ∈ diagPlane p ζ hζ.pow_eq_one := by
  choose u hu1 hu2 using fun i => hζ.eq_pow_of_pow_eq_one (hd i)
  have hdet : ζ ^ (u 0 + u 1 + u 2) = 1 := by
    have h := A.2
    rw [hA, det_diagonal, Fin.prod_univ_three, ← hu2 0, ← hu2 1, ← hu2 2, ← pow_add,
      ← pow_add] at h
    exact h
  have hv : (fun i => (u i : ZMod p)) ∈ sumZeroPlane p := by
    change (u 0 : ZMod p) + u 1 + u 2 = 0
    rw [← Nat.cast_add, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
    exact (hζ.pow_eq_one_iff_dvd _).1 hdet
  refine mem_diagPlane.2 ⟨⟨_, hv⟩, Subtype.ext ?_⟩
  rw [coe_planeElem, hA, diagPow]
  congr 1
  funext i
  rw [← hu2 i, ZMod.val_natCast, Nat.mod_eq_of_lt (hu1 i)]

variable (p) in
@[expose] def regVec : sumZeroPlane p :=
  ⟨![1, -1, 0], by
    change (1 : ZMod p) + -1 + 0 = 0
    ring⟩

theorem regVec_pow_injective [Fact p.Prime] (hp3 : 3 ≤ p) {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    Function.Injective fun i : Fin 3 => ζ ^ ((regVec p : Fin 3 → ZMod p) i).val := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 2 := by
      have := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h)
      exact this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h10 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have hm0 : (-1 : ZMod p) ≠ 0 := neg_ne_zero.2 h10
  have h1m : (1 : ZMod p) ≠ -1 := by
    intro h'
    apply h2
    rw [← one_add_one_eq_two]
    nth_rewrite 2 [h']
    exact add_neg_cancel 1
  intro i j hij
  have h := pow_val_injective hζ hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd (h : (1 : ZMod p) = -1) h1m
  · exact absurd (h : (1 : ZMod p) = 0) h10
  · exact absurd (h : (-1 : ZMod p) = 1) (Ne.symm h1m)
  · rfl
  · exact absurd (h : (-1 : ZMod p) = 0) hm0
  · exact absurd (h : (0 : ZMod p) = 1) (Ne.symm h10)
  · exact absurd (h : (0 : ZMod p) = -1) (Ne.symm hm0)
  · rfl

theorem exists_perm_of_conj_diagonal [Fact p.Prime] (hp3 : 3 ≤ p) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) {N N' : Matrix (Fin 3) (Fin 3) F} (hN'N : N' * N = 1)
    (hNN' : N * N' = 1) (d : Fin 3 → F)
    (hd : N' * diagPow ζ (regVec p : Fin 3 → ZMod p) * N = diagonal d) :
    ∃ (w : Equiv.Perm (Fin 3)) (t : Fin 3 → F), (∀ m, t m ≠ 0) ∧
      ∀ m, N *ᵥ Pi.single m 1 = t m • Pi.single (w m) 1 := by
  classical
  have hρinj := regVec_pow_injective hp3 hζ
  have hr : diagPow ζ (regVec p : Fin 3 → ZMod p) * N = N * diagonal d := by
    calc diagPow ζ (regVec p : Fin 3 → ZMod p) * N
        = N * N' * diagPow ζ (regVec p : Fin 3 → ZMod p) * N := by rw [hNN', Matrix.one_mul]
      _ = N * (N' * diagPow ζ (regVec p : Fin 3 → ZMod p) * N) := by
          simp only [Matrix.mul_assoc]
      _ = N * diagonal d := by rw [hd]
  have heig : ∀ m k, ζ ^ ((regVec p : Fin 3 → ZMod p) k).val * (N *ᵥ Pi.single m 1) k =
      d m * (N *ᵥ Pi.single m 1) k := by
    intro m k
    have hdm : diagonal d *ᵥ Pi.single m 1 = d m • Pi.single m 1 := by
      funext j
      rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
      by_cases hj : j = m
      · subst hj
        simp
      · simp [Pi.single_eq_of_ne hj]
    have h2 : diagPow ζ (regVec p : Fin 3 → ZMod p) *ᵥ (N *ᵥ Pi.single m 1) =
        d m • (N *ᵥ Pi.single m 1) := by
      rw [mulVec_mulVec, hr, ← mulVec_mulVec, hdm, mulVec_smul]
    have h3 := congrFun h2 k
    rw [diagPow, mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h3
    exact h3
  have hne : ∀ m, N *ᵥ Pi.single m 1 ≠ 0 := by
    intro m h
    have h1 := congrArg (fun v => N' *ᵥ v) h
    simp only [mulVec_mulVec, hN'N, one_mulVec, mulVec_zero] at h1
    have h2 := congrFun h1 m
    simp at h2
  have hsupp : ∀ m, ∃ k, ∀ k', k' ≠ k → (N *ᵥ Pi.single m 1) k' = 0 := by
    intro m
    obtain ⟨k, hk⟩ : ∃ k, (N *ᵥ Pi.single m 1) k ≠ 0 := by
      by_contra h
      push Not at h
      exact hne m (funext h)
    refine ⟨k, fun k' hk' => ?_⟩
    have h1 := mul_right_cancel₀ hk (heig m k)
    have h2 := heig m k'
    rw [← h1] at h2
    have h3 : ζ ^ ((regVec p : Fin 3 → ZMod p) k').val ≠
        ζ ^ ((regVec p : Fin 3 → ZMod p) k).val := fun h => hk' (hρinj h)
    exact (mul_eq_mul_right_iff.1 h2).resolve_left h3
  choose w₀ hw₀ using hsupp
  have hform : ∀ m, ∃ t : F, t ≠ 0 ∧ N *ᵥ Pi.single m 1 = t • Pi.single (w₀ m) 1 := by
    intro m
    have h1 : N *ᵥ Pi.single m 1 = (N *ᵥ Pi.single m 1) (w₀ m) • Pi.single (w₀ m) 1 := by
      funext k
      by_cases hk : k = w₀ m
      · subst hk
        simp
      · rw [hw₀ m k hk, Pi.smul_apply, Pi.single_eq_of_ne hk, smul_zero]
    refine ⟨_, fun h => hne m ?_, h1⟩
    rw [h1, h, zero_smul]
  choose t ht hN using hform
  have hinj : Function.Injective w₀ := by
    intro m m' h
    by_contra hmm
    have h1 : N *ᵥ (t m' • Pi.single m 1 - t m • Pi.single m' 1) = 0 := by
      rw [mulVec_sub, mulVec_smul, mulVec_smul, hN m, hN m', h, smul_smul, smul_smul, mul_comm,
        sub_self]
    have h2 := congrArg (fun v => N' *ᵥ v) h1
    simp only [mulVec_mulVec, hN'N, one_mulVec, mulVec_zero] at h2
    have h3 := congrFun h2 m
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hmm,
      smul_eq_mul, mul_one, mul_zero, sub_zero, Pi.zero_apply] at h3
    exact ht m' h3
  exact ⟨Equiv.ofBijective w₀ (Finite.injective_iff_bijective.1 hinj), t, ht, hN⟩

theorem conj_diagonal_of_monomial {N N' : Matrix (Fin 3) (Fin 3) F} (hN'N : N' * N = 1)
    (w : Equiv.Perm (Fin 3)) (t : Fin 3 → F) (ht : ∀ m, t m ≠ 0)
    (hN : ∀ m, N *ᵥ Pi.single m 1 = t m • Pi.single (w m) 1) (c : Fin 3 → F) :
    N * diagonal c * N' = diagonal fun k => c (w.symm k) := by
  classical
  have hN' : ∀ m, N' *ᵥ Pi.single (w m) 1 = (t m)⁻¹ • Pi.single m 1 := by
    intro m
    have h1 := congrArg (fun v => N' *ᵥ v) (hN m)
    simp only [mulVec_mulVec, hN'N, one_mulVec, mulVec_smul] at h1
    rw [h1, smul_smul, inv_mul_cancel₀ (ht m), one_smul]
  have hdiag : ∀ (e : Fin 3 → F) (m : Fin 3),
      diagonal e *ᵥ Pi.single m 1 = e m • Pi.single m 1 := by
    intro e m
    funext j
    rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases hj : j = m
    · subst hj
      simp
    · simp [Pi.single_eq_of_ne hj]
  refine ext_of_mulVec_single fun k => ?_
  obtain ⟨m, rfl⟩ := w.surjective k
  rw [← mulVec_mulVec, ← mulVec_mulVec, hN', mulVec_smul, hdiag, mulVec_smul, mulVec_smul, hN,
    hdiag, smul_smul, smul_smul, Equiv.symm_apply_apply, mul_comm (t m)⁻¹, mul_assoc,
    inv_mul_cancel₀ (ht m), mul_one]

theorem diagonal_of_monomial_of_pow_eq_one [Fact p.Prime] (hp5 : 5 ≤ p)
    {N : Matrix (Fin 3) (Fin 3) F} (w : Equiv.Perm (Fin 3)) (t : Fin 3 → F) (ht : ∀ m, t m ≠ 0)
    (hN : ∀ m, N *ᵥ Pi.single m 1 = t m • Pi.single (w m) 1) (hNp : N ^ p = 1) :
    N = diagonal t := by
  classical
  have hpow : ∀ (k : ℕ) (m : Fin 3), ∃ s : F, s ≠ 0 ∧
      N ^ k *ᵥ Pi.single m 1 = s • Pi.single ((w ^ k) m) 1 := by
    intro k
    induction k with
    | zero => exact fun m => ⟨1, one_ne_zero, by
        rw [pow_zero, pow_zero, one_mulVec, one_smul, Equiv.Perm.one_apply]⟩
    | succ k ih =>
      intro m
      obtain ⟨s, hs, hk⟩ := ih m
      refine ⟨s * t ((w ^ k) m), mul_ne_zero hs (ht _), ?_⟩
      rw [pow_succ', ← mulVec_mulVec, hk, mulVec_smul, hN, smul_smul, pow_succ',
        Equiv.Perm.mul_apply]
  have hwp : w ^ p = 1 := by
    refine Equiv.ext fun m => ?_
    obtain ⟨s, -, hs⟩ := hpow p m
    rw [hNp, one_mulVec] at hs
    by_contra hne
    have hne' : m ≠ (w ^ p) m := fun h => hne (by rw [Equiv.Perm.one_apply]; exact h.symm)
    have h1 := congrFun hs m
    rw [Pi.smul_apply, Pi.single_eq_of_ne hne', Pi.single_eq_same, smul_zero] at h1
    exact one_ne_zero h1
  have hw : w = 1 := by
    have h1 : orderOf w ∣ p := orderOf_dvd_of_pow_eq_one hwp
    have h2 : orderOf w ∣ 6 := by
      have := orderOf_dvd_card (x := w)
      rwa [Fintype.card_perm, Fintype.card_fin] at this
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ h1 with h | h
    · exact orderOf_eq_one_iff.1 h
    · rw [h] at h2
      have hp := (Fact.out : p.Prime)
      rcases (Nat.Prime.dvd_mul hp).1 (show p ∣ 2 * 3 by simpa using h2) with h3 | h3
      · have := Nat.le_of_dvd (by norm_num) h3
        omega
      · have := Nat.le_of_dvd (by norm_num) h3
        omega
  subst hw
  refine ext_of_mulVec_single fun m => ?_
  rw [hN]
  funext j
  rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases hj : j = m
  · subst hj
    simp
  · simp [Pi.single_eq_of_ne hj]

end CFSG.Quasithin.SteinbergBQ
