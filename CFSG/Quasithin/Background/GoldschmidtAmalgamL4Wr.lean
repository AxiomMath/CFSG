module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.F6.GoldAmL4

structure Tc where
  i : Fin 4
  j : Fin 4
  e : Fin 2
deriving DecidableEq, Fintype

namespace Tc

instance : Mul Tc := ⟨fun x y =>
  ⟨x.i + (if x.e = 0 then y.i else y.j), x.j + (if x.e = 0 then y.j else y.i), x.e + y.e⟩⟩

instance : One Tc := ⟨⟨0, 0, 0⟩⟩

instance : Inv Tc := ⟨fun x =>
  if x.e = 0 then ⟨-x.i, -x.j, 0⟩ else ⟨-x.j, -x.i, 1⟩⟩

theorem mul_def (x y : Tc) : x * y =
    ⟨x.i + (if x.e = 0 then y.i else y.j), x.j + (if x.e = 0 then y.j else y.i), x.e + y.e⟩ :=
  rfl

instance : Group Tc where
  mul_assoc := by decide +kernel
  one_mul := by decide +kernel
  mul_one := by decide +kernel
  inv_mul_cancel := by decide +kernel

end Tc

theorem card_Tc : Nat.card Tc = 32 := by
  rw [Nat.card_eq_fintype_card]
  rfl

@[expose] def tA : Tc := ⟨1, 0, 0⟩
@[expose] def tB : Tc := ⟨0, 1, 0⟩
@[expose] def tS : Tc := ⟨0, 0, 1⟩

@[expose] def tC : Tc := ⟨1, 1, 0⟩
@[expose] def tP : Tc := ⟨2, 0, 0⟩
@[expose] def tT0 : Tc := ⟨0, 1, 1⟩

theorem tA_pow_four : tA ^ 4 = 1 := by decide +kernel
theorem tB_pow_four : tB ^ 4 = 1 := by decide +kernel
theorem tS_sq : tS ^ 2 = 1 := by decide +kernel
theorem tA_mul_tB : tA * tB = tB * tA := by decide +kernel
theorem tS_tA_tS : tS * tA * tS = tB := by decide +kernel
theorem tS_tB_tS : tS * tB * tS = tA := by decide +kernel
theorem tA_ne_tB : tA ≠ tB := by decide +kernel
theorem tP_ne_tS : tP ≠ tS := by decide +kernel
theorem tC_eq : tC = tA * tB := by decide +kernel
theorem tP_eq : tP = tA * tA := by decide +kernel
theorem tT0_eq : tT0 = tS * tA := by decide +kernel

theorem tc_pow32 : ∀ w : Tc, w ^ 32 = 1 := by decide +kernel

theorem tc_nf : ∀ w : Tc, w = tA ^ w.i.val * tB ^ w.j.val * tS ^ w.e.val := by decide +kernel

def baseSub : Subgroup Tc where
  carrier := {w | w.e = 0}
  mul_mem' := fun {x y} hx hy => by
    have h : ∀ x y : Tc, x.e = 0 → y.e = 0 → (x * y).e = 0 := by decide +kernel
    exact h x y hx hy
  one_mem' := by decide +kernel
  inv_mem' := fun {x} hx => by
    have h : ∀ x : Tc, x.e = 0 → (x⁻¹).e = 0 := by decide +kernel
    exact h x hx

theorem mem_baseSub {w : Tc} : w ∈ baseSub ↔ w.e = 0 := Iff.rfl

instance (w : Tc) : Decidable (w ∈ baseSub) := by
  rw [mem_baseSub]; infer_instance

theorem base_or : ∀ w : Tc, w ∈ baseSub ∨ w * tS⁻¹ ∈ baseSub := by
  have h : ∀ w : Tc, w.e = 0 ∨ (w * tS⁻¹).e = 0 := by decide +kernel
  exact h

theorem base_normal : ∀ g w : Tc, w ∈ baseSub → g * w * g⁻¹ ∈ baseSub := by
  have h : ∀ g w : Tc, w.e = 0 → (g * w * g⁻¹).e = 0 := by decide +kernel
  exact h

def m2Sub : Subgroup Tc where
  carrier := {w | (w.i.val + w.j.val) % 2 = 0}
  mul_mem' := fun {x y} hx hy => by
    have h : ∀ x y : Tc, (x.i.val + x.j.val) % 2 = 0 → (y.i.val + y.j.val) % 2 = 0 →
        ((x * y).i.val + (x * y).j.val) % 2 = 0 := by decide +kernel
    exact h x y hx hy
  one_mem' := by decide +kernel
  inv_mem' := fun {x} hx => by
    have h : ∀ x : Tc, (x.i.val + x.j.val) % 2 = 0 →
        ((x⁻¹).i.val + (x⁻¹).j.val) % 2 = 0 := by decide +kernel
    exact h x hx

theorem mem_m2Sub {w : Tc} : w ∈ m2Sub ↔ (w.i.val + w.j.val) % 2 = 0 := Iff.rfl

instance (w : Tc) : Decidable (w ∈ m2Sub) := by
  rw [mem_m2Sub]; infer_instance

theorem m2_or : ∀ w : Tc, w ∈ m2Sub ∨ w * tT0⁻¹ ∈ m2Sub := by decide +kernel

theorem m2_normal : ∀ g w : Tc, w ∈ m2Sub → g * w * g⁻¹ ∈ m2Sub := by decide +kernel

theorem tC_mem : tC ∈ m2Sub := by decide +kernel
theorem tP_mem : tP ∈ m2Sub := by decide +kernel
theorem tS_mem : tS ∈ m2Sub := by decide +kernel
theorem tT0_not_mem : tT0 ∉ m2Sub := by decide +kernel

theorem m2_center : ∀ w : Tc, w ∈ m2Sub → (∀ v : Tc, v ∈ m2Sub → w * v = v * w) →
    ∃ k : Fin 4, w = tC ^ k.val := by decide +kernel

theorem order_eight_of_not : ∀ w : Tc, w ∉ baseSub → w ∉ m2Sub → w ^ 4 ≠ 1 := by decide +kernel

theorem m2_pow_four : ∀ w : Tc, w ∈ m2Sub → w ^ 4 = 1 := by decide +kernel

theorem m2_squares : ∀ w : Tc, w ∈ m2Sub →
    ∃ x₁ x₂ : Tc, w = x₁ ^ 2 * x₂ ^ 2 ∨ w = x₁ ^ 2 * x₂ ^ 2 * tS := by decide +kernel

theorem card_m2Sub : Nat.card m2Sub = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_baseSub : Nat.card baseSub = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem eq_m2Sub_of (N : Subgroup Tc) (hN : N.index = 2)
    (hab : ∃ x ∈ N, ∃ y ∈ N, x * y ≠ y * x) (hexp : ∀ w ∈ N, w ^ 4 = 1) : N = m2Sub := by
  have hcardN : Nat.card N = 16 := by
    have := N.card_mul_index
    rw [hN, card_Tc] at this
    omega
  have hsq : ∀ w : Tc, w ^ 2 ∈ N := fun w => Subgroup.sq_mem_of_index_two hN w
  have hmul : ∀ {x y : Tc}, x ∉ N → y ∉ N → x * y ∈ N := fun {x y} hx hy => by
    rw [Subgroup.mul_mem_iff_of_index_two hN]
    exact iff_of_false hx hy
  have hmul' : ∀ {x y : Tc}, x ∉ N → y ∈ N → x * y ∉ N := fun {x y} hx hy h => by
    rw [Subgroup.mul_mem_iff_of_index_two hN] at h
    exact hx (h.mpr hy)
  have hsN : tS ∈ N := by
    by_contra hs
    by_cases ha : tA ∈ N
    · have hb : tB ∈ N := by
        rw [← tS_tA_tS]
        exact hmul (hmul' hs ha) hs
      have hle : baseSub ≤ N := fun w hw => by
        have h1 := tc_nf w
        have h0 : w.e.val = 0 := by
          have : w.e = 0 := hw
          simp [this]
        rw [h1, h0, pow_zero, mul_one]
        exact N.mul_mem (N.pow_mem ha _) (N.pow_mem hb _)
      have heq : baseSub = N := Subgroup.eq_of_le_of_card_ge hle (by rw [hcardN, card_baseSub])
      obtain ⟨x, hx, y, hy, hxy⟩ := hab
      rw [← heq] at hx hy
      have hc : ∀ x y : Tc, x.e = 0 → y.e = 0 → x * y = y * x := by decide +kernel
      exact hxy (hc x y hx hy)
    · have hn : tS * tA ∈ N := hmul hs ha
      have h4 := hexp _ hn
      have : tS * tA = tT0 := tT0_eq.symm
      rw [this] at h4
      exact absurd h4 (by decide +kernel)
  have hle : m2Sub ≤ N := fun w hw => by
    obtain ⟨x₁, x₂, h | h⟩ := m2_squares w hw
    · rw [h]; exact N.mul_mem (hsq x₁) (hsq x₂)
    · rw [h]; exact N.mul_mem (N.mul_mem (hsq x₁) (hsq x₂)) hsN
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardN, card_m2Sub])).symm

@[expose] def evalFrom {M : Type*} [Mul M] (P Q : M) : M → List Bool → M
  | r, [] => r
  | r, b :: wd => evalFrom P Q (r * (if b then Q else P)) wd

@[expose] def evalw {M : Type*} [Mul M] [One M] (wd : List Bool) (P Q : M) : M :=
  evalFrom P Q 1 wd

theorem map_evalFrom {M N : Type*} [Mul M] [Mul N] (f : M → N)
    (hf : ∀ x y, f (x * y) = f x * f y) (P Q : M) (wd : List Bool) :
    ∀ r, f (evalFrom P Q r wd) = evalFrom (f P) (f Q) (f r) wd := by
  induction wd with
  | nil => intro r; rfl
  | cons b wd ih =>
    intro r
    show f (evalFrom P Q (r * (if b then Q else P)) wd) =
      evalFrom (f P) (f Q) (f r * (if b then f Q else f P)) wd
    rw [ih, hf]
    cases b <;> rfl

@[expose] def nfList : List (Tc × ℕ × List Bool) := [
  (⟨0, 0, 0⟩, 0, []),
  (⟨2, 0, 0⟩, 0, [false]),
  (⟨0, 0, 1⟩, 0, [true]),
  (⟨2, 0, 1⟩, 0, [false, true]),
  (⟨0, 2, 1⟩, 0, [true, false]),
  (⟨2, 2, 1⟩, 0, [false, true, false]),
  (⟨0, 2, 0⟩, 0, [true, false, true]),
  (⟨2, 2, 0⟩, 0, [false, true, false, true]),
  (⟨1, 1, 0⟩, 1, []),
  (⟨3, 1, 0⟩, 1, [false]),
  (⟨1, 1, 1⟩, 1, [true]),
  (⟨3, 1, 1⟩, 1, [false, true]),
  (⟨1, 3, 1⟩, 1, [true, false]),
  (⟨3, 3, 1⟩, 1, [false, true, false]),
  (⟨1, 3, 0⟩, 1, [true, false, true]),
  (⟨3, 3, 0⟩, 1, [false, true, false, true])]

@[expose] def nfOf (w : Tc) : ℕ × List Bool :=
  match nfList.find? (fun r => decide (r.1 = w)) with
  | some r => r.2
  | none => (0, [])

theorem nf_spec : ∀ w : Tc, w ∈ m2Sub → w = tC ^ (nfOf w).1 * evalw (nfOf w).2 tP tS := by
  decide +kernel

@[expose] def Fu (u : Tc × Tc × Tc) (w : Tc) : Tc :=
  u.1 ^ (nfOf w).1 * evalw (nfOf w).2 u.2.1 u.2.2

@[expose] def Rels (u : Tc × Tc × Tc) : Prop :=
  u.1 ^ 4 = 1 ∧ u.2.1 * u.2.1 = 1 ∧ u.2.2 * u.2.2 = 1 ∧ u.1 * u.2.1 = u.2.1 * u.1 ∧
    u.1 * u.2.2 = u.2.2 * u.1 ∧ (u.2.1 * u.2.2) ^ 4 = 1 ∧ u.1 * u.1 = (u.2.1 * u.2.2) ^ 2

instance (u : Tc × Tc × Tc) : Decidable (Rels u) := by unfold Rels; infer_instance

@[expose] def Cube (u : Tc × Tc × Tc) : Prop :=
  Fu u (Fu u (Fu u tC)) = tC ∧ Fu u (Fu u (Fu u tP)) = tP ∧ Fu u (Fu u (Fu u tS)) = tS

instance (u : Tc × Tc × Tc) : Decidable (Cube u) := by unfold Cube; infer_instance

@[expose] def alpha0 : Tc × Tc × Tc := (tC, tS, ⟨1, 3, 1⟩)

@[expose] def ConjTrip (t : Tc) (u : Tc × Tc × Tc) : Tc × Tc × Tc :=
  (t * Fu u (t⁻¹ * tC * t) * t⁻¹, t * Fu u (t⁻¹ * tP * t) * t⁻¹, t * Fu u (t⁻¹ * tS * t) * t⁻¹)

theorem classify_B_aux : ∀ u₁ u₂ u₃ : Tc, u₁ ∈ m2Sub → u₂ ∈ m2Sub → u₃ ∈ m2Sub →
    Rels (u₁, u₂, u₃) → (u₁, u₂, u₃) ≠ (tC, tP, tS) → Cube (u₁, u₂, u₃) →
    ∃ t : Tc, ConjTrip t (u₁, u₂, u₃) = alpha0 := by decide +kernel

theorem alpha0_rels : Rels alpha0 := by decide +kernel

theorem alpha0_cube : Cube alpha0 := by decide +kernel

theorem alpha0_inverted : ∀ w : Tc, w ∈ m2Sub →
    Fu alpha0 (tT0 * Fu alpha0 (tT0⁻¹ * w * tT0) * tT0⁻¹) = w := by decide +kernel

theorem tC_central : ∀ w : Tc, tC * w = w * tC := by decide +kernel

theorem tC_ne_tA_inv : tC ≠ tA⁻¹ := by decide +kernel

theorem Fu_id : ∀ w : Tc, w ∈ m2Sub → Fu (tC, tP, tS) w = w := by decide +kernel

theorem tC_pow_four : tC ^ 4 = 1 := by decide +kernel

theorem Fu_alpha0_mem : ∀ w : Tc, w ∈ m2Sub → Fu alpha0 w ∈ m2Sub := by decide +kernel

theorem alpha0_fix : Fu alpha0 tC = tC := by decide +kernel

structure HomOn (f : Tc → Tc) : Prop where
  one : f 1 = 1
  mem : ∀ x ∈ m2Sub, f x ∈ m2Sub
  mul : ∀ x ∈ m2Sub, ∀ y ∈ m2Sub, f (x * y) = f x * f y

namespace HomOn

variable {f : Tc → Tc}

theorem pow (hf : HomOn f) {x : Tc} (hx : x ∈ m2Sub) (n : ℕ) : f (x ^ n) = f x ^ n := by
  induction n with
  | zero => simp [hf.one]
  | succ n ih => rw [pow_succ, hf.mul _ (m2Sub.pow_mem hx n) _ hx, ih, pow_succ]

theorem evalFrom (hf : HomOn f) {P Q : Tc} (hP : P ∈ m2Sub) (hQ : Q ∈ m2Sub) :
    ∀ (wd : List Bool) (r : Tc), r ∈ m2Sub →
      f (CFSG.Quasithin.F6.GoldAmL4.evalFrom P Q r wd) =
          CFSG.Quasithin.F6.GoldAmL4.evalFrom (f P) (f Q) (f r) wd ∧
        CFSG.Quasithin.F6.GoldAmL4.evalFrom P Q r wd ∈ m2Sub := by
  intro wd
  induction wd with
  | nil => intro r hr; exact ⟨rfl, hr⟩
  | cons b wd ih =>
    intro r hr
    have hstep : (if b then Q else P) ∈ m2Sub := by
      cases b <;> simpa
    obtain ⟨h1, h2⟩ := ih (r * (if b then Q else P)) (m2Sub.mul_mem hr hstep)
    refine ⟨?_, h2⟩
    show f (CFSG.Quasithin.F6.GoldAmL4.evalFrom P Q (r * (if b then Q else P)) wd) =
      CFSG.Quasithin.F6.GoldAmL4.evalFrom (f P) (f Q) (f r * (if b then f Q else f P)) wd
    rw [h1, hf.mul _ hr _ hstep]
    cases b <;> rfl

theorem eq_Fu (hf : HomOn f) {w : Tc} (hw : w ∈ m2Sub) :
    f w = Fu (f tC, f tP, f tS) w := by
  have hspec : w = tC ^ (nfOf w).1 *
      CFSG.Quasithin.F6.GoldAmL4.evalFrom tP tS 1 (nfOf w).2 := nf_spec w hw
  have hk : tC ^ (nfOf w).1 ∈ m2Sub := m2Sub.pow_mem tC_mem _
  obtain ⟨h1, h2⟩ := hf.evalFrom tP_mem tS_mem (nfOf w).2 1 m2Sub.one_mem
  conv_lhs => rw [hspec]
  rw [hf.mul _ hk _ h2, hf.pow tC_mem, h1, hf.one]
  rfl

theorem rels (hf : HomOn f) : Rels (f tC, f tP, f tS) := by
  have e1 : tC ^ 4 = 1 := by decide +kernel
  have e2 : tP * tP = 1 := by decide +kernel
  have e3 : tS * tS = 1 := by decide +kernel
  have e4 : tC * tP = tP * tC := by decide +kernel
  have e5 : tC * tS = tS * tC := by decide +kernel
  have e6 : (tP * tS) ^ 4 = 1 := by decide +kernel
  have e7 : tC * tC = (tP * tS) ^ 2 := by decide +kernel
  have hPS : tP * tS ∈ m2Sub := m2Sub.mul_mem tP_mem tS_mem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hf.pow tC_mem, e1, hf.one]
  · rw [← hf.mul _ tP_mem _ tP_mem, e2, hf.one]
  · rw [← hf.mul _ tS_mem _ tS_mem, e3, hf.one]
  · rw [← hf.mul _ tC_mem _ tP_mem, e4, hf.mul _ tP_mem _ tC_mem]
  · rw [← hf.mul _ tC_mem _ tS_mem, e5, hf.mul _ tS_mem _ tC_mem]
  · rw [← hf.mul _ tP_mem _ tS_mem, ← hf.pow hPS, e6, hf.one]
  · rw [← hf.mul _ tC_mem _ tC_mem, e7, hf.pow hPS, hf.mul _ tP_mem _ tS_mem]

end HomOn

theorem classify_B {f : Tc → Tc} (hf : HomOn f) (h3 : ∀ x ∈ m2Sub, f (f (f x)) = x)
    (hne : ¬ (f tC = tC ∧ f tP = tP ∧ f tS = tS)) :
    ∃ t : Tc, t * f (t⁻¹ * tC * t) * t⁻¹ = tC ∧ t * f (t⁻¹ * tP * t) * t⁻¹ = tS ∧
      t * f (t⁻¹ * tS * t) * t⁻¹ = ⟨1, 3, 1⟩ := by
  have hF : ∀ w ∈ m2Sub, Fu (f tC, f tP, f tS) w = f w := fun w hw => (hf.eq_Fu hw).symm
  have hcube : Cube (f tC, f tP, f tS) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hF _ tC_mem, hF _ (hf.mem _ tC_mem), hF _ (hf.mem _ (hf.mem _ tC_mem))]
      exact h3 _ tC_mem
    · rw [hF _ tP_mem, hF _ (hf.mem _ tP_mem), hF _ (hf.mem _ (hf.mem _ tP_mem))]
      exact h3 _ tP_mem
    · rw [hF _ tS_mem, hF _ (hf.mem _ tS_mem), hF _ (hf.mem _ (hf.mem _ tS_mem))]
      exact h3 _ tS_mem
  obtain ⟨t, ht⟩ := classify_B_aux (f tC) (f tP) (f tS) (hf.mem _ tC_mem) (hf.mem _ tP_mem)
    (hf.mem _ tS_mem) hf.rels (fun h => hne (by simpa [Prod.ext_iff] using h)) hcube
  refine ⟨t, ?_⟩
  have hn : ∀ g ∈ m2Sub, t⁻¹ * g * t ∈ m2Sub := fun g hg => by
    simpa using m2_normal t⁻¹ g hg
  unfold ConjTrip at ht
  rw [hF _ (hn _ tC_mem), hF _ (hn _ tP_mem), hF _ (hn _ tS_mem)] at ht
  unfold alpha0 at ht
  simpa [Prod.ext_iff] using ht

@[expose] def xAct (w : Tc) : Tc := ⟨-w.j, w.i - w.j, 0⟩

theorem xAct_eq : ∀ i j : Fin 4, xAct ⟨i, j, 0⟩ = tB ^ i.val * (tA⁻¹ * tB⁻¹) ^ j.val := by
  decide +kernel

theorem xAct_mem : ∀ w : Tc, w ∈ baseSub → xAct w ∈ baseSub := by decide +kernel

theorem tc_alpha0 : (⟨1, 3, 1⟩ : Tc) = tA * tB⁻¹ * tS := by decide +kernel

theorem xAct_fixed : ∀ w : Tc, w ∈ baseSub → xAct w = w → w = 1 := by decide +kernel

theorem xAct_surj : ∀ w : Tc, w ∈ baseSub →
    ∃ v : Tc, v ∈ baseSub ∧ v * xAct (xAct v⁻¹) = w := by decide +kernel

theorem swap_xAct : ∀ w : Tc, w ∈ baseSub → tS * w * tS⁻¹ = xAct w → w = tA ^ w.i.val := by
  decide +kernel

theorem odd_of_sq : ∀ i : Fin 4, tA ^ (i.val * i.val) = tA → i = 1 ∨ i = 3 := by decide +kernel

theorem exists_base_mul_tS : ∀ w : Tc, w ∉ baseSub → ∃ w₀ : Tc, w₀ ∈ baseSub ∧ w = w₀ * tS := by
  decide +kernel

theorem tc_closure : Subgroup.closure ({tA, tB, tS} : Set Tc) = ⊤ := by
  rw [eq_top_iff]
  intro w _
  have hA : tA ∈ Subgroup.closure ({tA, tB, tS} : Set Tc) := Subgroup.subset_closure (by simp)
  have hB : tB ∈ Subgroup.closure ({tA, tB, tS} : Set Tc) := Subgroup.subset_closure (by simp)
  have hS : tS ∈ Subgroup.closure ({tA, tB, tS} : Set Tc) := Subgroup.subset_closure (by simp)
  rw [tc_nf w]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hA _)
    (Subgroup.pow_mem _ hB _)) (Subgroup.pow_mem _ hS _)

@[expose] def sigma (w : Tc) : Tc := ⟨-w.i, -w.j, w.e⟩

theorem sigma_mul : ∀ x y : Tc, sigma (x * y) = sigma x * sigma y := by decide +kernel

theorem sigma_sigma : ∀ w : Tc, sigma (sigma w) = w := by decide +kernel

theorem sigma_m2 : ∀ w : Tc, w ∈ m2Sub → sigma w ∈ m2Sub := by decide +kernel

theorem sigma_one : sigma 1 = 1 := by decide +kernel

theorem sigma_tA : sigma tA = tA⁻¹ := by decide +kernel

theorem sigma_tB : sigma tB = tB⁻¹ := by decide +kernel

theorem sigma_tS : sigma tS = tS := by decide +kernel

@[expose] def sigmaHom : Tc →* Tc where
  toFun := sigma
  map_one' := sigma_one
  map_mul' := sigma_mul

@[expose] def tU : Tc := ⟨1, 3, 0⟩

theorem tU_mem : tU ∈ m2Sub := by decide +kernel

theorem tU_eq : tU = tA * tB⁻¹ := by decide +kernel

theorem sigma_alpha0_sigma : ∀ w : Tc, w ∈ m2Sub →
    sigma (Fu alpha0 (sigma w)) = Fu alpha0 (tU⁻¹ * w * tU) := by decide +kernel

theorem tU_norm : tU * Fu alpha0 (Fu alpha0 tU) *
    Fu alpha0 (Fu alpha0 (Fu alpha0 (Fu alpha0 tU))) = 1 := by decide +kernel

theorem sigma_tC_sq : sigma (tC * tC) = tC * tC := by decide +kernel

theorem tCsq_mem_base : tC * tC ∈ baseSub := by decide +kernel

theorem xAct_tCsq : xAct (tC * tC) ≠ tC * tC := by decide +kernel

theorem alpha0_norm_one : (1 : Tc) * Fu alpha0 (Fu alpha0 1) *
    Fu alpha0 (Fu alpha0 (Fu alpha0 (Fu alpha0 1))) = 1 := by decide +kernel

theorem tC_ne_one : tC ≠ 1 := by decide +kernel

end CFSG.Quasithin.F6.GoldAmL4
