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

namespace CFSG.Quasithin.F6.GoldAmL4

abbrev V4 : Type := ZMod 4 × ZMod 4

@[expose] def app (M : V4 × V4) (v : V4) : V4 :=
  (v.1 * M.1.1 + v.2 * M.2.1, v.1 * M.1.2 + v.2 * M.2.2)

@[expose] def mmul (M N : V4 × V4) : V4 × V4 := (app M N.1, app M N.2)

@[expose] def mI : V4 × V4 := ((1, 0), (0, 1))

set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

theorem fin_fixed : ∀ X : V4 × V4, mmul X (mmul X X) = mI → X ≠ mI →
    ∀ v : V4, app X v = v → v = 0 := by decide +kernel

theorem fin_solve : ∀ X : V4 × V4, mmul X (mmul X X) = mI → X ≠ mI →
    ∀ v : V4, ∃ r : V4, r - app (mmul X X) r = v := by decide +kernel

theorem fin_basis : ∀ X S : V4 × V4, mmul X (mmul X X) = mI → X ≠ mI → mmul S S = mI →
    mmul S X = mmul (mmul X X) S →
    ∃ w₁ : V4, app S w₁ = app (mmul X X) w₁ ∧
      app (mmul X X) (app (mmul X X) w₁) = - w₁ - app (mmul X X) w₁ ∧
      app S (app S w₁) = w₁ ∧
      (∀ v : V4, ∃ m n : Fin 4, v = m.val • w₁ + n.val • app (mmul X X) w₁) := by
  decide +kernel

theorem app_eq_nsmul (M : V4 × V4) (v : V4) : app M v = v.1.val • M.1 + v.2.val • M.2 := by
  ext <;> simp [app, nsmul_eq_mul]

section Coord

variable {D : Type*} [Group D] {Q : Subgroup D} (ε : ↥Q ≃* Multiplicative V4)

@[expose] def Qelt (v : V4) : D := ((ε.symm (Multiplicative.ofAdd v) : ↥Q) : D)

open Classical in
@[expose] noncomputable def Qvec (q : D) : V4 :=
  if h : q ∈ Q then Multiplicative.toAdd (ε ⟨q, h⟩) else 0

theorem Qelt_mem (v : V4) : Qelt ε v ∈ Q := (ε.symm (Multiplicative.ofAdd v)).2

theorem Qvec_Qelt (v : V4) : Qvec ε (Qelt ε v) = v := by
  unfold Qvec
  rw [dite_eq_left_of_eq_true (eq_true (Qelt_mem ε v))]
  have : (⟨Qelt ε v, Qelt_mem ε v⟩ : ↥Q) = ε.symm (Multiplicative.ofAdd v) := rfl
  rw [this, MulEquiv.apply_symm_apply]
  rfl

theorem Qelt_Qvec {q : D} (h : q ∈ Q) : Qelt ε (Qvec ε q) = q := by
  unfold Qvec Qelt
  rw [dite_eq_left_of_eq_true (eq_true h)]
  simp

theorem Qelt_add (v w : V4) : Qelt ε (v + w) = Qelt ε v * Qelt ε w := by
  unfold Qelt
  rw [show Multiplicative.ofAdd (v + w) = Multiplicative.ofAdd v * Multiplicative.ofAdd w from rfl,
    map_mul]
  rfl

theorem Qelt_zero : Qelt ε 0 = 1 := by
  unfold Qelt
  rw [show Multiplicative.ofAdd (0 : V4) = 1 from rfl, map_one]
  rfl

theorem Qelt_neg (v : V4) : Qelt ε (-v) = (Qelt ε v)⁻¹ := by
  unfold Qelt
  rw [show Multiplicative.ofAdd (-v) = (Multiplicative.ofAdd v)⁻¹ from rfl, map_inv]
  rfl

theorem Qelt_nsmul (n : ℕ) (v : V4) : Qelt ε (n • v) = Qelt ε v ^ n := by
  induction n with
  | zero => simp [Qelt_zero]
  | succ n ih => rw [succ_nsmul, Qelt_add, ih, pow_succ]

theorem Qelt_comm (v w : V4) : Qelt ε v * Qelt ε w = Qelt ε w * Qelt ε v := by
  rw [← Qelt_add, ← Qelt_add, add_comm]

theorem Qelt_pow_four (v : V4) : Qelt ε v ^ 4 = 1 := by
  have h4 : (4 : ZMod 4) = 0 := by decide
  rw [← Qelt_nsmul, show (4 : ℕ) • v = 0 by ext <;> simp [nsmul_eq_mul, h4], Qelt_zero]

theorem Qvec_mul {q q' : D} (hq : q ∈ Q) (hq' : q' ∈ Q) :
    Qvec ε (q * q') = Qvec ε q + Qvec ε q' := by
  have hqq : q * q' ∈ Q := Q.mul_mem hq hq'
  unfold Qvec
  rw [dite_eq_left_of_eq_true (eq_true hq), dite_eq_left_of_eq_true (eq_true hq'),
    dite_eq_left_of_eq_true (eq_true hqq)]
  have : (⟨q * q', hqq⟩ : ↥Q) = ⟨q, hq⟩ * ⟨q', hq'⟩ := rfl
  rw [this, map_mul]
  rfl

theorem Qvec_one : Qvec ε (1 : D) = 0 := by
  have := Qvec_Qelt ε 0
  rwa [Qelt_zero] at this

@[expose] noncomputable def cact (g : D) (v : V4) : V4 := Qvec ε (g * Qelt ε v * g⁻¹)

theorem cact_zero (g : D) : cact ε g 0 = 0 := by
  unfold cact
  rw [Qelt_zero, mul_one, mul_inv_cancel, Qvec_one]

theorem cact_one (v : V4) : cact ε (1 : D) v = v := by
  unfold cact
  rw [one_mul, inv_one, mul_one, Qvec_Qelt]

theorem cact_of_mem {q : D} (hq : q ∈ Q) (v : V4) : cact ε q v = v := by
  unfold cact
  have hc : q * Qelt ε v * q⁻¹ = Qelt ε v := by
    have := Qelt_comm ε (Qvec ε q) v
    rw [Qelt_Qvec ε hq] at this
    rw [this]; group
  rw [hc, Qvec_Qelt]

@[expose] noncomputable def mat (g : D) : V4 × V4 := (cact ε g (1, 0), cact ε g (0, 1))

theorem mat_one : mat ε (1 : D) = mI := by
  unfold mat mI
  rw [cact_one, cact_one]

theorem mat_of_mem {q : D} (hq : q ∈ Q) : mat ε q = mI := by
  unfold mat mI
  rw [cact_of_mem ε hq, cact_of_mem ε hq]

variable {G : Subgroup D} (hG : ∀ g ∈ G, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)

include hG

theorem Qelt_cact {g : D} (hg : g ∈ G) (v : V4) :
    Qelt ε (cact ε g v) = g * Qelt ε v * g⁻¹ :=
  Qelt_Qvec ε (hG g hg _ (Qelt_mem ε v))

theorem cact_add {g : D} (hg : g ∈ G) (v w : V4) :
    cact ε g (v + w) = cact ε g v + cact ε g w := by
  unfold cact
  have e : g * Qelt ε (v + w) * g⁻¹ = (g * Qelt ε v * g⁻¹) * (g * Qelt ε w * g⁻¹) := by
    rw [Qelt_add]; group
  rw [e, Qvec_mul ε (hG g hg _ (Qelt_mem ε v)) (hG g hg _ (Qelt_mem ε w))]

theorem cact_nsmul {g : D} (hg : g ∈ G) (n : ℕ) (v : V4) :
    cact ε g (n • v) = n • cact ε g v := by
  induction n with
  | zero => simp [cact_zero ε]
  | succ n ih => rw [succ_nsmul, cact_add ε hG hg, ih, succ_nsmul]

theorem cact_mul {g h : D} (hh : h ∈ G) (v : V4) :
    cact ε (g * h) v = cact ε g (cact ε h v) := by
  unfold cact
  rw [Qelt_Qvec ε (hG h hh _ (Qelt_mem ε v))]
  congr 1
  group

theorem cact_eq_app {g : D} (hg : g ∈ G) (v : V4) : cact ε g v = app (mat ε g) v := by
  rw [app_eq_nsmul]
  have hv : v = v.1.val • ((1 : ZMod 4), (0 : ZMod 4)) +
      v.2.val • ((0 : ZMod 4), (1 : ZMod 4)) := by
    ext <;> simp [nsmul_eq_mul]
  conv_lhs => rw [hv]
  rw [cact_add ε hG hg, cact_nsmul ε hG hg, cact_nsmul ε hG hg]
  rfl

theorem mat_mul {g h : D} (hg : g ∈ G) (hh : h ∈ G) :
    mat ε (g * h) = mmul (mat ε g) (mat ε h) := by
  unfold mat mmul
  rw [cact_mul ε hG hh, cact_mul ε hG hh, cact_eq_app ε hG hg, cact_eq_app ε hG hg]
  rfl

end Coord

end CFSG.Quasithin.F6.GoldAmL4
