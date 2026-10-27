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
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

public section

namespace CFSG.Quasithin.RonanF95

open Module

structure TwoInv (E : Type*) [AddCommGroup E] [Module (ZMod 2) E] where
  b : E →ₗ[ZMod 2] E →ₗ[ZMod 2] ZMod 2
  q : E → ZMod 2
  v : Module.End (ZMod 2) E
  i : Module.End (ZMod 2) E
  X : Submodule (ZMod 2) E
  Y : Submodule (ZMod 2) E
  hq : ∀ x y, q (x + y) = q x + q y + b x y
  hbalt : ∀ x, b x x = 0
  hbnd : ∀ x, (∀ y, b x y = 0) → x = 0
  hv : v * v = 1
  hi : i * i = 1
  hqv : ∀ x, q (v x) = q x
  hqi : ∀ x, q (i x) = q x
  hXv : ∀ x, x ∈ X ↔ v x = x
  hYi : ∀ y, y ∈ Y ↔ i y = y
  hvX : ∀ y, v y + y ∈ X
  hiY : ∀ x, i x + x ∈ Y
  hXY : IsCompl X Y
  hqX : ∀ x ∈ X, q x = 0
  hqY : ∀ y ∈ Y, q y = 0

namespace TwoInv

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] (S : TwoInv E)

@[expose] def t : Module.End (ZMod 2) E := S.v * S.i

@[expose] def D : Module.End (ZMod 2) E := S.v * S.i + S.i * S.v

@[expose] def nv : Module.End (ZMod 2) E := S.v + 1

@[expose] def ni : Module.End (ZMod 2) E := S.i + 1

theorem vec_self_add (x : E) : x + x = 0 := by
  have h2 : (1 + 1 : ZMod 2) = 0 := by decide
  calc x + x = (1 + 1 : ZMod 2) • x := by rw [add_smul, one_smul]
    _ = 0 := by rw [h2, zero_smul]

theorem vec_eq_of_add_eq_zero (a b : E) (h : a + b = 0) : a = b := by
  have hbb : b + b = 0 := vec_self_add b
  calc a = a + 0 := (add_zero a).symm
    _ = a + (b + b) := by rw [hbb]
    _ = a + b + b := (add_assoc a b b).symm
    _ = 0 + b := by rw [h]
    _ = b := zero_add b

theorem char_two : (2 : Module.End (ZMod 2) E) = 0 := by
  have h : (2 : Module.End (ZMod 2) E) = algebraMap (ZMod 2) (Module.End (ZMod 2) E) 2 :=
    (map_ofNat (algebraMap (ZMod 2) (Module.End (ZMod 2) E)) 2).symm
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h, h2, map_zero]

theorem one_add_one_zero : (1 : Module.End (ZMod 2) E) + 1 = 0 := by
  rw [one_add_one_eq_two, char_two]

theorem v_v (w : E) : S.v (S.v w) = w := by
  have h := congrArg (fun f : Module.End (ZMod 2) E => f w) S.hv
  exact h

theorem i_i (w : E) : S.i (S.i w) = w := by
  have h := congrArg (fun f : Module.End (ZMod 2) E => f w) S.hi
  exact h

theorem D_mul_t : S.D * S.t = S.t * S.t + 1 := by
  have h1 : (S.i * S.v) * (S.v * S.i) = 1 := by
    calc (S.i * S.v) * (S.v * S.i) = S.i * ((S.v * S.v) * S.i) := by simp only [mul_assoc]
      _ = 1 := by rw [S.hv, one_mul, S.hi]
  unfold D t
  rw [add_mul, h1]

theorem t_sq : S.t * S.t = S.D * S.t + 1 := by
  rw [D_mul_t, add_assoc, one_add_one_zero, add_zero]

theorem D_comm_v : S.D * S.v = S.v * S.D := by
  have h1 : S.i * S.v * S.v = S.i := by rw [mul_assoc, S.hv, mul_one]
  have h2 : S.v * (S.v * S.i) = S.i := by rw [← mul_assoc, S.hv, one_mul]
  unfold D
  rw [add_mul, mul_add, h1, h2, mul_assoc]
  exact add_comm _ _

theorem D_comm_i : S.D * S.i = S.i * S.D := by
  have h1 : S.v * S.i * S.i = S.v := by rw [mul_assoc, S.hi, mul_one]
  have h2 : S.i * (S.i * S.v) = S.v := by rw [← mul_assoc, S.hi, one_mul]
  unfold D
  rw [add_mul, mul_add, h1, h2, mul_assoc]
  exact add_comm _ _

theorem D_comm_t : S.D * S.t = S.t * S.D := by
  unfold t
  rw [← mul_assoc, D_comm_v, mul_assoc, D_comm_i, ← mul_assoc]

theorem D_comm_ni : S.D * S.ni = S.ni * S.D := by
  unfold ni
  rw [mul_add, add_mul, D_comm_i, mul_one, one_mul]

theorem b_symm (x y : E) : S.b x y = S.b y x := by
  have h1 : S.q (x + y) = S.q x + S.q y + S.b x y := S.hq x y
  have h2 : S.q (x + y) = S.q y + S.q x + S.b y x := by
    rw [add_comm x y]
    exact S.hq y x
  linear_combination h2 - h1

theorem b_X (x x' : E) (hx : x ∈ S.X) (hx' : x' ∈ S.X) : S.b x x' = 0 := by
  have h := S.hq x x'
  rw [S.hqX _ (S.X.add_mem hx hx'), S.hqX _ hx, S.hqX _ hx'] at h
  linear_combination -h

theorem b_Y (y y' : E) (hy : y ∈ S.Y) (hy' : y' ∈ S.Y) : S.b y y' = 0 := by
  have h := S.hq y y'
  rw [S.hqY _ (S.Y.add_mem hy hy'), S.hqY _ hy, S.hqY _ hy'] at h
  linear_combination -h

theorem b_v (x y : E) : S.b (S.v x) (S.v y) = S.b x y := by
  have h1 : S.q (x + y) = S.q x + S.q y + S.b x y := S.hq x y
  have h2 : S.q (S.v x + S.v y) = S.q (S.v x) + S.q (S.v y) + S.b (S.v x) (S.v y) :=
    S.hq (S.v x) (S.v y)
  have h3 : S.q (S.v x + S.v y) = S.q (x + y) := by
    rw [← map_add S.v x y, S.hqv]
  have h4 : S.q (S.v x) = S.q x := S.hqv x
  have h5 : S.q (S.v y) = S.q y := S.hqv y
  linear_combination h1 - h2 + h3 - h4 - h5

theorem b_i (x y : E) : S.b (S.i x) (S.i y) = S.b x y := by
  have h1 : S.q (x + y) = S.q x + S.q y + S.b x y := S.hq x y
  have h2 : S.q (S.i x + S.i y) = S.q (S.i x) + S.q (S.i y) + S.b (S.i x) (S.i y) :=
    S.hq (S.i x) (S.i y)
  have h3 : S.q (S.i x + S.i y) = S.q (x + y) := by
    rw [← map_add S.i x y, S.hqi]
  have h4 : S.q (S.i x) = S.q x := S.hqi x
  have h5 : S.q (S.i y) = S.q y := S.hqi y
  linear_combination h1 - h2 + h3 - h4 - h5

theorem b_v_left (z w : E) : S.b (S.v z) w = S.b z (S.v w) := by
  have h := S.b_v z (S.v w)
  rw [S.v_v] at h
  exact h

theorem b_i_left (z w : E) : S.b (S.i z) w = S.b z (S.i w) := by
  have h := S.b_i z (S.i w)
  rw [S.i_i] at h
  exact h

theorem D_selfAdj (x y : E) : S.b (S.D x) y = S.b x (S.D y) := by
  have hDx : S.D x = S.v (S.i x) + S.i (S.v x) := rfl
  have hDy : S.D y = S.v (S.i y) + S.i (S.v y) := rfl
  have e1 := S.b_v_left (S.i x) y
  have e2 := S.b_i_left (S.v x) y
  have e3 := S.b_v_left x (S.i y)
  have e4 := S.b_i_left x (S.v y)
  simp only [hDx, hDy, map_add, LinearMap.add_apply]
  linear_combination e1 + e2 + e3 + e4

theorem D_mem_X (x : E) (hx : x ∈ S.X) : S.D x ∈ S.X := by
  have hvx : S.v x = x := (S.hXv x).1 hx
  have hDx : S.D x = S.v (S.i x) + S.i x := by
    show S.v (S.i x) + S.i (S.v x) = S.v (S.i x) + S.i x
    rw [hvx]
  rw [hDx]
  exact S.hvX (S.i x)

theorem ni_inj_X (x : E) (hx : x ∈ S.X) (h : S.ni x = 0) : x = 0 := by
  have h' : S.i x + x = 0 := h
  have hix : S.i x = x := vec_eq_of_add_eq_zero _ _ h'
  have hxY : x ∈ S.Y := (S.hYi x).2 hix
  exact (Submodule.disjoint_def.mp S.hXY.disjoint) x hx hxY

theorem nv_inj_Y (y : E) (hy : y ∈ S.Y) (h : S.nv y = 0) : y = 0 := by
  have h' : S.v y + y = 0 := h
  have hvy : S.v y = y := vec_eq_of_add_eq_zero _ _ h'
  have hyX : y ∈ S.X := (S.hXv y).2 hvy
  exact (Submodule.disjoint_def.mp S.hXY.disjoint) y hyX hy

theorem nv_ni_X (x : E) (hx : x ∈ S.X) : S.nv (S.ni x) = S.D x := by
  have hvx : S.v x = x := (S.hXv x).1 hx
  have hxx : x + x = 0 := vec_self_add x
  show S.v (S.i x + x) + (S.i x + x) = S.v (S.i x) + S.i (S.v x)
  rw [map_add, hvx]
  calc S.v (S.i x) + x + (S.i x + x) = S.v (S.i x) + S.i x + (x + x) := by abel
    _ = S.v (S.i x) + S.i x := by rw [hxx, add_zero]

theorem D_inj_X (x : E) (hx : x ∈ S.X) (h : S.D x = 0) : x = 0 := by
  have hY : S.ni x ∈ S.Y := S.hiY x
  have h1 : S.nv (S.ni x) = 0 := (S.nv_ni_X x hx).trans h
  have h2 : S.ni x = 0 := S.nv_inj_Y (S.ni x) hY h1
  exact S.ni_inj_X x hx h2

theorem ni_mem_Y (x : E) : S.ni x ∈ S.Y := by
  show S.i x + x ∈ S.Y
  exact S.hiY x

variable [Finite E]

theorem nv_mem_X (y : E) : S.nv y ∈ S.X := by
  show S.v y + y ∈ S.X
  exact S.hvX y

theorem finrank_Y : finrank (ZMod 2) S.Y = finrank (ZMod 2) S.X := by
  let f : S.X →ₗ[ZMod 2] S.Y :=
    LinearMap.codRestrict S.Y (LinearMap.comp S.ni S.X.subtype) (fun c => S.ni_mem_Y (c : E))
  let g : S.Y →ₗ[ZMod 2] S.X :=
    LinearMap.codRestrict S.X (LinearMap.comp S.nv S.Y.subtype) (fun c => S.nv_mem_X (c : E))
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have h1 : S.ni (c : E) = 0 := congrArg Subtype.val hc
    exact Subtype.ext (S.ni_inj_X c c.2 h1)
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have h1 : S.nv (c : E) = 0 := congrArg Subtype.val hc
    exact Subtype.ext (S.nv_inj_Y c c.2 h1)
  exact le_antisymm (LinearMap.finrank_le_finrank_of_injective hg)
    (LinearMap.finrank_le_finrank_of_injective hf)

theorem finrank_E : finrank (ZMod 2) E = 2 * finrank (ZMod 2) S.X := by
  have h := Submodule.finrank_add_eq_of_isCompl S.hXY
  rw [finrank_Y S] at h
  omega

end TwoInv

end CFSG.Quasithin.RonanF95
