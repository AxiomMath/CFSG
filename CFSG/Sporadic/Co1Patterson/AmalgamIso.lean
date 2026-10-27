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

namespace CFSG.Sporadic.Co1Patterson

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

structure IsoOn (f : G → G') (H : Subgroup G) (H' : Subgroup G') : Prop where
  map_mem : ∀ x ∈ H, f x ∈ H'
  map_mul : ∀ x ∈ H, ∀ y ∈ H, f (x * y) = f x * f y
  injOn : Set.InjOn f H
  surjOn : ∀ y ∈ H', ∃ x ∈ H, f x = y

namespace IsoOn

variable {f : G → G'} {H : Subgroup G} {H' : Subgroup G'}

theorem map_one (hf : IsoOn f H H') : f 1 = 1 := by
  have h := hf.map_mul 1 H.one_mem 1 H.one_mem
  rw [one_mul] at h
  exact (mul_eq_left.mp h.symm)

theorem map_inv (hf : IsoOn f H H') {x : G} (hx : x ∈ H) : f x⁻¹ = (f x)⁻¹ := by
  have h := hf.map_mul x hx x⁻¹ (H.inv_mem hx)
  rw [mul_inv_cancel, hf.map_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem map_conj (hf : IsoOn f H H') {g x : G} (hg : g ∈ H) (hx : x ∈ H) :
    f (g * x * g⁻¹) = f g * f x * (f g)⁻¹ := by
  rw [hf.map_mul _ (H.mul_mem hg hx) _ (H.inv_mem hg), hf.map_mul _ hg _ hx, hf.map_inv hg]

theorem map_pow (hf : IsoOn f H H') {x : G} (hx : x ∈ H) (n : ℕ) : f (x ^ n) = f x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, hf.map_one]
  | succ n ih => rw [pow_succ, pow_succ, hf.map_mul _ (H.pow_mem hx n) _ hx, ih]

theorem orderOf_eq (hf : IsoOn f H H') {x : G} (hx : x ∈ H) : orderOf (f x) = orderOf x := by
  have hinj : Function.Injective (H'.subtype.comp
      { toFun := fun y : H => (⟨f y, hf.map_mem y y.2⟩ : H')
        map_one' := Subtype.ext hf.map_one
        map_mul' := fun y z => Subtype.ext (hf.map_mul y y.2 z z.2) }) := fun y z hyz =>
    Subtype.ext (hf.injOn y.2 z.2 hyz)
  have := orderOf_injective _ hinj ⟨x, hx⟩
  rwa [Subgroup.orderOf_mk] at this

theorem comp {g : G' → G''} {H'' : Subgroup G''} (hf : IsoOn f H H') (hg : IsoOn g H' H'') :
    IsoOn (fun x => g (f x)) H H'' where
  map_mem x hx := hg.map_mem _ (hf.map_mem x hx)
  map_mul x hx y hy := by
    rw [hf.map_mul x hx y hy, hg.map_mul _ (hf.map_mem x hx) _ (hf.map_mem y hy)]
  injOn x hx y hy h := hf.injOn hx hy (hg.injOn (hf.map_mem x hx) (hf.map_mem y hy) h)
  surjOn z hz := by
    obtain ⟨y, hy, rfl⟩ := hg.surjOn z hz
    obtain ⟨x, hx, rfl⟩ := hf.surjOn y hy
    exact ⟨x, hx, rfl⟩

theorem restrict (hf : IsoOn f H H') {K : Subgroup G} {K' : Subgroup G'} (hK : K ≤ H)
    (hmem : ∀ x ∈ K, f x ∈ K') (hsurj : ∀ y ∈ K', ∃ x ∈ K, f x = y) : IsoOn f K K' where
  map_mem := hmem
  map_mul x hx y hy := hf.map_mul x (hK hx) y (hK hy)
  injOn _ hx _ hy h := hf.injOn (hK hx) (hK hy) h
  surjOn := hsurj

theorem congr (hf : IsoOn f H H') {f' : G → G'} (h : ∀ x ∈ H, f' x = f x) : IsoOn f' H H' where
  map_mem x hx := h x hx ▸ hf.map_mem x hx
  map_mul x hx y hy := by
    rw [h _ (H.mul_mem hx hy), h x hx, h y hy, hf.map_mul x hx y hy]
  injOn x hx y hy e := hf.injOn hx hy (by rw [← h x hx, ← h y hy, e])
  surjOn y hy := by
    obtain ⟨x, hx, rfl⟩ := hf.surjOn y hy
    exact ⟨x, hx, h x hx⟩

@[expose] def toHom (hf : IsoOn f H H') : H →* H' where
  toFun x := ⟨f x, hf.map_mem x x.2⟩
  map_one' := Subtype.ext hf.map_one
  map_mul' x y := Subtype.ext (hf.map_mul x x.2 y y.2)

@[expose] noncomputable def toMulEquiv (hf : IsoOn f H H') : H ≃* H' :=
  MulEquiv.ofBijective hf.toHom
    ⟨fun x y hxy => Subtype.ext (hf.injOn x.2 y.2 (congrArg Subtype.val hxy)), fun y => by
      obtain ⟨x, hx, hxy⟩ := hf.surjOn y y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

@[simp] theorem toMulEquiv_apply (hf : IsoOn f H H') (x : H) :
    (hf.toMulEquiv x : G') = f x := rfl

open Classical in
@[expose] noncomputable def inv (hf : IsoOn f H H') (y : G') : G :=
  if hy : y ∈ H' then (hf.toMulEquiv.symm ⟨y, hy⟩ : G) else 1

theorem inv_of_mem (hf : IsoOn f H H') {y : G'} (hy : y ∈ H') :
    hf.inv y = (hf.toMulEquiv.symm ⟨y, hy⟩ : G) := by
  simp only [inv, hy, ↓reduceDIte]

theorem inv_mem (hf : IsoOn f H H') {y : G'} (hy : y ∈ H') : hf.inv y ∈ H := by
  rw [hf.inv_of_mem hy]
  exact (hf.toMulEquiv.symm ⟨y, hy⟩).2

theorem apply_inv (hf : IsoOn f H H') {y : G'} (hy : y ∈ H') : f (hf.inv y) = y := by
  rw [hf.inv_of_mem hy, ← hf.toMulEquiv_apply (hf.toMulEquiv.symm ⟨y, hy⟩)]
  exact congrArg Subtype.val (hf.toMulEquiv.apply_symm_apply ⟨y, hy⟩)

theorem inv_apply (hf : IsoOn f H H') {x : G} (hx : x ∈ H) : hf.inv (f x) = x :=
  hf.injOn (hf.inv_mem (hf.map_mem x hx)) hx (hf.apply_inv (hf.map_mem x hx))

theorem isoOn_inv (hf : IsoOn f H H') : IsoOn hf.inv H' H where
  map_mem _ hy := hf.inv_mem hy
  map_mul x hx y hy := by
    refine hf.injOn (hf.inv_mem (H'.mul_mem hx hy))
      (H.mul_mem (hf.inv_mem hx) (hf.inv_mem hy)) ?_
    rw [hf.apply_inv (H'.mul_mem hx hy), hf.map_mul _ (hf.inv_mem hx) _ (hf.inv_mem hy),
      hf.apply_inv hx, hf.apply_inv hy]
  injOn x hx y hy h := by
    rw [← hf.apply_inv hx, ← hf.apply_inv hy, h]
  surjOn x hx := ⟨f x, hf.map_mem x hx, hf.inv_apply hx⟩

end IsoOn

theorem isoOn_conj (c : G) {H H' : Subgroup G} (h : ∀ x, x ∈ H ↔ c * x * c⁻¹ ∈ H') :
    IsoOn (fun x => c * x * c⁻¹) H H' where
  map_mem x hx := (h x).1 hx
  map_mul _ _ _ _ := by group
  injOn _ _ _ _ e := by simpa using e
  surjOn y hy := ⟨c⁻¹ * y * c, (h _).2 (by simpa [mul_assoc] using hy), by group⟩

open Classical in
@[expose] noncomputable def extFun {H : Subgroup G} {H' : Subgroup G'} (e : H ≃* H') (x : G) : G' :=
  if hx : x ∈ H then (e ⟨x, hx⟩ : G') else 1

theorem extFun_of_mem {H : Subgroup G} {H' : Subgroup G'} (e : H ≃* H') {x : G} (hx : x ∈ H) :
    extFun e x = e ⟨x, hx⟩ := by
  simp only [extFun, hx, ↓reduceDIte]

theorem isoOn_extFun {H : Subgroup G} {H' : Subgroup G'} (e : H ≃* H') :
    IsoOn (extFun e) H H' where
  map_mem x hx := by rw [extFun_of_mem e hx]; exact (e ⟨x, hx⟩).2
  map_mul x hx y hy := by
    rw [extFun_of_mem e hx, extFun_of_mem e hy, extFun_of_mem e (H.mul_mem hx hy)]
    exact congrArg Subtype.val (e.map_mul ⟨x, hx⟩ ⟨y, hy⟩)
  injOn x hx y hy h := by
    rw [extFun_of_mem e hx, extFun_of_mem e hy] at h
    exact congrArg Subtype.val (e.injective (Subtype.ext h))
  surjOn y hy := ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).2, by
    rw [extFun_of_mem e (e.symm ⟨y, hy⟩).2]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)⟩

end CFSG.Sporadic.Co1Patterson
