module

import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.AutAlternatingFour
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
public import Mathlib.GroupTheory.SpecificGroups.Alternating
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

namespace CFSG.SignalizerFunctorTheorem.McBride.PSL2Three

theorem a4_mul_sq : ∀ x y : alternatingGroup (Fin 4), x ^ 2 = 1 → y ^ 2 = 1 → (x * y) ^ 2 = 1 := by
  decide +kernel

theorem a4_card_sq : Nat.card {x : alternatingGroup (Fin 4) // x ^ 2 = 1} = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem a4_sq_or_cube : ∀ x : alternatingGroup (Fin 4), x ^ 2 = 1 ∨ x ^ 3 = 1 := by
  decide +kernel

theorem a4_comm_sq : ∀ x y : alternatingGroup (Fin 4), (x * y * x⁻¹ * y⁻¹) ^ 2 = 1 := by
  decide +kernel

theorem a4_centralizer : ∀ x : alternatingGroup (Fin 4),
    (∀ v : alternatingGroup (Fin 4), v ^ 2 = 1 → x * v = v * x) → x ^ 2 = 1 := by
  decide +kernel

theorem a4_fpf : ∀ x z : alternatingGroup (Fin 4), x ^ 2 ≠ 1 ∧ z ^ 2 = 1 ∧ x * z = z * x →
    z = 1 := by
  decide +kernel

theorem a4_normal_gen : ∀ n : alternatingGroup (Fin 4), n ≠ 1 → ∀ v : alternatingGroup (Fin 4),
    v ^ 2 = 1 → ∃ x : alternatingGroup (Fin 4),
      v = 1 ∨ v = x * n * x⁻¹ ∨ v = x * n * x⁻¹ * n⁻¹ := by
  decide +kernel

theorem a4_exists_noncomm : ∃ a b : alternatingGroup (Fin 4), a * b ≠ b * a := by
  decide +kernel

theorem a4_card : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem a4_sign_eq_one : ∀ σ : Equiv.Perm (Fin 4),
    (∀ x : Equiv.Perm (Fin 4), Equiv.Perm.sign x = 1 → (x⁻¹ * (σ * x * σ⁻¹)) ^ 2 = 1) →
      Equiv.Perm.sign σ = 1 := by
  decide +kernel

variable {Y : Type*} [Group Y]

structure IsA4Subgroup (C : Subgroup Y) : Prop where
  card : Nat.card C = 12
  nonabelian : ∃ a ∈ C, ∃ b ∈ C, a * b ≠ b * a
  mul_sq : ∀ x ∈ C, ∀ y ∈ C, x ^ 2 = 1 → y ^ 2 = 1 → (x * y) ^ 2 = 1
  card_sq : Nat.card {x : Y // x ∈ C ∧ x ^ 2 = 1} = 4
  sq_or_cube : ∀ x ∈ C, x ^ 2 = 1 ∨ x ^ 3 = 1
  comm_sq : ∀ x ∈ C, ∀ y ∈ C, (x * y * x⁻¹ * y⁻¹) ^ 2 = 1
  centralizer_sq : ∀ x ∈ C, (∀ v ∈ C, v ^ 2 = 1 → x * v = v * x) → x ^ 2 = 1
  fpf : ∀ x ∈ C, ∀ z ∈ C, x ^ 2 ≠ 1 → z ^ 2 = 1 → x * z = z * x → z = 1
  normal_gen : ∀ n ∈ C, n ≠ 1 → ∀ v ∈ C, v ^ 2 = 1 →
    ∃ x ∈ C, v = 1 ∨ v = x * n * x⁻¹ ∨ v = x * n * x⁻¹ * n⁻¹
  aut_inner : ∀ g : MulAut Y, (∀ x ∈ C, g x ∈ C) → (∀ x ∈ C, (x⁻¹ * g x) ^ 2 = 1) →
    ∃ c ∈ C, ∀ x ∈ C, g x = c * x * c⁻¹

namespace IsA4Subgroup

variable {C : Subgroup Y}

@[expose] def klein (h : IsA4Subgroup C) : Subgroup Y where
  carrier := {x | x ∈ C ∧ x ^ 2 = 1}
  one_mem' := ⟨C.one_mem, one_pow 2⟩
  mul_mem' := fun ha hb => ⟨C.mul_mem ha.1 hb.1, h.mul_sq _ ha.1 _ hb.1 ha.2 hb.2⟩
  inv_mem' := fun ha => ⟨C.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem mem_klein (h : IsA4Subgroup C) {x : Y} : x ∈ h.klein ↔ x ∈ C ∧ x ^ 2 = 1 := Iff.rfl

theorem klein_le (h : IsA4Subgroup C) : h.klein ≤ C := fun _ hx => hx.1

theorem card_klein (h : IsA4Subgroup C) : Nat.card h.klein = 4 := h.card_sq

theorem klein_comm (h : IsA4Subgroup C) {x y : Y} (hx : x ∈ h.klein) (hy : y ∈ h.klein) :
    x * y = y * x := by
  have hxy := (h.klein.mul_mem hx hy).2
  have hx2 := hx.2
  have hy2 := hy.2
  have hx' : x⁻¹ = x := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hx2]
  have hy' : y⁻¹ = y := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hy2]
  have hxy' : (x * y)⁻¹ = x * y := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hxy]
  rw [← hxy', mul_inv_rev, hx', hy']

instance isMulCommutative_klein (h : IsA4Subgroup C) : IsMulCommutative h.klein :=
  ⟨⟨fun a b => Subtype.ext (h.klein_comm a.2 b.2)⟩⟩

theorem conj_mem_klein (h : IsA4Subgroup C) {c x : Y} (hc : c ∈ C) (hx : x ∈ h.klein) :
    c * x * c⁻¹ ∈ h.klein :=
  ⟨C.mul_mem (C.mul_mem hc hx.1) (C.inv_mem hc), by rw [conj_pow, hx.2]; group⟩

theorem exists_ne_one_mem_klein (h : IsA4Subgroup C) : ∃ v ∈ h.klein, v ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : Nat.card h.klein = 1 := Subgroup.card_eq_one.mpr
    ((Subgroup.eq_bot_iff_forall _).mpr hcon)
  rw [h.card_klein] at this
  omega

theorem orderOf_eq_two (h : IsA4Subgroup C) {v : Y} (hv : v ∈ h.klein) (hv1 : v ≠ 1) :
    orderOf v = 2 :=
  orderOf_eq_prime hv.2 hv1

theorem orderOf_eq_three (h : IsA4Subgroup C) {x : Y} (hx : x ∈ C) (hx2 : x ^ 2 ≠ 1) :
    orderOf x = 3 := by
  have hx3 : x ^ 3 = 1 := (h.sq_or_cube x hx).resolve_left hx2
  refine orderOf_eq_prime hx3 ?_
  rintro rfl
  exact hx2 (one_pow 2)

end IsA4Subgroup

section OfEquiv

variable {C : Subgroup Y}

private theorem pow_eq_one_iff (e : C ≃* alternatingGroup (Fin 4)) (z : C) (n : ℕ) :
    (e z) ^ n = 1 ↔ (z : Y) ^ n = 1 := by
  rw [← map_pow, MulEquiv.map_eq_one_iff, Subtype.ext_iff]
  simp

private theorem aut_inner_of_equiv (e : C ≃* alternatingGroup (Fin 4)) (g : MulAut Y)
    (hgC : ∀ x ∈ C, g x ∈ C) (hg2 : ∀ x ∈ C, (x⁻¹ * g x) ^ 2 = 1) :
    ∃ c ∈ C, ∀ x ∈ C, g x = c * x * c⁻¹ := by
  classical
  have hfin : Finite C := Finite.of_equiv _ e.symm.toEquiv
  let α : C →* C :=
    { toFun := fun x => ⟨g (x : Y), hgC x x.2⟩
      map_one' := Subtype.ext (map_one g)
      map_mul' := fun x y => Subtype.ext (map_mul g (x : Y) (y : Y)) }
  have hαinj : Function.Injective α := fun x y hxy =>
    Subtype.ext (g.injective (congrArg Subtype.val hxy))
  have hαbij : Function.Bijective α := Finite.injective_iff_bijective.mp hαinj
  let α' : C ≃* C := MulEquiv.ofBijective α hαbij
  have hα' : ∀ w : C, ((α' w : C) : Y) = g (w : Y) := fun w => rfl
  let β : MulAut (alternatingGroup (Fin 4)) := e.symm.trans (α'.trans e)
  have hβ' : ∀ w : C, β (e w) = e (α' w) := fun w => by simp [β]
  obtain ⟨σ, hσ⟩ := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_four_bijective_conj.2 β
  have hβσ : ∀ x : alternatingGroup (Fin 4),
      ((β x : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4)) = σ * x * σ⁻¹ := fun x => by
    rw [← hσ]
    exact MulAut.conjNormal_apply σ x
  have hsign : Equiv.Perm.sign σ = 1 := by
    refine a4_sign_eq_one σ fun x hx => ?_
    set x' : alternatingGroup (Fin 4) := ⟨x, Equiv.Perm.mem_alternatingGroup.mpr hx⟩ with hx'
    set z : C := e.symm x' with hz
    have h1 : ((z : Y)⁻¹ * g (z : Y)) ^ 2 = 1 := hg2 z z.2
    have h2 : (z⁻¹ * α' z) ^ 2 = 1 := by
      apply Subtype.ext
      simpa [hα'] using h1
    have h3 : (x'⁻¹ * β x') ^ 2 = 1 := by
      have := congrArg e h2
      rw [map_pow, map_mul, map_inv, hz, MulEquiv.apply_symm_apply, map_one] at this
      have h5 := hβ' z
      rw [hz, MulEquiv.apply_symm_apply] at h5
      rw [h5]
      exact this
    have h4 := congrArg (fun w : alternatingGroup (Fin 4) => (w : Equiv.Perm (Fin 4))) h3
    simpa [hβσ, hx'] using h4
  set c' : alternatingGroup (Fin 4) := ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩ with hc'
  have hβc : ∀ x : alternatingGroup (Fin 4), β x = c' * x * c'⁻¹ := fun x => by
    apply Subtype.ext
    rw [hβσ]
    simp [hc']
  refine ⟨(e.symm c' : Y), (e.symm c').2, fun x hx => ?_⟩
  have h1 : α' ⟨x, hx⟩ = e.symm c' * ⟨x, hx⟩ * (e.symm c')⁻¹ := by
    apply e.injective
    rw [← hβ', hβc]
    simp
  have h2 := congrArg Subtype.val h1
  rw [hα'] at h2
  simpa using h2

theorem IsA4Subgroup.of_equiv (e : C ≃* alternatingGroup (Fin 4)) : IsA4Subgroup C := by
  classical
  have hfin : Finite C := Finite.of_equiv _ e.symm.toEquiv
  have key : ∀ (x : Y) (hx : x ∈ C) (n : ℕ),
      (e ⟨x, hx⟩) ^ n = 1 ↔ x ^ n = 1 := fun x hx n => pow_eq_one_iff e ⟨x, hx⟩ n
  refine
    { card := by rw [Nat.card_congr e.toEquiv]; exact a4_card
      nonabelian := ?_
      mul_sq := ?_
      card_sq := ?_
      sq_or_cube := ?_
      comm_sq := ?_
      centralizer_sq := ?_
      fpf := ?_
      normal_gen := ?_
      aut_inner := ?_ }
  · obtain ⟨a, b, hab⟩ := a4_exists_noncomm
    refine ⟨(e.symm a : Y), (e.symm a).2, (e.symm b : Y), (e.symm b).2, fun h => hab ?_⟩
    have h' : e.symm a * e.symm b = e.symm b * e.symm a := Subtype.ext h
    simpa using congrArg e h'
  · intro x hx y hy hx2 hy2
    have := a4_mul_sq (e ⟨x, hx⟩) (e ⟨y, hy⟩) ((key x hx 2).mpr hx2) ((key y hy 2).mpr hy2)
    rw [← map_mul] at this
    exact (key (x * y) (C.mul_mem hx hy) 2).mp this
  · rw [← a4_card_sq]
    refine Nat.card_congr ?_
    exact
      { toFun := fun x => ⟨e ⟨x.1, x.2.1⟩, (key x.1 x.2.1 2).mpr x.2.2⟩
        invFun := fun w => ⟨(e.symm w.1 : Y), (e.symm w.1).2,
          (pow_eq_one_iff e (e.symm w.1) 2).mp (by rw [MulEquiv.apply_symm_apply]; exact w.2)⟩
        left_inv := fun x => by simp
        right_inv := fun w => by simp }
  · intro x hx
    rcases a4_sq_or_cube (e ⟨x, hx⟩) with h | h
    · exact Or.inl ((key x hx 2).mp h)
    · exact Or.inr ((key x hx 3).mp h)
  · intro x hx y hy
    have := a4_comm_sq (e ⟨x, hx⟩) (e ⟨y, hy⟩)
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at this
    have h2 := (pow_eq_one_iff e _ 2).mp this
    simpa using h2
  · intro x hx hcomm
    refine (key x hx 2).mp (a4_centralizer (e ⟨x, hx⟩) fun v hv => ?_)
    obtain ⟨w, rfl⟩ := e.surjective v
    have hw : (w : Y) ^ 2 = 1 := (pow_eq_one_iff e w 2).mp hv
    have := hcomm w w.2 hw
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext this)
  · intro x hx z hz hx2 hz2 hxz
    have hx2' : (e ⟨x, hx⟩) ^ 2 ≠ 1 := fun h => hx2 ((key x hx 2).mp h)
    have := a4_fpf (e ⟨x, hx⟩) (e ⟨z, hz⟩)
      ⟨hx2', (key z hz 2).mpr hz2, by
        rw [← map_mul, ← map_mul]
        exact congrArg e (Subtype.ext hxz)⟩
    have h1 : (⟨z, hz⟩ : C) = 1 := e.injective (by rw [this, map_one])
    simpa using congrArg Subtype.val h1
  · intro n hn hn1 v hv hv2
    have hn1' : e ⟨n, hn⟩ ≠ 1 := fun h => hn1 (by
      have : (⟨n, hn⟩ : C) = 1 := e.injective (by rw [h, map_one])
      simpa using congrArg Subtype.val this)
    obtain ⟨x', hx'⟩ := a4_normal_gen (e ⟨n, hn⟩) hn1' (e ⟨v, hv⟩) ((key v hv 2).mpr hv2)
    refine ⟨(e.symm x' : Y), (e.symm x').2, ?_⟩
    rcases hx' with h | h | h
    · left
      have : (⟨v, hv⟩ : C) = 1 := e.injective (by rw [h, map_one])
      simpa using congrArg Subtype.val this
    · right; left
      have : (⟨v, hv⟩ : C) = e.symm x' * ⟨n, hn⟩ * (e.symm x')⁻¹ :=
        e.injective (by rw [h]; simp)
      simpa using congrArg Subtype.val this
    · right; right
      have : (⟨v, hv⟩ : C) = e.symm x' * ⟨n, hn⟩ * (e.symm x')⁻¹ * ⟨n, hn⟩⁻¹ :=
        e.injective (by rw [h]; simp)
      simpa using congrArg Subtype.val this
  · exact fun g hgC hg2 => aut_inner_of_equiv e g hgC hg2

end OfEquiv

end CFSG.SignalizerFunctorTheorem.McBride.PSL2Three
