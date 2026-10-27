module

public import CFSG.Monster.B.Classical.UnitarySixClass

public noncomputable section

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Classical.UnitarySix

variable {S V : Type*} [Group S] (act : S →* Equiv.Perm V) (lab : V → S) (Y : Set V)

@[expose] def sliceGroup : Subgroup S := Subgroup.closure (lab '' Y)

@[expose] def sliceGraph : SimpleGraph V where
  Adj y z := y ∈ Y ∧ z ∈ Y ∧ y ≠ z ∧ Commute (lab y) (lab z)
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2.2.1 rfl⟩

theorem sliceGraph_adj {y z : V} :
    (sliceGraph lab Y).Adj y z ↔ y ∈ Y ∧ z ∈ Y ∧ y ≠ z ∧ Commute (lab y) (lab z) := Iff.rfl

@[expose] def actStab (x : V) : Subgroup S where
  carrier := {a | act a x = x}
  mul_mem' {a b} ha hb := by
    change act (a * b) x = x
    rw [map_mul, Equiv.Perm.mul_apply, show act b x = x from hb, show act a x = x from ha]
  one_mem' := by
    change act 1 x = x
    rw [map_one, Equiv.Perm.one_apply]
  inv_mem' {a} ha := by
    change act a⁻¹ x = x
    rw [map_inv, Equiv.Perm.inv_eq_iff_eq]
    exact (show act a x = x from ha).symm

theorem mem_actStab {x : V} {a : S} : a ∈ actStab act x ↔ act a x = x := Iff.rfl

@[expose] def sliceStab (u : V) : Subgroup S := sliceGroup lab Y ⊓ actStab act u

theorem mem_sliceStab {u : V} {a : S} :
    a ∈ sliceStab act lab Y u ↔ a ∈ sliceGroup lab Y ∧ act a u = u := Iff.rfl

@[expose] def setStab (C : Set V) : Subgroup S where
  carrier := {a | a ∈ sliceGroup lab Y ∧ ∀ x, act a x ∈ C ↔ x ∈ C}
  mul_mem' {a b} ha hb := ⟨(sliceGroup lab Y).mul_mem ha.1 hb.1, fun x => by
    rw [map_mul, Equiv.Perm.mul_apply, ha.2, hb.2]⟩
  one_mem' := ⟨(sliceGroup lab Y).one_mem, fun x => by rw [map_one, Equiv.Perm.one_apply]⟩
  inv_mem' {a} ha := ⟨(sliceGroup lab Y).inv_mem ha.1, fun x => by
    rw [← ha.2, map_inv, Equiv.Perm.coe_inv, Equiv.apply_symm_apply]⟩

theorem mem_setStab {C : Set V} {a : S} :
    a ∈ setStab act lab Y C ↔ a ∈ sliceGroup lab Y ∧ ∀ x, act a x ∈ C ↔ x ∈ C := Iff.rfl

@[expose] def ptStab (C : Set V) : Subgroup S where
  carrier := {a | a ∈ sliceGroup lab Y ∧ ∀ x ∈ C, act a x = x}
  mul_mem' {a b} ha hb := ⟨(sliceGroup lab Y).mul_mem ha.1 hb.1, fun x hx => by
    rw [map_mul, Equiv.Perm.mul_apply, hb.2 x hx, ha.2 x hx]⟩
  one_mem' := ⟨(sliceGroup lab Y).one_mem, fun x _ => by rw [map_one, Equiv.Perm.one_apply]⟩
  inv_mem' {a} ha := ⟨(sliceGroup lab Y).inv_mem ha.1, fun x hx => by
    rw [map_inv, Equiv.Perm.inv_eq_iff_eq, ha.2 x hx]⟩

theorem mem_ptStab {C : Set V} {a : S} :
    a ∈ ptStab act lab Y C ↔ a ∈ sliceGroup lab Y ∧ ∀ x ∈ C, act a x = x := Iff.rfl

@[expose] def setStabPerm (C : Set V) : setStab act lab Y C →* Equiv.Perm C where
  toFun a := (act (a : S)).subtypePerm fun x => a.2.2 x
  map_one' := Equiv.ext fun x => Subtype.ext (by
    change act (1 : S) x = x
    rw [map_one, Equiv.Perm.one_apply])
  map_mul' a b := Equiv.ext fun x => Subtype.ext (by
    change act ((a : S) * b) x = act (a : S) (act (b : S) x)
    rw [map_mul, Equiv.Perm.mul_apply])

theorem setStabPerm_apply (C : Set V) (a : setStab act lab Y C) (x : C) :
    ((setStabPerm act lab Y C a x : C) : V) = act (a : S) x := rfl

@[expose] def IsSliceMaxClique (C : Set V) : Prop :=
  Maximal (fun D : Set V => D ⊆ Y ∧ (sliceGraph lab Y).IsClique D) C

@[expose] def slicePerm (hmaps : ∀ a ∈ sliceGroup lab Y, ∀ y ∈ Y, act a y ∈ Y) :
    sliceGroup lab Y →* Equiv.Perm Y where
  toFun a := (act (a : S)).subtypePerm fun y => ⟨fun h => by
      have h' := hmaps _ ((sliceGroup lab Y).inv_mem a.2) _ h
      rwa [map_inv, Equiv.Perm.coe_inv, Equiv.symm_apply_apply] at h', fun h => hmaps _ a.2 y h⟩
  map_one' := Equiv.ext fun x => Subtype.ext (by
    change act (1 : S) x = x
    rw [map_one, Equiv.Perm.one_apply])
  map_mul' a b := Equiv.ext fun x => Subtype.ext (by
    change act ((a : S) * b) x = act (a : S) (act (b : S) x)
    rw [map_mul, Equiv.Perm.mul_apply])

theorem slicePerm_apply (hmaps : ∀ a ∈ sliceGroup lab Y, ∀ y ∈ Y, act a y ∈ Y)
    (a : sliceGroup lab Y) (y : Y) : ((slicePerm act lab Y hmaps a y : Y) : V) = act (a : S) y :=
  rfl

structure IsFischerSlice : Prop where
  lab_act : ∀ (a : S) (x : V), lab (act a x) = a * lab x * a⁻¹
  finite : Y.Finite
  ncard : Y.ncard = 3510
  injOn : Set.InjOn lab Y
  orderOf_lab : ∀ y ∈ Y, orderOf (lab y) = 2
  orderOf_mul : ∀ y ∈ Y, ∀ z ∈ Y, ¬Commute (lab y) (lab z) → orderOf (lab y * lab z) = 3
  mapsTo : ∀ a ∈ sliceGroup lab Y, ∀ y ∈ Y, act a y ∈ Y
  faithful : ∀ a ∈ sliceGroup lab Y, (∀ y ∈ Y, act a y = y) → a = 1
  transitive : ∀ y ∈ Y, ∀ z ∈ Y, ∃ a ∈ sliceGroup lab Y, act a y = z
  valency : ∀ y ∈ Y, ((sliceGraph lab Y).neighborSet y).ncard = 693
  lambda : ∀ y z, (sliceGraph lab Y).Adj y z →
    ((sliceGraph lab Y).commonNeighbors y z).ncard = 180
  mu : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → ¬(sliceGraph lab Y).Adj y z →
    ((sliceGraph lab Y).commonNeighbors y z).ncard = 126
  local_unitary : ∀ u ∈ Y, ∃ (τ : (sliceGraph lab Y).neighborSet u ≃ IsoPt)
    (φ : sliceStab act lab Y u →* ProjSU),
    Function.Surjective φ ∧
    (∀ a : sliceStab act lab Y u, φ a = 1 ↔ (a : S) ∈ Subgroup.zpowers (lab u)) ∧
    (∀ (z : (sliceGraph lab Y).neighborSet u) (a : sliceStab act lab Y u),
      (a : S) = lab z → φ a = tPt (τ z)) ∧
    ∀ (a : sliceStab act lab Y u) (z z' : (sliceGraph lab Y).neighborSet u),
      (z' : V) = act (a : S) z → τ z' = projAct (φ a) (τ z)

structure LocalChart (u : V) where
  τ : (sliceGraph lab Y).neighborSet u ≃ IsoPt
  φ : sliceStab act lab Y u →* ProjSU
  surj : Function.Surjective φ
  ker : ∀ a : sliceStab act lab Y u, φ a = 1 ↔ (a : S) ∈ Subgroup.zpowers (lab u)
  lab_eq : ∀ (z : (sliceGraph lab Y).neighborSet u) (a : sliceStab act lab Y u),
    (a : S) = lab z → φ a = tPt (τ z)
  equivariant : ∀ (a : sliceStab act lab Y u) (z z' : (sliceGraph lab Y).neighborSet u),
    (z' : V) = act (a : S) z → τ z' = projAct (φ a) (τ z)

variable {act lab Y}

theorem mem_of_mem_neighborSet {u z : V} (hz : z ∈ (sliceGraph lab Y).neighborSet u) :
    z ∈ Y :=
  hz.2.1

theorem mem_of_adj {y z : V} (h : (sliceGraph lab Y).Adj y z) : y ∈ Y := h.1

theorem lab_mem_sliceGroup {y : V} (hy : y ∈ Y) : lab y ∈ sliceGroup lab Y :=
  Subgroup.subset_closure ⟨y, hy, rfl⟩

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem nonempty_localChart {u : V} (hu : u ∈ Y) : Nonempty (LocalChart act lab Y u) := by
  obtain ⟨τ, φ, h1, h2, h3, h4⟩ := hS.local_unitary u hu
  exact ⟨⟨τ, φ, h1, h2, h3, h4⟩⟩

theorem act_lab_eq_iff {y z : V} (hy : y ∈ Y) (hz : z ∈ Y) :
    act (lab y) z = z ↔ Commute (lab y) (lab z) := by
  constructor
  · intro h
    have h1 := hS.lab_act (lab y) z
    rw [h] at h1
    rw [Commute, SemiconjBy]
    calc lab y * lab z = lab y * lab z * (lab y)⁻¹ * lab y := by group
      _ = lab z * lab y := by rw [← h1]
  · intro h
    refine hS.injOn (hS.mapsTo _ (lab_mem_sliceGroup hy) z hz) hz ?_
    rw [hS.lab_act, h.eq, mul_inv_cancel_right]

theorem lab_mem_sliceStab {u z : V} (hu : u ∈ Y) (hz : z ∈ Y)
    (h : Commute (lab z) (lab u)) : lab z ∈ sliceStab act lab Y u :=
  ⟨lab_mem_sliceGroup hz, (hS.act_lab_eq_iff hz hu).2 h⟩

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
