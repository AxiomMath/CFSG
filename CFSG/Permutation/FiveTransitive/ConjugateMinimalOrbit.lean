module

public import CFSG.Permutation.FiveTransitive.MinimalOrbitStabilizer

public section

namespace CFSG

namespace FiveTransitive.ConjugateMinimalOrbit

open MulAction

private theorem mem_orbit_equivariant
    {G H X Y : Type*} [Group G] [Group H] [MulAction G X] [MulAction H Y]
    (φ : G ≃* H) (e : X ≃ Y) (he : ∀ (g:G) (x:X), e (g • x)=φ g • e x)
    (x y : X) : y ∈ orbit G x ↔ e y ∈ orbit H (e x) := by
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨φ g,(he g x).symm⟩
  · rintro ⟨h,hh⟩
    refine ⟨φ.symm h,e.injective ?_⟩
    rw [he,φ.apply_symm_apply]
    exact hh

theorem card_orbit_equivariant
    {G H X Y : Type*} [Group G] [Group H] [MulAction G X] [MulAction H Y]
    (φ : G ≃* H) (e : X ≃ Y) (he : ∀ (g:G) (x:X), e (g • x)=φ g • e x)
    (x : X) : Nat.card (orbit G x)=Nat.card (orbit H (e x)) :=
  Nat.card_congr (Equiv.subtypeEquiv e (fun y=>mem_orbit_equivariant φ e he x y))

theorem fixedPoints_equivariant
    {G H X Y : Type*} [Group G] [Group H] [MulAction G X] [MulAction H Y]
    (φ : G ≃* H) (e : X ≃ Y) (he : ∀ (g:G) (x:X), e (g • x)=φ g • e x)
    (x : X) : x ∈ fixedPoints G X ↔ e x ∈ fixedPoints H Y := by
  constructor
  · intro hx
    rw [mem_fixedPoints]
    intro h
    calc
      h • e x = e (φ.symm h • x) := by rw [he,φ.apply_symm_apply]
      _ = e x := congrArg e (mem_fixedPoints.mp hx (φ.symm h))
  · intro hx
    rw [mem_fixedPoints]
    intro g
    apply e.injective
    rw [he]
    exact mem_fixedPoints.mp hx (φ g)

private theorem minimal_orbit_equivariant
    {G H X Y : Type*} [Group G] [Group H] [MulAction G X] [MulAction H Y]
    (φ : G ≃* H) (e : X ≃ Y) (he : ∀ (g:G) (x:X), e (g • x)=φ g • e x)
    (t : X) (hmin : ∀ y : X, y ∉ fixedPoints G X → Nat.card (orbit G t) ≤ Nat.card (orbit G y)) :
    ∀ y : Y, y ∉ fixedPoints H Y → Nat.card (orbit H (e t)) ≤ Nat.card (orbit H y) := by
  intro y hy
  have hy' : e.symm y ∉ fixedPoints G X := by
    intro h
    exact hy (by simpa using (fixedPoints_equivariant φ e he _).mp h)
  have h := hmin (e.symm y) hy'
  simpa only [card_orbit_equivariant φ e he, e.apply_symm_apply] using h

@[expose] abbrev conjugateSubgroup {G : Type*} [Group G] (P : Subgroup G) (a : G) :=
  P.map (MulAut.conj a).toMonoidHom

noncomputable def conjugateEquiv {G : Type*} [Group G] (P : Subgroup G) (a : G) :
    P ≃* conjugateSubgroup P a :=
  P.equivMapOfInjective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective

theorem conjugate_equivariant
    {G X : Type*} [Group G] [MulAction G X] (P : Subgroup G) (a : G)
    (p : P) (x : X) :
    (MulAction.toPerm a) (p • x) = conjugateEquiv P a p • (MulAction.toPerm a) x := by
  change a • ((p:G) • x) = (a * (p:G) * a⁻¹) • (a • x)
  simp only [mul_smul,inv_smul_smul]

theorem minimal_orbit_conjugate
    {G X : Type*} [Group G] [MulAction G X] (P : Subgroup G) (a : G)
    (t : X) (hmin : ∀ y : X, y ∉ fixedPoints P X → Nat.card (orbit P t) ≤ Nat.card (orbit P y)) :
    ∀ y : X, y ∉ fixedPoints (conjugateSubgroup P a) X →
      Nat.card (orbit (conjugateSubgroup P a) (a • t)) ≤ Nat.card (orbit (conjugateSubgroup P a) y) :=
  minimal_orbit_equivariant (conjugateEquiv P a) (MulAction.toPerm a) (conjugate_equivariant P a) t hmin

theorem card_stabilizer_conjugate
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (P : Subgroup G) (a : G) (t : X) :
    Nat.card (stabilizer P t)=Nat.card (stabilizer (conjugateSubgroup P a) (a • t)) := by
  have he := card_orbit_equivariant (conjugateEquiv P a) (MulAction.toPerm a)
    (conjugate_equivariant P a) t
  change Nat.card (orbit P t)=Nat.card (orbit (conjugateSubgroup P a) (a • t)) at he
  have ht := MinimalOrbitStabilizer.nat_card_orbit_mul_stabilizer P X t
  have hs := MinimalOrbitStabilizer.nat_card_orbit_mul_stabilizer (conjugateSubgroup P a) X (a • t)
  have hg := Nat.card_congr (conjugateEquiv P a).toEquiv
  have : Nonempty (orbit P t) := ⟨⟨t,mem_orbit_self t⟩⟩
  apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card (orbit P t) from Nat.card_pos)
  rw [ht,he,hs,hg]

end FiveTransitive.ConjugateMinimalOrbit

end CFSG
