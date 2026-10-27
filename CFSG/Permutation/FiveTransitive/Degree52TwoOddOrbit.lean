module

public import CFSG.Permutation.FiveTransitive.Degree52TwoOrbitPreserved

public section

namespace CFSG

namespace FiveTransitive.Degree52TwoOddOrbit

open MulAction

theorem stable
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (Q : Subgroup G) (x : X) (hO : Nat.card (orbit Q x) = 16)
    (hsmall : ∀ y : X, y ∉ orbit Q x → Nat.card (orbit Q y) ≤ 2)
    (g : Subgroup.normalizer (Q : Set G)) :
    ∀ y : X, g.val • y ∈ orbit Q x ↔ y ∈ orbit Q x := by
  let f := NormalizerOrbitHom.toPermHom (Y := X) Q g
  have hcard : Nat.card (orbit Q (g.val • x)) = 16 := by
    have hh := NormalizerLargeOrbit.card_orbit_eq Q g (Quotient.mk'' x)
    change Nat.card (orbit Q (g.val • x)) = Nat.card (orbit Q x) at hh
    exact hh.trans hO
  have hx : g.val • x ∈ orbit Q x := by
    by_contra hn
    have hh := hsmall _ hn
    omega
  have hfx : f (Quotient.mk'' x) = Quotient.mk'' x := Quotient.sound hx
  intro y
  constructor
  · intro hy
    exact Quotient.exact (f.injective ((Quotient.sound hy).trans hfx.symm))
  · intro hy
    exact Quotient.exact ((congrArg f (Quotient.sound hy)).trans hfx)

theorem exterior_fixed_mem
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X ≤ 52) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (x : X) (hsmall : ∀ y : X, y ∉ orbit Q x → Nat.card (orbit Q y) ≤ 2)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (hunique : ∀ y z : X, y ∉ fixedPoints Q X → z ∉ fixedPoints Q X →
      g.val • y = y → g.val • z = z → y = z)
    (y : X) (hy : y ∉ fixedPoints Q X) (hgy : g.val • y = y) : y ∈ orbit Q x := by
  classical
  let _ : Fintype X := Fintype.ofFinite X
  let O : orbitRel.Quotient Q X := Quotient.mk'' y
  have hne : Nat.card O.orbit ≠ 1 := by
    intro he
    apply hy
    apply mem_fixedPoints_iff_card_orbit_eq_one.mpr
    rw [←Nat.card_eq_fintype_card]
    exact he
  have hpres : NormalizerOrbitHom.toPermHom (Y := X) Q g O = O := by
    change Quotient.mk'' (g.val • y) = Quotient.mk'' y
    rw [hgy]
  have hsixteen : Nat.card (orbit Q y) = 16 :=
    Degree52TwoOrbitPreserved.preserved_card_eq_sixteen hX Q hQ g hg hunique O hne hpres
  by_contra hn
  have hh := hsmall y hn
  omega

end FiveTransitive.Degree52TwoOddOrbit

end CFSG
