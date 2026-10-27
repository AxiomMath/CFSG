module

public import CFSG.Permutation.FiveTransitive.TwoGroupQuadCommutatorImage
public import CFSG.Permutation.FiveTransitive.TwoPointActionCommutator

public section

namespace CFSG

namespace FiveTransitive.TwoGroupQuadCommutatorOrbit

open MulAction

private theorem orbit_card_le_map_card
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (A : Subgroup G) (x : X) :
    Nat.card (orbit A x) ≤ Nat.card (A.map (toPermHom G (orbit G x))) := by
  classical
  let Y := orbit G x
  let xY : Y := ⟨x,mem_orbit_self x⟩
  let rho := toPermHom G Y
  let J := A.map rho
  let ev : J → orbit A x := fun j => ⟨(j.val xY).val,by
    obtain ⟨g,hg,hgj⟩ := j.property
    rw [← hgj]
    exact mem_orbit_iff.mpr ⟨⟨g,hg⟩,rfl⟩⟩
  have hev : Function.Surjective ev := by
    rintro ⟨y,hy⟩
    obtain ⟨g,hg⟩ := mem_orbit_iff.mp hy
    refine ⟨⟨rho g.val,⟨g.val,g.property,rfl⟩⟩,?_⟩
    apply Subtype.ext
    exact hg
  exact Nat.card_le_card_of_surjective ev hev

private theorem commutator_orbit_card_le_two
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (hG : IsPGroup 2 G) (x : X) (hsmall : Nat.card (orbit G x) ≤ 4) :
    Nat.card (orbit (commutator G) x) ≤ 2 := by
  exact (orbit_card_le_map_card (commutator G) x).trans
    (TwoGroupQuadCommutatorImage.map_commutator_card_le_two hG
      (toPermHom G (orbit G x)) hsmall)

theorem commutator_fixes_small_orbit
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (x : X) (hsmall : Nat.card (orbit G x) ≤ 2)
    (g : G) (hg : g ∈ commutator G) (y : X) (hy : y ∈ orbit G x) :
    g • y = y := by
  have he := TwoPointActionCommutator.apply_eq_one (toPermHom G (orbit G x)) hsmall g hg
  exact congrArg (fun f : Equiv.Perm (orbit G x) => (f ⟨y,hy⟩).val) he

theorem all_commutator_orbits_le_two
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (hG : IsPGroup 2 G) (horbits : ∀ x : X, Nat.card (orbit G x) ≤ 4) :
    ∀ x : X, Nat.card (orbit (commutator G) x) ≤ 2 := by
  intro x
  exact commutator_orbit_card_le_two hG x (horbits x)

end FiveTransitive.TwoGroupQuadCommutatorOrbit

end CFSG
