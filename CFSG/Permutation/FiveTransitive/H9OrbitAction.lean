module

public import CFSG.Permutation.FiveTransitive.NormalizerOrbitHom

public section

namespace CFSG

namespace FiveTransitive.H9OrbitAction
open MulAction

@[expose] def toPermHom
    {G H X : Type*} [Group G] [Group H] [MulAction G X]
    (Q : Subgroup G) (i : H →* Subgroup.normalizer (Q : Set G))
    (O : orbitRel.Quotient Q X)
    (hInv : ∀ h : H, NormalizerOrbitHom.toPermHom (Y := X) Q (i h) O = O) :
    H →* Equiv.Perm O.orbit where
  toFun h := (MulAction.toPerm (i h).val).subtypePerm (by
    intro x
    let p := NormalizerOrbitHom.toPermHom (Y := X) Q (i h)
    simp only [orbitRel.Quotient.mem_orbit]
    change p (Quotient.mk'' x) = O ↔ Quotient.mk'' x = O
    exact ⟨fun he => p.injective (he.trans (hInv h).symm),
      fun he => (congrArg p he).trans (hInv h)⟩)
  map_one' := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change (i 1).val • x.val = x.val
    rw [map_one,Subgroup.coe_one,one_smul]
  map_mul' h k := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change (i (h*k)).val • x.val = (i h).val • ((i k).val • x.val)
    rw [map_mul,Subgroup.coe_mul,mul_smul]

theorem invariant_of_fixed_point
    {G H X : Type*} [Group G] [Group H] [MulAction G X]
    (Q : Subgroup G) (i : H →* Subgroup.normalizer (Q : Set G))
    (O : orbitRel.Quotient Q X) (x : X) (hx : x ∈ O.orbit)
    (hfix : ∀ h : H, (i h).val • x = x) :
    ∀ h : H, NormalizerOrbitHom.toPermHom (Y := X) Q (i h) O = O := by
  intro h
  have he : (Quotient.mk'' x : orbitRel.Quotient Q X) = O := orbitRel.Quotient.mem_orbit.mp hx
  rw [← he]
  change Quotient.mk'' ((i h).val • x) = Quotient.mk'' x
  rw [hfix]

end FiveTransitive.H9OrbitAction

end CFSG
