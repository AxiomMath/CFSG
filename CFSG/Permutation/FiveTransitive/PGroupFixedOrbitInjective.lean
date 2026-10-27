module

public import CFSG.Permutation.FiveTransitive.SylowThreeFixedOrbits

public section

namespace CFSG

namespace FiveTransitive.PGroupFixedOrbitInjective

open MulAction

theorem fixed_orbit_surjective
    {G X:Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (S:Subgroup G) (hS:IsPGroup 2 S)
    (hpoint:∀x:X,∃T:Sylow 2 G,x∈fixedPoints T X) :
    Function.Surjective (fun x:fixedPoints S X => (Quotient.mk'' x.val:orbitRel.Quotient G X)) := by
  intro o
  let O := SylowThreeFixedOrbits.orbitAction S o.out
  obtain ⟨T,hT⟩ := hpoint o.out
  have hodd := SylowThreeFixedOrbits.odd_orbit_of_sylow_fixed o.out T hT
  have hmod := hS.card_modEq_card_fixedPoints O
  have hnonzero:Nat.card (fixedPoints S O)≠0 := by
    intro he
    change Nat.card (orbit G o.out) % 2=Nat.card (fixedPoints S O) % 2 at hmod
    rw [he,Nat.zero_mod] at hmod
    exact hodd (Nat.dvd_of_mod_eq_zero hmod)
  obtain ⟨z⟩ : Nonempty (fixedPoints S O) := Finite.card_pos_iff.mp (Nat.pos_of_ne_zero hnonzero)
  let x:fixedPoints S X := ⟨z.val.val,mem_fixedPoints.mpr fun s =>
    congrArg Subtype.val (mem_fixedPoints.mp z.property s)⟩
  refine ⟨x,?_⟩
  exact (Quotient.sound (orbitRel_apply.mpr z.val.property)).trans (Quotient.out_eq o)

theorem fixed_orbit_injective
    {G X:Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (S:Subgroup G) (hS:IsPGroup 2 S)
    (hpoint:∀x:X,∃T:Sylow 2 G,x∈fixedPoints T X)
    (hcard:Nat.card (fixedPoints S X)=Nat.card (orbitRel.Quotient G X)) :
    Function.Injective (fun x:fixedPoints S X => (Quotient.mk'' x.val:orbitRel.Quotient G X)) := by
  classical
  let _ := Fintype.ofFinite (fixedPoints S X)
  let _ := Fintype.ofFinite (orbitRel.Quotient G X)
  apply (Fintype.bijective_iff_surjective_and_card _).mpr ?_ |>.injective
  exact ⟨fixed_orbit_surjective S hS hpoint,by simpa only [Nat.card_eq_fintype_card] using hcard⟩

end FiveTransitive.PGroupFixedOrbitInjective

end CFSG
