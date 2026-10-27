module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG

namespace FiveTransitive.FreeActionTransporterCount

open MulAction
open scoped BigOperators

theorem smul_injective
    {H Y : Type*} [Group H] [MulAction H Y]
    (hfree : ∀ (h : H) (y : Y), h • y = y → h = 1) (y : Y) :
    Function.Injective (fun h : H => h • y) := by
  intro h k he
  change h • y = k • y at he
  have hh : (k⁻¹ * h) • y = y := by rw [mul_smul, he, inv_smul_smul]
  exact (inv_mul_eq_one.mp (hfree _ _ hh)).symm

theorem sum_card_transporter
    {H Y : Type*} [Group H] [Fintype H] [Finite Y] [MulAction H Y]
    (hfree : ∀ (h : H) (y : Y), h • y = y → h = 1) (f : Y → Y) :
    (∑ h : H, Nat.card {y : Y // h • f y = y}) =
      Nat.card {y : Y // ∃ h : H, h • f y = y} := by
  let forget : (Σ h : H, {y : Y // h • f y = y}) →
      {y : Y // ∃ h : H, h • f y = y} := fun p => ⟨p.2.val, p.1, p.2.property⟩
  have hf : Function.Bijective forget := by
    constructor
    · rintro ⟨h, y, hy⟩ ⟨k, z, hz⟩ he
      have hyz : y = z := congrArg Subtype.val he
      subst z
      have hhk : h = k := smul_injective hfree (f y) (hy.trans hz.symm)
      subst k
      rfl
    · rintro ⟨y, h, hy⟩
      exact ⟨⟨h, ⟨y, hy⟩⟩, rfl⟩
  rw [← Nat.card_sigma]
  exact Nat.card_congr (Equiv.ofBijective forget hf)

private theorem card_orbit_fiber
    {H Y : Type*} [Group H] [MulAction H Y]
    (hfree : ∀ (h : H) (y : Y), h • y = y → h = 1)
    (O : orbitRel.Quotient H Y) :
    Nat.card {y : Y // (Quotient.mk'' y : orbitRel.Quotient H Y) = O} = Nat.card H := by
  let f : H → {y : Y // (Quotient.mk'' y : orbitRel.Quotient H Y) = O} :=
    fun h => ⟨h • O.out, orbitRel.Quotient.quotient_smul_eq.trans (Quotient.out_eq O)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro h k he
      exact smul_injective hfree O.out (congrArg Subtype.val he)
    · intro y
      have hy : y.val ∈ orbit H O.out :=
        Quotient.exact (y.property.trans (Quotient.out_eq O).symm)
      obtain ⟨h, hh⟩ := mem_orbit_iff.mp hy
      exact ⟨h, Subtype.ext hh⟩
  exact Nat.card_congr (Equiv.ofBijective f hf).symm

theorem card_orbit_preimage
    {H Y : Type*} [Group H] [Finite H] [Finite Y] [MulAction H Y]
    (hfree : ∀ (h : H) (y : Y), h • y = y → h = 1)
    (P : orbitRel.Quotient H Y → Prop) :
    Nat.card {y : Y // P (Quotient.mk'' y)} =
      Nat.card H * Nat.card {O : orbitRel.Quotient H Y // P O} := by
  classical
  let _ : Fintype {O : orbitRel.Quotient H Y // P O} := Fintype.ofFinite _
  have he := Nat.card_congr (Equiv.sigmaSubtypeFiberEquivSubtype
    (fun y : Y => (Quotient.mk'' y : orbitRel.Quotient H Y)) (fun _ => Iff.rfl (a := P _)))
  rw [← he, Nat.card_sigma]
  simp_rw [card_orbit_fiber hfree]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card, Nat.mul_comm]

end FiveTransitive.FreeActionTransporterCount

end CFSG
