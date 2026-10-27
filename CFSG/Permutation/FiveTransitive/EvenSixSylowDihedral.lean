module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

namespace FiveTransitive.EvenSixSylowDihedral

open Equiv

private def dihedralPerm (d : DihedralGroup 4) : Perm (Fin 6) :=
  let r : Perm (Fin 6) := swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5
  let t : Perm (Fin 6) := swap 0 2 * swap 4 5
  match d with
  | .r i => r ^ i.val
  | .sr i => t * r ^ i.val

private theorem dihedralPerm_one : dihedralPerm 1 = 1 := by decide +kernel
private theorem dihedralPerm_mul : ∀ x y, dihedralPerm (x * y) = dihedralPerm x * dihedralPerm y := by
  decide +kernel
private theorem dihedralPerm_even : ∀ x, (dihedralPerm x).sign = 1 := by decide +kernel
private theorem dihedralPerm_injective : Function.Injective dihedralPerm := by decide +kernel

private theorem dihedral_cases : ∀ a x : DihedralGroup 4, a ^ 2 ≠ 1 →
    x ^ 2 = 1 ∨ x = a ∨ x = a⁻¹ := by decide +kernel

private noncomputable def dihedralHom (X : Type*) [Fintype X] [DecidableEq X] (hX : Fintype.card X = 6) :
    DihedralGroup 4 →* alternatingGroup X :=
  let e := (Fintype.equivFinOfCardEq hX).symm
  let f : DihedralGroup 4 →* Perm (Fin 6) :=
    { toFun := dihedralPerm, map_one' := dihedralPerm_one, map_mul' := dihedralPerm_mul }
  { toFun := fun x => ⟨e.permCongrHom (f x), Perm.mem_alternatingGroup.mpr
      ((Perm.sign_permCongr e (f x)).trans (dihedralPerm_even x))⟩
    map_one' := Subtype.ext (by change e.permCongrHom (f 1) = 1; rw [map_one, map_one])
    map_mul' := fun x y => Subtype.ext (by
      change e.permCongrHom (f (x * y)) = e.permCongrHom (f x) * e.permCongrHom (f y)
      rw [map_mul, map_mul]) }

private theorem dihedralHom_injective
    (X : Type*) [Fintype X] [DecidableEq X] (hX : Fintype.card X = 6) :
    Function.Injective (dihedralHom X hX) := by
  intro x y h
  apply dihedralPerm_injective
  apply (Fintype.equivFinOfCardEq hX).symm.permCongrHom.injective
  exact congrArg Subtype.val h

theorem nonempty_equiv_dihedral
    (X : Type*) [Fintype X] [DecidableEq X] (hX : Fintype.card X = 6)
    (P : Sylow 2 (alternatingGroup X)) : Nonempty (P ≃* DihedralGroup 4) := by
  let _ : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let f := dihedralHom X hX
  let e := MonoidHom.ofInjective (dihedralHom_injective X hX)
  have hD : Nat.card f.range = 8 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
  have hA : Nat.card (alternatingGroup X) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, hX]
    norm_num [Nat.factorial]
  have hi : f.range.index = 45 := by
    have h := f.range.card_mul_index
    rw [hD, hA] at h
    omega
  have hp : IsPGroup 2 f.range := IsPGroup.of_card (n := 3) (hD.trans (by norm_num))
  let D : Sylow 2 (alternatingGroup X) := hp.toSylow (by rw [hi]; norm_num)
  exact ⟨(P.equiv D).trans e.symm⟩

theorem square_eq_one_or_eq_or_eq_inv
    (X : Type*) [Fintype X] [DecidableEq X] (hX : Fintype.card X = 6)
    (P : Sylow 2 (alternatingGroup X)) (a x : P) (ha : orderOf a = 4) :
    x ^ 2 = 1 ∨ x = a ∨ x = a⁻¹ := by
  obtain ⟨e⟩ := nonempty_equiv_dihedral X hX P
  have hea : orderOf (e a) = 4 := (orderOf_injective e.toMonoidHom e.injective a).trans ha
  have hne : (e a) ^ 2 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hea] at hd
    norm_num at hd
  rcases dihedral_cases (e a) (e x) hne with hx | hx | hx
  · left
    apply e.injective
    simpa only [map_pow, map_one] using hx
  · exact Or.inr (Or.inl (e.injective hx))
  · right; right
    apply e.injective
    simpa only [map_inv] using hx

end FiveTransitive.EvenSixSylowDihedral

end CFSG
