module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.Quasithin

namespace S153EN8

@[expose] def n8Rot4 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3

@[expose] def n8Ref4 : Equiv.Perm (Fin 4) := Equiv.swap 0 2

@[expose] def n8D8PermFun : DihedralGroup 4 → Equiv.Perm (Fin 4)
  | .r i => n8Rot4 ^ i.val
  | .sr i => n8Rot4 ^ (-i).val * n8Ref4

theorem n8D8PermFun_mul : ∀ x y : DihedralGroup 4,
    n8D8PermFun (x * y) = n8D8PermFun x * n8D8PermFun y := by
  decide +kernel

theorem n8D8PermFun_one : n8D8PermFun 1 = 1 := by decide +kernel

@[expose] def n8D8Perm : DihedralGroup 4 →* Equiv.Perm (Fin 4) where
  toFun := n8D8PermFun
  map_one' := n8D8PermFun_one
  map_mul' := n8D8PermFun_mul

theorem n8D8Perm_injective : Function.Injective n8D8Perm := by
  intro x y h
  revert x y
  decide +kernel

theorem n8_factorization_twentyFour : (24 : ℕ).factorization 2 = 3 := by
  have hprod : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
  rw [hprod, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬2 ∣ 3)]

theorem exists_dihedral_of_perm_four {R : Type*} [Group R] (hR : IsPGroup 2 R)
    (ψ : R →* Equiv.Perm (Fin 4)) (hψ : Function.Injective ψ) :
    ∃ f : R →* DihedralGroup 4, Function.Injective f := by
  obtain ⟨T, hT⟩ := (hR.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective).exists_le_sylow
  have hcard : Nat.card n8D8Perm.range = 2 ^ (Nat.card (Equiv.Perm (Fin 4))).factorization 2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective n8D8Perm_injective).toEquiv, DihedralGroup.nat_card,
      Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin,
      show Nat.factorial 4 = 24 from rfl, n8_factorization_twentyFour]
    rfl
  let H : Sylow 2 (Equiv.Perm (Fin 4)) := Sylow.ofCard n8D8Perm.range hcard
  let e : T ≃* H := Sylow.equiv T H
  let eD : n8D8Perm.range ≃* DihedralGroup 4 := (MonoidHom.ofInjective n8D8Perm_injective).symm
  exact ⟨eD.toMonoidHom.comp (e.toMonoidHom.comp ((Subgroup.inclusion hT).comp
      (MonoidHom.ofInjective hψ).toMonoidHom)),
    eD.injective.comp (e.injective.comp ((Subgroup.inclusion_injective hT).comp
      (MonoidHom.ofInjective hψ).injective))⟩

theorem nonempty_dihedral_of_perm_four {R : Type*} [Group R] (hR : IsPGroup 2 R)
    (hR8 : Nat.card R = 8) (ψ : R →* Equiv.Perm (Fin 4)) (hψ : Function.Injective ψ) :
    Nonempty (R ≃* DihedralGroup 4) := by
  obtain ⟨f, hf⟩ := exists_dihedral_of_perm_four hR ψ hψ
  have hbij : Function.Bijective f :=
    hf.bijective_of_nat_card_le (by rw [hR8, DihedralGroup.nat_card])
  exact ⟨MulEquiv.ofBijective f hbij⟩

end S153EN8

end CFSG.Quasithin
