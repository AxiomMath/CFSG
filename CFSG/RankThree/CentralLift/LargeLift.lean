module

public import CFSG.RankThree.CentralLift.LinearTwoLifting
public import CFSG.LieType.CentralExt.SL2Lift

public section

namespace CFSG.RankThree.CentralLift

open Matrix CFSG.LieType.CentralExt

structure IsLargeCentralExt {E G : Type*} [Group E] [Group G] (π : E →* G) : Prop where
  surj : Function.Surjective π
  cen : π.ker ≤ Subgroup.center E
  large : ∃ p : ℕ, p.Prime ∧ 3 < p ∧ IsPGroup p π.ker

variable {k : Type} [Field k] [Finite k] {E G : Type*} [Group E] [Group G] [Finite E]
  {π : E →* G}

theorem existsUnique_lift_large (hk : ringChar k ≠ 2) (hπ : IsLargeCentralExt π)
    (α : SpecialLinearGroup (Fin 2) k →* G) :
    ∃! β : SpecialLinearGroup (Fin 2) k →* E, π.comp β = α := by
  have : Fintype k := Fintype.ofFinite k
  have : Finite G := Finite.of_surjective π hπ.surj
  obtain ⟨p, hp, hp3, hpk⟩ := hπ.large
  obtain ⟨f, hℓ, hcard⟩ := FiniteField.card k (ringChar k)
  have hk' : Nat.card k = ringChar k ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard]
  have hodd : Odd (ringChar k) := hℓ.odd_of_ne_two hk
  exact (odd_field_linear_two_central_large_prime_homomorphism_lifting hp hp3 hℓ hodd f.pos hk'
    π hπ.surj hπ.cen hpk α).1

theorem comp_sl2Lift_large (hk : ringChar k ≠ 2) (hπ : IsLargeCentralExt π)
    (α : SpecialLinearGroup (Fin 2) k →* G) : π.comp (sl2Lift π α) = α :=
  comp_sl2Lift_of_exists (existsUnique_lift_large hk hπ α).exists

theorem map_sl2Lift_large (hk : ringChar k ≠ 2) (hπ : IsLargeCentralExt π)
    (α : SpecialLinearGroup (Fin 2) k →* G) (g : SpecialLinearGroup (Fin 2) k) :
    π (sl2Lift π α g) = α g :=
  DFunLike.congr_fun (comp_sl2Lift_large hk hπ α) g

theorem eq_sl2Lift_large (hk : ringChar k ≠ 2) (hπ : IsLargeCentralExt π)
    {α : SpecialLinearGroup (Fin 2) k →* G} {β : SpecialLinearGroup (Fin 2) k →* E}
    (hβ : π.comp β = α) : β = sl2Lift π α :=
  (existsUnique_lift_large hk hπ α).unique hβ (comp_sl2Lift_large hk hπ α)

theorem sl2Lift_injective_large (hk : ringChar k ≠ 2) (hπ : IsLargeCentralExt π)
    {α : SpecialLinearGroup (Fin 2) k →* G} (hα : Function.Injective α) :
    Function.Injective (sl2Lift π α) := by
  intro g g' h
  apply hα
  rw [← map_sl2Lift_large hk hπ α, ← map_sl2Lift_large hk hπ α, h]

theorem conj_sl2Lift_large (hk : ringChar k ≠ 2) (hπ : IsLargeCentralExt π)
    (α : SpecialLinearGroup (Fin 2) k →* G) (e : E) :
    (MulAut.conj e).toMonoidHom.comp (sl2Lift π α) =
      sl2Lift π ((MulAut.conj (π e)).toMonoidHom.comp α) := by
  apply eq_sl2Lift_large hk hπ
  ext g
  change π (e * sl2Lift π α g * e⁻¹) = π e * α g * (π e)⁻¹
  rw [map_mul, map_mul, map_inv, map_sl2Lift_large hk hπ α g]

theorem conj_sl2Lift_apply_large (hk : ringChar k ≠ 2) (hπ : IsLargeCentralExt π)
    (α : SpecialLinearGroup (Fin 2) k →* G) (e : E) (g : SpecialLinearGroup (Fin 2) k) :
    e * sl2Lift π α g * e⁻¹ = sl2Lift π ((MulAut.conj (π e)).toMonoidHom.comp α) g :=
  DFunLike.congr_fun (conj_sl2Lift_large hk hπ α e) g

variable {k' : Type} [Field k'] [Finite k']

theorem sl2Lift_comp_large (hk : ringChar k ≠ 2) (hk' : ringChar k' ≠ 2)
    (hπ : IsLargeCentralExt π) (α : SpecialLinearGroup (Fin 2) k →* G)
    (β : SpecialLinearGroup (Fin 2) k' →* SpecialLinearGroup (Fin 2) k) :
    (sl2Lift π α).comp β = sl2Lift π (α.comp β) := by
  apply eq_sl2Lift_large hk' hπ
  rw [← MonoidHom.comp_assoc, comp_sl2Lift_large hk hπ α]

theorem commute_sl2Lift_large (hk : ringChar k ≠ 2) (hk' : ringChar k' ≠ 2)
    (hπ : IsLargeCentralExt π) (α : SpecialLinearGroup (Fin 2) k →* G)
    (α' : SpecialLinearGroup (Fin 2) k' →* G) (hαα' : ∀ g g', Commute (α g) (α' g'))
    (g : SpecialLinearGroup (Fin 2) k) (g' : SpecialLinearGroup (Fin 2) k') :
    Commute (sl2Lift π α g) (sl2Lift π α' g') := by
  have hconj : (MulAut.conj (π (sl2Lift π α g))).toMonoidHom.comp α' = α' := by
    ext x
    change π (sl2Lift π α g) * α' x * (π (sl2Lift π α g))⁻¹ = α' x
    rw [map_sl2Lift_large hk hπ α g, (hαα' g x).eq, mul_inv_cancel_right]
  have h3 := conj_sl2Lift_apply_large hk' hπ α' (sl2Lift π α g) g'
  rw [hconj] at h3
  exact mul_inv_eq_iff_eq_mul.1 h3

end CFSG.RankThree.CentralLift
