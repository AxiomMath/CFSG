module

public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

theorem s16t_w3_exists_perm {T : Type} [CommGroup T] {U : Subgroup T} (hU : Nat.card ↥U = 4) :
    ∃ r : ↥(stabSub U) →* Equiv.Perm (Fin 3),
      ∀ g : ↥(stabSub U), r g = 1 ↔ ∀ u ∈ U, (g : MulAut T) u = u := by
  classical
  have : Finite ↥U := Nat.finite_of_card_ne_zero (by rw [hU]; norm_num)
  have := Fintype.ofFinite ↥U
  let N : Set ↥U := {x | x ≠ 1}
  have hN : Fintype.card ↥N = 3 := by
    rw [Set.card_ne_eq, ← Nat.card_eq_fintype_card, hU]
  let e : ↥N ≃ Fin 3 := Fintype.equivFinOfCardEq hN
  let φ : MulAut ↥U →* Equiv.Perm ↥N :=
    { toFun := fun σ => Equiv.Perm.subtypePerm σ.toEquiv fun x => MulEquiv.map_ne_one_iff σ
      map_one' := Equiv.ext fun x => Subtype.ext rfl
      map_mul' := fun a b => Equiv.ext fun x => Subtype.ext rfl }
  refine ⟨(e.permCongrHom.toMonoidHom.comp φ).comp (resHom U), fun g => ?_⟩
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff]
  constructor
  · intro h1 u hu
    by_cases hu1 : (⟨u, hu⟩ : ↥U) = 1
    · rw [show u = 1 from congrArg Subtype.val hu1, map_one]
    · exact congrArg (fun π : Equiv.Perm ↥N => ((π ⟨⟨u, hu⟩, hu1⟩ : ↥U) : T)) h1
  · intro h1
    exact Equiv.ext fun x => Subtype.ext (Subtype.ext (h1 _ x.1.2))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
