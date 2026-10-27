module

public import CFSG.Monster.Existence.TwoPointTwoB
public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.Monster.Existence

open CFSG CFSG.Blueprint

variable {G G' : Type} [Group G] [Group G']

theorem nonempty_mulEquiv_transport {X Y Z : Type} [Group X] [Group Y] [Group Z] (e : X ≃* Y)
    (h : Nonempty (X ≃* Z)) : Nonempty (Y ≃* Z) :=
  h.map fun f => e.symm.trans f

theorem TwoPointShape.of_mulEquiv {H : Subgroup G} {H' : Subgroup G'} (e : H ≃* H') :
    ∀ {i : Fin 9}, TwoPointShape H i → TwoPointShape H' i
  | 0, h => HasTwoShape.of_mulEquiv (k := 1)
      (P := fun X _ => Nonempty (X ≃* NativeSporadic.B)) e
      (fun _ _ _ _ f hX => hX.map fun g => f.symm.trans g) h
  | 1, h => by
    obtain ⟨N, hN, hE, hc, hL⟩ := h
    have : (N.map (e : H →* H')).Normal := hN.map _ e.surjective
    exact ⟨N.map (e : H →* H'), inferInstance,
      isElementaryAbelian_of_mulEquiv (N.equivMapOfInjective (e : H →* H') e.injective),
      by rw [Subgroup.card_map_of_injective e.injective, hc],
      CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.congr N _ e rfl) hL⟩
  | 2, h => HasLayeredTwoShape.of_mulEquiv (a := 2) (b := 22)
      (P := fun X _ => Nonempty (X ≃* NativeSporadic.Co2)) e
      (fun _ _ _ _ f hX => hX.map fun g => f.symm.trans g) h
  | 3, h => h.map fun g => e.symm.trans g
  | 4, h => h.map fun g => e.symm.trans g
  | 5, h => by
    obtain ⟨N, hN, hX, hc, hq⟩ := h
    have : (N.map (e : H →* H')).Normal := hN.map _ e.surjective
    exact ⟨N.map (e : H →* H'), inferInstance,
      IsExtraspecialPGroup.of_mulEquiv (N.equivMapOfInjective (e : H →* H') e.injective) hX,
      by rw [Subgroup.card_map_of_injective e.injective, hc],
      hq.map fun g => (QuotientGroup.congr N _ e rfl).symm.trans g⟩
  | 6, h => HasTwoShape.of_mulEquiv (k := 1) (P := fun X _ => LieModel X .F4 0 2 1) e
      (fun _ _ _ _ f hX => CFSG.LieType.CurtisTits.lieModel_of_mulEquiv f hX) h
  | 7, h => h.map fun g => e.symm.trans g
  | 8, h => HasTwoShape.of_mulEquiv (k := 1)
      (P := fun X _ => Nonempty (X ≃* NativeSporadic.Fi22)) e
      (fun _ _ _ _ f hX => hX.map fun g => f.symm.trans g) h

theorem map_conj_cent2 (g α β : G) :
    (cent2 α β).map (MulAut.conj g).toMonoidHom = cent2 (g * α * g⁻¹) (g * β * g⁻¹) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, ⟨hxa, hxb⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · calc g * x * g⁻¹ * (g * α * g⁻¹) = g * (x * α) * g⁻¹ := by group
        _ = g * (α * x) * g⁻¹ := by rw [hxa]
        _ = g * α * g⁻¹ * (g * x * g⁻¹) := by group
    · calc g * x * g⁻¹ * (g * β * g⁻¹) = g * (x * β) * g⁻¹ := by group
        _ = g * (β * x) * g⁻¹ := by rw [hxb]
        _ = g * β * g⁻¹ * (g * x * g⁻¹) := by group
  · rintro ⟨hya, hyb⟩
    refine ⟨g⁻¹ * y * g, ⟨?_, ?_⟩, by group⟩
    · calc g⁻¹ * y * g * α = g⁻¹ * (y * (g * α * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * α * g⁻¹) * y) * g := by rw [hya]
        _ = α * (g⁻¹ * y * g) := by group
    · calc g⁻¹ * y * g * β = g⁻¹ * (y * (g * β * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * β * g⁻¹) * y) * g := by rw [hyb]
        _ = β * (g⁻¹ * y * g) := by group

noncomputable def cent2ConjEquiv (g α β : G) :
    cent2 α β ≃* cent2 (g * α * g⁻¹) (g * β * g⁻¹) :=
  ((cent2 α β).equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
    (MulEquiv.subgroupCongr (map_conj_cent2 g α β))

theorem TwoPointShape.conj {α β : G} {i : Fin 9} (g : G) (h : TwoPointShape (cent2 α β) i) :
    TwoPointShape (cent2 (g * α * g⁻¹) (g * β * g⁻¹)) i :=
  TwoPointShape.of_mulEquiv (cent2ConjEquiv g α β) h

end CFSG.Monster.Existence
