module

public import CFSG.Quasithin.Background.RonanH163Vocab

public section

namespace CFSG.Quasithin.RonanH155

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RonanH163 CFSG.Quasithin.RonanH143

@[expose] def restrictAutHom {G : Type*} [Group G] {V : Type*} [CommGroup V] (ρ : G →* MulAut V)
    (W : Subgroup V) (hW : ∀ g : G, ∀ w ∈ W, ρ g w ∈ W) : G →* MulAut ↥W where
  toFun g :=
    { toFun := fun w => ⟨ρ g (w : V), hW g w w.2⟩
      invFun := fun w => ⟨ρ g⁻¹ (w : V), hW g⁻¹ w w.2⟩
      left_inv := fun w => by
        apply Subtype.ext
        show ρ g⁻¹ (ρ g (w : V)) = w
        rw [map_inv, MulAut.inv_apply_self]
      right_inv := fun w => by
        apply Subtype.ext
        show ρ g (ρ g⁻¹ (w : V)) = w
        rw [map_inv, MulAut.apply_inv_self]
      map_mul' := fun a b => Subtype.ext (map_mul (ρ g) (a : V) (b : V)) }
  map_one' := by
    ext w
    show ρ 1 (w : V) = w
    rw [map_one, MulAut.one_apply]
  map_mul' := fun g g' => by
    ext w
    show ρ (g * g') (w : V) = ρ g (ρ g' (w : V))
    rw [map_mul, MulAut.mul_apply]

theorem fixV_rImg_invariant {V : Type*} [CommGroup V] {Γ : Subgroup P24} (ρ : ↥Γ →* MulAut V)
    (A : Subgroup P24) (g : ↥Γ) (hg : ∀ a : P24, a ∈ A ↔ (g : P24) * a * (g : P24)⁻¹ ∈ A)
    (w : V) (hw : w ∈ fixV (rImg ρ A)) : ρ g w ∈ fixV (rImg ρ A) := by
  rw [mem_fixV] at hw ⊢
  intro a ha
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 ha
  have hyA : (y : P24) ∈ A := Subgroup.mem_subgroupOf.1 hy
  have hy' : g⁻¹ * y * g ∈ A.subgroupOf Γ := by
    rw [Subgroup.mem_subgroupOf]
    refine (hg _).2 ?_
    have e : (g : P24) * ((g⁻¹ * y * g : ↥Γ) : P24) * (g : P24)⁻¹ = (y : P24) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact hyA
  have h1 := hw (ρ (g⁻¹ * y * g)) (Subgroup.mem_map_of_mem ρ hy')
  calc ρ y (ρ g w) = ρ g (ρ (g⁻¹ * y * g) w) := by
        rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, map_inv, MulAut.apply_inv_self]
    _ = ρ g w := by rw [h1]

end CFSG.Quasithin.RonanH155
