module

public import CFSG.Quasithin.EmptyFaithful.S146zRL3A

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

theorem l3_inner_of_normalizes_ambient {X : Type*} [Group X] [Finite X] {N₁ R Y : Subgroup X}
    (hL : Nonempty (↥N₁ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hRN : R ≤ N₁) (hYN : Y ≤ N₁) (hR : IsPGroup 2 R) (hRi : ¬ 2 ∣ R.relIndex N₁)
    (hRY : R ≤ Subgroup.normalizer (Y : Set X)) (hO : oTwoUpper Y = Y) (hY : Y ≠ ⊥)
    (h7 : ¬ 7 ∣ Nat.card Y) {t : X} (ht : t ∈ Subgroup.normalizer (N₁ : Set X))
    (htY : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y) :
    ∃ g ∈ N₁, ∀ m ∈ N₁, t * m * t⁻¹ = g * m * g⁻¹ := by
  obtain ⟨φ, hφ⟩ : ∃ φ : MulAut ↥N₁, ∀ x : ↥N₁, ((φ x : ↥N₁) : X) = t * x * t⁻¹ :=
    ⟨N₁.normalizerMonoidHom ⟨t, ht⟩, fun x => rfl⟩
  have hYmap : (Y.subgroupOf N₁).map N₁.subtype = Y := Subgroup.map_subgroupOf_eq_of_le hYN
  have hRY' : R.subgroupOf N₁ ≤
      Subgroup.normalizer ((Y.subgroupOf N₁ : Subgroup ↥N₁) : Set ↥N₁) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (hRY hr) (y : X)
  have hO' : oTwoUpper (Y.subgroupOf N₁) = Y.subgroupOf N₁ := by
    apply Subgroup.map_injective N₁.subtype_injective
    rw [← oTwoUpper_map, hYmap, hO]
  have hY' : Y.subgroupOf N₁ ≠ ⊥ := fun h => hY (by rw [← hYmap, h, Subgroup.map_bot])
  have hcard : Nat.card (Y.subgroupOf N₁) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYN).toEquiv
  have h7' : ¬ 7 ∣ Nat.card (Y.subgroupOf N₁) := by rwa [hcard]
  have hφY : (Y.subgroupOf N₁).map φ.toMonoidHom = Y.subgroupOf N₁ := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨y, hy, rfl⟩
      show ((φ y : ↥N₁) : X) ∈ Y
      rw [hφ]
      exact htY y hy
    · exact (Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective).ge
  obtain ⟨g, hg⟩ := l3_aut_inner_of_normalizes hL (A4.isPGroup_subgroupOf_of_le hRN hR) hRi hRY'
    hO' hY' h7' φ hφY
  refine ⟨(g : X), g.2, fun m hm => ?_⟩
  have h1 := congrArg (fun ψ : MulAut ↥N₁ => ((ψ ⟨m, hm⟩ : ↥N₁) : X)) hg
  simpa [hφ, MulAut.conj_apply] using h1.symm

end CFSG.Quasithin
