module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFT7SecMat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFT7SecSplit
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFT7SecSyl
public import CFSG.Quasithin.EmptyFaithful.S146F3
public import CFSG.Quasithin.EmptyFaithful.SBc11List

public section

namespace CFSG.Quasithin.SBd19F

theorem center_eq_bot_of_sq_lifts {E : Type} [Group E] [Finite E] [Group.IsPerfect E]
    (hexp : ∀ a ∈ Subgroup.center E, a * a = 1)
    (hL32 : IsPSL 3 2 1 (E ⧸ Subgroup.center E))
    (hsq : ∀ y : E, y * y ∈ Subgroup.center E → y * y = 1) :
    Subgroup.center E = ⊥ := by
  obtain ⟨φ⟩ := isPSL_three_two_iff.mp hL32
  let ρ : E →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center E))
  have hker : ∀ x, ρ x = 1 ↔ x ∈ Subgroup.center E := fun x => by
    simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    rw [map_eq_one_iff φ φ.injective, QuotientGroup.eq_one_iff]
  have hsurj : Function.Surjective ρ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨u₁, hu₁⟩ := hsurj slThreeTwoE12
  obtain ⟨u₂, hu₂⟩ := hsurj slThreeTwoE23
  have h1 : u₁ * u₁ = 1 :=
    hsq _ ((hker _).mp (by rw [map_mul, hu₁]; exact slThreeTwoE12_mul_self))
  have h2 : u₂ * u₂ = 1 :=
    hsq _ ((hker _).mp (by rw [map_mul, hu₂]; exact slThreeTwoE23_mul_self))
  have h4 : (u₁ * u₂) ^ 4 = 1 := by
    have hmem : (u₁ * u₂) ^ 4 ∈ Subgroup.center E := (hker _).mp (by
      rw [map_pow, map_mul, hu₁, hu₂]
      exact slThreeTwoE_prod_pow_four)
    have h : (u₁ * u₂) ^ 4 = (u₁ * u₂ * (u₁ * u₂)) * (u₁ * u₂ * (u₁ * u₂)) := by
      rw [show 4 = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
    rw [h] at hmem ⊢
    exact hsq _ hmem
  have hd : DihedralDistinct ρ u₁ u₂ := by
    intro i j e d hi hj he hd h
    rw [hu₁, hu₂] at h
    exact slThreeTwoE_dihedral_distinct hi hj he hd h
  have hA : IsPGroup 2 (Subgroup.center E) := fun g =>
    ⟨1, Subtype.ext (by simpa [pow_two] using hexp g.1 g.2)⟩
  have hP8 := card_closure_pair_eq_eight h1 h2 h4 hd
  have hPA := closure_pair_inf_eq_bot (fun a ha => (hker a).mpr ha) h1 h2 h4 hd
  refine eq_bot_of_central_two_complement le_rfl hA ?_ hP8 hPA
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center E),
    SBc11.card_of_isPSL_three_two hL32]

end CFSG.Quasithin.SBd19F
