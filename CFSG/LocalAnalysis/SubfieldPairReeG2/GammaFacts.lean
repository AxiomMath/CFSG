module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIReeSocleSteps
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeWhole

public section

open CFSG CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley

namespace CFSG.LocalAnalysis.SubfieldPairReeG2

section GammaFacts


variable {m : ℕ} {k : Type} [Field k] [Finite k] [CharP k G2.prime]

theorem reeGamma_involution_conj (hk : Nat.card k = 3 ^ (2 * m + 1))
    {x y : G2.reeGamma k m} (hx : orderOf x = 2) (hy : orderOf y = 2) :
    ∃ g : G2.reeGamma k m, g * x * g⁻¹ = y := by
  obtain ⟨g₁, h₁⟩ := CFSG.ComponentClassification.OutcomeLocal.ree_involution_fusion hk x hx
  obtain ⟨g₂, h₂⟩ := CFSG.ComponentClassification.OutcomeLocal.ree_involution_fusion hk y hy
  refine ⟨g₂⁻¹ * g₁, ?_⟩
  calc g₂⁻¹ * g₁ * x * (g₂⁻¹ * g₁)⁻¹ = g₂⁻¹ * (g₁ * x * g₁⁻¹) * g₂ := by group
    _ = g₂⁻¹ * (g₂ * y * g₂⁻¹) * g₂ := by rw [h₁, ← h₂]
    _ = y := by group

theorem reeGamma_exists_sylow_two (hk : Nat.card k = 3 ^ (2 * m + 1)) :
    ∃ S : Sylow 2 (G2.reeGamma k m),
      Nat.card (S : Subgroup (G2.reeGamma k m)) = 8 ∧ ∀ x ∈ (S : Subgroup (G2.reeGamma k m)), x ^ 2 = 1 := by
  classical
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element G2.tag
  obtain ⟨-, hel, h8, ⟨P, hP⟩, -, -⟩ :=
    CFSG.Walter.Ree.Model.small_Ree_prime_field_involution_fusion m k hk w₀ hw₀
  refine ⟨P, ?_, ?_⟩
  · have hc : Nat.card ((P : Subgroup (G2.reeGamma k m)).map (G2.reeGamma k m).subtype) =
        Nat.card (P : Subgroup (G2.reeGamma k m)) :=
      Subgroup.card_map_of_injective (G2.reeGamma k m).subtype_injective
    rw [← hc, hP]
    exact h8
  · intro x hx
    have hxE : (x : ModGL G2.tag k) ∈ CFSG.Walter.Ree.Model.smallReeE8 m k w₀ := by
      rw [← hP]; exact ⟨x, hx, rfl⟩
    haveI := hel
    have h2 : (x : ModGL G2.tag k) ^ 2 = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (A := CFSG.Walter.Ree.Model.smallReeE8 m k w₀) _ hxE
    exact Subtype.ext (by simpa using h2)

theorem reeGamma_exists_simple (hk : Nat.card k = 3 ^ (2 * m + 1)) :
    ∃ W : Subgroup (G2.reeGamma k m), IsSimpleGroup W ∧ (∃ x y : W, x * y ≠ y * x) ∧
      ∃ s ∈ W, orderOf s = 2 := by
  classical
  rcases Nat.eq_zero_or_pos m with h0 | hm
  ·
    subst h0
    have hk3 : Nat.card k = 3 := by simpa using hk
    obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element G2.tag
    obtain ⟨-, hDΓ, -, hD504, -, hDs, hDnc, -⟩ :=
      CFSG.LieType.Ree.small_Ree_three_derived_simple k hk3 w₀ hw₀
    set D := Subgroup.closure {ReeTag.g2U₀ k, canonicalRep (coxeterSystem G2.tag) k w₀} with hD
    let e : (D.subgroupOf (G2.reeGamma k 0)) ≃* D := Subgroup.subgroupOfEquivOfLe hDΓ
    refine ⟨D.subgroupOf (G2.reeGamma k 0), ?_, ?_, ?_⟩
    · haveI := hDs
      exact e.isSimpleGroup
    · obtain ⟨x, y, hxy⟩ := hDnc
      exact ⟨e.symm x, e.symm y, fun h => hxy (e.symm.injective (by rw [map_mul, map_mul]; exact h))⟩
    · have hdvd : 2 ∣ Nat.card D := by rw [hD504]; norm_num
      obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 2 hdvd
      refine ⟨((e.symm s : ↥(D.subgroupOf (G2.reeGamma k 0))) : G2.reeGamma k 0),
        (e.symm s).2, ?_⟩
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact hs
  ·
    obtain ⟨-, hs, x, y, hxy⟩ :=
      CFSG.ComponentClassification.CatalogueBSmallRee.reeGamma_G2_simple hm k hk
    refine ⟨⊤, ?_, ⟨⟨x, trivial⟩, ⟨y, trivial⟩, fun h => hxy (congrArg Subtype.val h)⟩, ?_⟩
    · haveI := hs
      exact (Subgroup.topEquiv : (⊤ : Subgroup (G2.reeGamma k m)) ≃* _).isSimpleGroup
    · refine ⟨⟨_, CFSG.Walter.Ree.Model.smallReeH_neg_one_mem_reeGamma hk⟩, trivial, ?_⟩
      exact CFSG.Walter.Ree.Model.orderOf_smallReeH_neg_one hk

theorem reeGamma_sylow_two_card (hk : Nat.card k = 3 ^ (2 * m + 1))
    (S : Sylow 2 (G2.reeGamma k m)) : Nat.card (S : Subgroup (G2.reeGamma k m)) = 8 := by
  obtain ⟨S₀, h8, -⟩ := reeGamma_exists_sylow_two (m := m) hk
  have h0 := Sylow.card_eq_multiplicity S₀
  have h1 := Sylow.card_eq_multiplicity S
  rw [h1, ← h0]
  exact h8

end GammaFacts

end CFSG.LocalAnalysis.SubfieldPairReeG2
