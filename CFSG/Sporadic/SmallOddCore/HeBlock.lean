module

public import CFSG.Sporadic.SmallOddCore.HeLocal
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotAlternating
public import CFSG.LocalAnalysis.ComponentInitial.GroupCentralQuotient

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

theorem card_nativeHe :
    Nat.card NativeSporadic.He = 4030387200 := by
  rw [Nat.card_congr CFSG.Sporadic.HeldB.heEquivP.toEquiv, CFSG.Sporadic.HeldB.card_heP]

theorem commuting_block_he_overgroup_exclusion
    {G : Type*} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) :
    ¬ Nonempty (L ⧸ center L ≃* NativeSporadic.He) := by
  classical
  rintro ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hodd, hπKq, hcomm, hloc, -⟩ :=
    escaping_block_quotient_inherits_local_components hq heven hJ hΔ hL hML hLH
  obtain ⟨K₁, hK₁, K₂, hK₂, hne⟩ := hΔ
  have hinv : ∀ K ∈ block J, ∃ t : L, (t : G) ∈ K ∧ orderOf t = 2 := by
    intro K hK
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := centerQuotientImage L K) 2
      (even_iff_two_dvd.1 (hπKq K hK).2)
    obtain ⟨t, htK, ht2, -⟩ := exists_involution_lift_of_odd_center hodd u.2
      (by rw [Subgroup.orderOf_coe, hu])
    exact ⟨t, htK, ht2⟩
  have h20160 : ∀ Ka ∈ block J, ∀ Kb ∈ block J, Ka ≠ Kb →
      Nat.card (centerQuotientImage L Ka ⧸ center (centerQuotientImage L Ka)) = 20160 := by
    intro Ka hKa Kb hKb hab
    obtain ⟨t, htK, ht2⟩ := hinv Kb hKb
    obtain ⟨hπt, hcompK⟩ := hloc Ka hKa Kb hKb hab t htK ht2
    exact cti_he_involution_local_components_simple_quotient_order ⟨e⟩ hπt hcompK
  have hsq := card_quotient_center_sq_dvd (hcomm K₁ hK₁ K₂ hK₂ hne).2
    (bot_le : (⊥ : Subgroup (L ⧸ center L)) ≤ center (L ⧸ center L))
    (by rw [h20160 K₁ hK₁ K₂ hK₂ hne, h20160 K₂ hK₂ K₁ hK₁ hne.symm])
  rw [h20160 K₁ hK₁ K₂ hK₂ hne, Nat.card_congr QuotientGroup.quotientBot.toEquiv,
    Nat.card_congr e.toEquiv, card_nativeHe] at hsq
  norm_num at hsq

end CFSG.Sporadic.SmallOddCore
