module

public import CFSG.Sporadic.Co1Block.Thirteen
public import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotAlternating
public import CFSG.LocalAnalysis.ComponentInitial.GroupCentralQuotient

public section

namespace CFSG.Sporadic.Co1Block

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

theorem commuting_block_co1_overgroup_exclusion
    {G : Type*} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) :
    ¬ Nonempty (L ⧸ center L ≃* NativeSporadic.Co1) := by
  classical
  rintro ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hodd, hπKq, hcomm, hloc, -⟩ :=
    escaping_block_quotient_inherits_local_components hq heven hJ hΔ hL hML hLH
  obtain ⟨K₁, hK₁, K₂, hK₂, hne⟩ := hΔ
  have hKL : ∀ K ∈ block J, K ≤ L := fun K hK => (le_blockGroup hK).trans hML
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := centerQuotientImage L K₂) 2
    (even_iff_two_dvd.1 (hπKq K₂ hK₂).2)
  obtain ⟨t, htK, ht2, -⟩ := exists_involution_lift_of_odd_center hodd u.2
    (by rw [Subgroup.orderOf_coe, hu])
  obtain ⟨hπt, hcompK⟩ := hloc K₁ hK₁ K₂ hK₂ hne t htK ht2
  have hB := (isComponentOf_iff_isComponent_subgroupOf hcompK.1).1 hcompK
  have h13 := cti_co1_involution_local_components_simple_quotient_divisible_by_thirteen ⟨e⟩
    hπt _ hB
  set S := Nat.card (centerQuotientImage L K₁ ⧸ center (centerQuotientImage L K₁))
  have hBS : Nat.card (((centerQuotientImage L K₁).subgroupOf
      (centralizer ({QuotientGroup.mk' (center L) t} : Set (L ⧸ center L)))) ⧸
        center ((centerQuotientImage L K₁).subgroupOf
          (centralizer ({QuotientGroup.mk' (center L) t} : Set (L ⧸ center L))))) = S := by
    let f := Subgroup.subgroupOfEquivOfLe hcompK.1
    exact Nat.card_congr (QuotientGroup.congr _ _ f (Subgroup.map_center_eq f)).toEquiv
  rw [hBS] at h13
  have hS₁ : S = Nat.card (J ⧸ center J) := card_centerQuotientImage_block hq hK₁ (hKL K₁ hK₁)
  have hS₂ : Nat.card (centerQuotientImage L K₂ ⧸ center (centerQuotientImage L K₂)) = S := by
    rw [hS₁]
    exact card_centerQuotientImage_block hq hK₂ (hKL K₂ hK₂)
  have hsq : S ^ 2 ∣ 4157776806543360000 := by
    have h := card_quotient_center_sq_dvd (hcomm K₁ hK₁ K₂ hK₂ hne).2
      (bot_le : (⊥ : Subgroup (L ⧸ center L)) ≤ center (L ⧸ center L)) hS₂.symm
    rw [Nat.card_congr QuotientGroup.quotientBot.toEquiv, Nat.card_congr e.toEquiv,
      CFSG.Sporadic.Co1.card_Co1] at h
    exact h
  rw [h13.1] at hsq
  norm_num at hsq

end CFSG.Sporadic.Co1Block
