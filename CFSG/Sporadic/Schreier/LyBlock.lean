module

public import CFSG.Sporadic.Schreier.LyOuter
public import CFSG.Sporadic.Ly
public import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotAlternating
public import CFSG.LocalAnalysis.ComponentInitial.GroupCentralQuotient

public section

namespace CFSG.Sporadic.LySchreier

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

theorem commuting_block_ly_overgroup_exclusion
    {G : Type*} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) :
    ¬ Nonempty (L ⧸ center L ≃* NativeSporadic.Ly) := by
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
  set C := centralizer ({QuotientGroup.mk' (center L) t} : Set (L ⧸ center L))
  obtain ⟨hCq, -, ⟨eA⟩⟩ := involution_centralizers_quasisimple ⟨e⟩ _ hπt
  have hB := (isComponentOf_iff_isComponent_subgroupOf hcompK.1).1 hcompK
  have hBC : centerQuotientImage L K₁ = C := by
    rcases quasisimple_subnormal_subgroups hCq hB.2 with h | h
    · exact le_antisymm hcompK.1 fun x hx => by
        have : (⟨x, hx⟩ : C) ∈ (centerQuotientImage L K₁).subgroupOf C := h ▸ mem_top _
        exact this
    · exfalso
      obtain ⟨-, -, a, b, hab⟩ := hB.1
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      have ha : (a : C) ∈ center C := h a.2
      have hab' : a * b = b * a := Subtype.ext (mem_center_iff.1 ha b).symm
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hab']
  have hS :
      Nat.card (centerQuotientImage L K₁ ⧸ center (centerQuotientImage L K₁)) = 19958400 := by
    rw [hBC, Nat.card_congr eA.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hS₂ : Nat.card (centerQuotientImage L K₂ ⧸ center (centerQuotientImage L K₂)) =
      Nat.card (centerQuotientImage L K₁ ⧸ center (centerQuotientImage L K₁)) := by
    rw [card_centerQuotientImage_block hq hK₂ (hKL K₂ hK₂),
      card_centerQuotientImage_block hq hK₁ (hKL K₁ hK₁)]
  have hsq := card_quotient_center_sq_dvd (hcomm K₁ hK₁ K₂ hK₂ hne).2
    (bot_le : (⊥ : Subgroup (L ⧸ center L)) ≤ center (L ⧸ center L)) hS₂.symm
  rw [hS, Nat.card_congr QuotientGroup.quotientBot.toEquiv, Nat.card_congr e.toEquiv,
    Sporadic.Ly.card_Ly] at hsq
  norm_num at hsq

end CFSG.Sporadic.LySchreier
