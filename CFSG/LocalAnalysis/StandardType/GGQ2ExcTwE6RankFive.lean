module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6Defs
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6RankNoTwo
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6RankComp
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6RankLabel
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6RankUnit
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6RankOrth
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6RankTwD4

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType


theorem excTwE6RankFive_holds : ExcTwE6RankFive := by
  intro G _ _ B Bs x L D J hS hM
  by_contra hlt
  obtain ⟨-, hBs, hx, -, h4le⟩ := hS.1.1.tableB_facts
  have h4 : Nat.card Bs = 3 ^ 4 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3)).1 hBs.isPGroup
    rw [hn] at h4le hlt ⊢
    have h1 : 4 ≤ n := (Nat.pow_le_pow_iff_right (by norm_num)).1 h4le
    have h2 : n < 5 := by
      by_contra h
      exact hlt (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [show n = 4 by omega]
  have hN : Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
    obtain ⟨-, lab, -, hraw⟩ := hS.1.2.2.2.2
    obtain ⟨R, _, I, F, -, -, θ, hN, -⟩ := largeEvenRawDatum_exists hraw
    exact hN
  have hNo : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ ggG0 3 B x L D J →
      Bs ≤ Subgroup.normalizer (S : Set G) →
      ¬ S ≤ Subgroup.centralizer (ggG0 3 B x L D J : Set G) → False :=
    fun S h2 hSG hSN hSZ => excTwE6_noTwo hS hM h4 h2 hSG hSN hSZ
  obtain ⟨lab, hΛ, hhas, hT⟩ := excTwE6_L_label hS hM hN hx (excTwE6_isComponentOf_L hS hN hx)
    (excTwE6_component_unique hS hN hx hNo)
  rcases hT with h | h | h | h | h | h | h
  · exact hlt (excTwE6_rank_of_unit hS hΛ hhas (Or.inl h))
  · exact hlt (excTwE6_rank_of_orth hS hΛ hhas (Or.inl h))
  · exact hlt (excTwE6_rank_of_orth hS hΛ hhas (Or.inr (Or.inr h)))
  · exact hlt (excTwE6_rank_of_orth hS hΛ hhas (Or.inr (Or.inl h)))
  · exact hlt (excTwE6_rank_of_unit hS hΛ hhas (Or.inr (Or.inl h)))
  · exact hlt (excTwE6_rank_of_unit hS hΛ hhas (Or.inr (Or.inr h)))
  · subst h
    obtain ⟨S, h2, hSL, hSN, hSZ⟩ := excTwE6_twD4_twoSub hS hhas
    have hLG : L ≤ ggG0 3 B x L D J := by unfold ggG0; exact le_sup_left
    exact hNo S h2 (hSL.trans hLG) hSN fun hc =>
      hSZ (hc.trans (Subgroup.centralizer_le hLG))

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
