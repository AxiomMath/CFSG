module

import all CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6
public import CFSG.Quasithin.EmptyFaithful.S151WJ
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Fin257
  CFSG.QuasithinUnique.Borel252 CFSG.QuasithinUnique.Borel252.A6

theorem wk_card_Sa : Nat.card Sa = 24 := by
  obtain ⟨-, hs, -, -, hsn, -, -, -, -, -⟩ := sizes_ok
  rw [card_of_list R6.enc_inj Sa saL hsn mem_Sa (fun r hr => (sound_Sa r hr).imp fun x hx => hx.2)]
  exact hs

theorem wk_card_Sb : Nat.card Sb = 24 := by
  obtain ⟨-, -, hs, -, -, hsn, -, -, -, -⟩ := sizes_ok
  rw [card_of_list R6.enc_inj Sb sbL hsn mem_Sb (fun r hr => (sound_Sb r hr).imp fun x hx => hx.2)]
  exact hs

theorem rank2Data_A6 : Rank2Data U6 := by
  have hD := borelData_A6
  have hsup : Ka ⊔ Kb = ⊤ := by
    have := hD.sup_norm
    rwa [normalizer_Ra, normalizer_Rb] at this
  have hmaxK : ∀ K₁ K₂ : Subgroup M6, K₁ ⊔ K₂ = ⊤ → K₁ < ⊤ → K₂ < ⊤ → U6 < K₁ → U6 < K₂ →
      (∀ X : Subgroup M6, U6 < X → X < ⊤ → X = K₁ ∨ X = K₂) → IsMaxSubgroupIn ⊤ K₁ := by
    intro K₁ K₂ hs h1 h2 hU1 hU2 honly
    refine ⟨h1, fun K hK _ => ?_⟩
    by_contra hne
    have hKt : K < ⊤ := lt_top_iff_ne_top.2 hne
    rcases honly K (hU1.trans hK) hKt with h | h
    · exact hK.ne' h
    · rw [h] at hK
      have : K₁ ⊔ K₂ = K₂ := sup_eq_right.2 hK.le
      rw [this] at hs
      exact h2.ne hs
  have honly : ∀ X : Subgroup M6, U6 < X → X < ⊤ → X = Ka ∨ X = Kb := fun X h1 h2 =>
    only_A6 X (by rw [normalizer_U6]; exact h1) h2
  have hmaxKa : IsMaxSubgroupIn ⊤ Ka := hmaxK Ka Kb hsup Ka_lt_top Kb_lt_top U6_lt_Ka U6_lt_Kb honly
  have hmaxKb : IsMaxSubgroupIn ⊤ Kb :=
    hmaxK Kb Ka (by rw [sup_comm]; exact hsup) Kb_lt_top Ka_lt_top U6_lt_Kb U6_lt_Ka
      (fun X h1 h2 => (honly X h1 h2).symm)
  have hcU : Nat.card U6 = 8 := by rw [U6, card_sub D0_le_A6, card_D0]
  refine ⟨normalizer_U6.le, Ka, Kb, ?_, hmaxKa, hmaxKb, U6_lt_Ka.le, U6_lt_Kb.le, ?_, ?_, ?_, ?_, ?_⟩
  · have := hD.ne_norm
    rwa [normalizer_Ra, normalizer_Rb] at this
  · rw [hcU, Ka, card_sub Sa_le_A6, wk_card_Sa]
  · rw [hcU, Kb, card_sub Sb_le_A6, wk_card_Sb]
  · have := hD.charTwo₁
    rwa [normalizer_Ra] at this
  · have := hD.charTwo₂
    rwa [normalizer_Rb] at this
  · intro K hK hUK
    have hlt : U6 < K := by
      refine lt_of_le_of_ne hUK fun h => ?_
      have := hK.2 Ka (h ▸ U6_lt_Ka) le_top
      exact Ka_lt_top.ne this
    exact honly K hlt hK.1

theorem input15122Rank2Lat_A6 (G : Type) [Group G] [Finite G] (L B : Subgroup G)
    (h : IsAltBlockType L 6) (hB : IsSylowTwoOf B L) :
    L ⊓ Subgroup.normalizer (B : Set G) ≤ B ∧
      ∀ M' : Subgroup G, IsMaxSubgroupIn L M' → B ≤ M' → ∃ P : Subgroup G, OtherPar L B M' P := by
  obtain ⟨-, α, hα, hker, -⟩ := h
  exact rank2Lat_of_sylow_data hB α hα hker sylow_U6 rank2Data_A6

end CFSG.Quasithin
