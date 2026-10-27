module

public import CFSG.RankThree.GF2n.Stroth80.Sec101LayerII
public import CFSG.RankThree.GF2n.Stroth80.Sec101TypeI
public import CFSG.RankThree.GF2n.Stroth80.Sec101TypeII
public import CFSG.RankThree.GF2n.Stroth80.Sec101Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7EndGold

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.GOC
open scoped commutatorElement


section Split


theorem bender_or_sylow_le_eight {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    (h : goldschmidtSimpleType L) :
    fusionIsBenderGroup L ∨ ∀ T : Sylow 2 L, Nat.card (T : Subgroup L) ≤ 8 := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpo, hf, -, h8, ⟨e⟩⟩ |
    ⟨m, hm, hcard⟩ | ⟨⟨e⟩⟩
  · exact Or.inl (Or.inl ⟨f, by omega, ⟨e⟩⟩)
  · exact Or.inl (Or.inr (Or.inr ⟨n, hn, ⟨e⟩⟩))
  · exact Or.inl (Or.inr (Or.inl ⟨f, hf, ⟨e⟩⟩))
  · haveI := hp
    refine Or.inr fun T => ?_
    have := (CFSG.Goldschmidt.GoldType.sylow_of_psl2_odd hpo hf h8 e T).1
    omega
  · refine Or.inr fun T => ?_
    have := (CFSG.Goldschmidt.GoldType.sylow_of_ree_or_j1 (K := L) (Or.inl ⟨m, hm, hcard⟩) T).2.1
    omega
  · refine Or.inr fun T => ?_
    have := (CFSG.Goldschmidt.GoldType.sylow_of_ree_or_j1 (K := L) (Or.inr ⟨e⟩) T).2.1
    omega

end Split

section Gold


theorem stroth101End_of (h34 : Stroth34Statement) (h44 : Stroth44Statement)
    (h45 : Stroth45Statement) (hNt : StrothNtStatement) :
    Stroth101EndStatement := by
  intro G _ _ M Q Z B _ hc n H _hno X _hX _hsat _hBX S _hS t ht ht1 htS htc _htO hab
  have hq := H.isQuasisimple_layer h34 h44 h45
  have hcs : CompSimple (Mbar M Q) := hc.compSimple h34 h44 H.width H.n_gt H.noA2 H.gen
  have hLBH : bar M Q (LB M Q B) ≤ bar M Q (H0 M Z) :=
    hc.bar_LB_le_bar_Lgen.trans hc.bar_Lgen_le_bar_H0
  haveI := hc.normal_bar_H0
  have hO : goldschmidtOddCore ↥(Subgroup.normalClosure ({t} : Set (Mbar M Q))) = ⊥ := by
    refine endg_goldschmidtOddCore_eq_bot (H := bar M Q (H0 M Z)) (fun Y hY hYH hodd => ?_)
      Subgroup.normalClosure_normal ?_
    · exact h44 G M Q Z B hc n H.width H.n_gt H.noA2 H.gen Y hYH
        (fun x _ => by rw [Subgroup.normalizer_eq_top_iff.mpr hY]; exact Subgroup.mem_top x) hodd
    · exact Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr (hLBH ht))
  have hO2 : pCore 2 ↥(Subgroup.normalClosure ({t} : Set (Mbar M Q))) = ⊥ :=
    endg_pCore_eq_bot_of_normal hc.pCore_two_Mbar Subgroup.normalClosure_normal
  obtain ⟨hdec, hgold⟩ := endg_gold_decomp S htS htc hab hO hO2
  obtain ⟨K, hK, hKnc⟩ : ∃ K : Subgroup (Mbar M Q), IsComponent K ∧
      K ≤ Subgroup.normalClosure ({t} : Set (Mbar M Q)) := by
    by_contra hnone
    push Not at hnone
    have hbot : Subgroup.normalClosure ({t} : Set (Mbar M Q)) = ⊥ := by
      rw [hdec]
      exact iSup₂_eq_bot.mpr fun K hK => (hnone K hK.1 hK.2).elim
    have htm : t ∈ Subgroup.normalClosure ({t} : Set (Mbar M Q)) :=
      Subgroup.subset_normalClosure (Set.mem_singleton t)
    rw [hbot, Subgroup.mem_bot] at htm
    exact ht1 htm
  have hKL : K = layer (Mbar M Q) := eq_layer_of_isComponent hq hK
  have hgK := hgold K hK hKnc
  rw [hKL] at hgK
  have hLc : IsComponent (layer (Mbar M Q)) := hKL ▸ hK
  have hZ : Subgroup.center ↥(layer (Mbar M Q)) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp
      hcs.center_layer_eq_bot
  haveI hsimple : IsSimpleGroup ↥(layer (Mbar M Q)) := isSimpleGroup_of_center_eq_bot hLc hZ
  have hL : goldschmidtSimpleType ↥(layer (Mbar M Q)) :=
    endg_goldschmidtSimpleType_congr
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)) hgK
  obtain ⟨hout, -⟩ := endg_gold_facts hL
  rcases bender_or_sylow_le_eight hL with hB | h8
  · exact H.false_of_bender_layer h34 h44 hNt hB hout
  · exact H.false_of_small_layer h34 h44 hout h8

end Gold

end CFSG.RankThree.GF2n.Stroth80
