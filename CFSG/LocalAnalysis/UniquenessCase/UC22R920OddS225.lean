module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251i
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251K
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Opp
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251j
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5
import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9 (R920odd)

variable {G : Type} [Group G] [Finite G]

theorem uc22p2251j_false_of_isL3_r920odd (D : Data G) (hx : DataExt D) (he : 3 < evenRank G)
    (hk : D.k = 1) (h847 : F08.R847 D) (h920 : R920odd D) {K Y H : Subgroup G}
    (hK : K ∈ calC D.M) (hL3 : IsL3 (Bar2 K) 1) (hYK : Y ≤ K) (hcov : K = Y ⊔ pCoreOf 2 K)
    (hY : Nonempty (Bar2 Y ≃* Bar2 K)) (hYH : Y ≤ H) (hHT : H ≠ ⊤) (hHM : ¬ H ≤ D.M) :
    False := by
  have hKM : K ≤ D.M := hK.1.le
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 K
  have hKY : K ⊓ Y = Y := inf_eq_right.2 hYK
  have hyp : PartTwo.Hyp919c D K P Y H := by
    refine ⟨hK, hP.le, PartTwo.card_sylow_three_of_isL3_bar2 hL3 hP,
      uc22p2251j_sylow_mem D hk hKM (by rw [PartTwo.card_eq_of_isL3 hL3]; norm_num) hP,
      hYK.trans hKM, ?_, ?_, ⟨0, ?_⟩, hHT, hYH, hHM⟩
    · rw [hKY]
      exact hcov
    · rw [hKY, subgroupOf_self]
      infer_instance
    · rw [hKY, subgroupOf_self, index_top, pow_zero]
  obtain ⟨eY⟩ := hY
  have hL27 : IsL2Odd (Bar2 Y) 7 :=
    CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism (Bar2 Y)
      (CFSG.Blueprint.LieModel.of_mulEquiv eY.symm hL3)
  obtain ⟨A', hA'Y, hA'p, hA'o, hA'N⟩ :=
    h920 K P Y H hyp hYK 7 (by norm_num) (by norm_num) hL27
  obtain ⟨p, hp⟩ := hx.sig_nonempty
  have hq2 : Nat.card A' ≠ 2 := by
    intro h
    have h1 := Nat.odd_iff.1 hA'o
    omega
  rcases h847 K hK A' (hA'Y.trans hYK) (Nat.card A') hA'p hq2 rfl p hp
      (Or.inl (uc22p2251b_thin8 (Or.inr hL3))) with h | ⟨-, -, -, -, -, h3, -⟩ |
      ⟨-, -, -, -, -, h3, -⟩
  · exact hA'N h
  · omega
  · omega

theorem s22_5_1K1_of_inputs_r920odd (D : Data G) (Ch : Choice2011 G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (he : 3 < evenRank G) (h33 : S22_3_3 D Ch) (h119 : R119W D)
    (h17 : S21_17 D Ch) (h211 : S21_1 D Ch) (hn3 : ∀ c : Ctx21 D Ch, 3 ≤ c.n)
    (h847 : F08.R847 D) (h920 : R920odd D) (h923 : F09.R923 D) (h2112 : S21_12 D Ch) :
    S22_5_1K1 D Ch := by
  intro hk hH c m Nb hNb i
  by_contra hbad
  obtain ⟨K, hK, hKb, ⟨eK⟩, hbs, hKn⟩ :=
    uc22p2251b_exists_bad D hx h61 h119 h17 hH c.toCtx22 hNb hbad
  have hKM : K ≤ D.M := hK.1.le
  have hKN : D.M ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hKM).1 hKn
  obtain ⟨A, hAB, hA, hA7, hAN, hAT, hc⟩ :=
    uc22p2251h_exists_A D Ch hH c.toCtx21 hk (hn3 _) h2112 hK hbs
  have hAM : A ≤ D.M := hAB.trans c.hBM
  obtain ⟨-, hcov1, hY, hcov⟩ := uc22p2251h_cover hKM hKn hAM hA (by omega) hc hbs.layerShape
  have hYN : K ⊓ centralizer (A : Set G) ≤ normalizer (A : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  rcases hbs with h2 | h3
  · obtain ⟨e5⟩ := BadShape22.nonempty_mulEquiv_alt_five_of_isL2Ev_two h2
    have h60 : Nat.card (Bar2 K) = 60 :=
      (Nat.card_congr e5.toEquiv).trans CFSG.QuasithinUnique.A5.Delta5.a5_card
    have hi : IsL2Ev ↥(Nb i) 2 ∨ IsS5 ↥(Nb i) := by
      rcases hNb.2 i with ⟨n, hn⟩ | h | h
      · obtain rfl : n = 2 := by
          by_contra hne
          exact hbad ⟨n, hn, hne⟩
        exact Or.inl hn
      · rw [Nat.card_congr eK.toEquiv, LayerShape22.commutator_eq_self (Y := Nb i) (Or.inr h),
          PartTwo.card_eq_of_isL3 h] at h60
        exfalso
        omega
      · exact Or.inr h
    have hX := PartTwo.close16_opp_le 3 (K ⊓ centralizer (A : Set G))
    have hN := h923 K hK hKM hKN ⟨e5⟩ (uc22p2251j_uniqueMax D Ch h211 hH c.toCtx21 hk hKM hKN e5)
      (fun P hP => uc22p2251j_sylow_mem D hk hKM (by rw [h60]; norm_num) hP)
      (Opp 3 (K ⊓ centralizer (A : Set G))) (PartTwo.close16_opp_idem 3 _)
      (hX.trans inf_le_left) hcov
      (uc22p2251i_r923_hyp D Ch h33 hH c hNb hi hK hKb hKN hAM hA hA7 hc hcov)
    exact hAN (P2251j.le_of_calNOf hN (hX.trans hYN) hAT)
  · exact uc22p2251j_false_of_isL3_r920odd D hx he hk h847 h920 hK h3 inf_le_left hcov1 hY hYN hAT
      hAN

end CFSG.LocalAnalysis.UniquenessCase.UC22
