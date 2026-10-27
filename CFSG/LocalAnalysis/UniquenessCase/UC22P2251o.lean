module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3L3
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251n
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251K
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09d
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Opp
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251j
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251i

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9 (R920odd)

variable {G : Type} [Group G] [Finite G]

theorem uc22p2251j_false_of_isL3E3 (D : Data G) (hk : D.k = 1) (h847 : R847E3L3 D)
    (h920 : R920odd D) {K Y H : Subgroup G} (hK : K ∈ calC D.M)
    (hKn : (K.subgroupOf D.M).Normal) (hL3 : IsL3 (Bar2 K) 1) (hYK : Y ≤ K)
    (hcov : K = Y ⊔ pCoreOf 2 K) (hY : Nonempty (Bar2 Y ≃* Bar2 K)) (hYH : Y ≤ H)
    (hHT : H ≠ ⊤) (hHM : ¬ H ≤ D.M) : False := by
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
  have hq2 : Nat.card A' ≠ 2 := by
    intro h
    have h1 := Nat.odd_iff.1 hA'o
    omega
  exact hA'N (h847 K hK hKn hL3 A' (hA'Y.trans hYK) hA'p hq2)

theorem s22_5_1K1_of_inputsE3 (D : Data G) (Ch : Choice2011 G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h33 : S22_3_3 D Ch) (h119 : R119W D) (h17 : S21_17 D Ch)
    (h211 : S21_1 D Ch) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (h847 : R847E3L3 D)
    (h920 : R920odd D) (h923 : F09.R923K1 D) (h2112 : S21_12 D Ch) : S22_5_1K1 D Ch := by
  intro hk hH c m Nb hNb i
  by_contra hbad
  obtain ⟨K, hK, hKb, ⟨eK⟩, hbs, hKn⟩ :=
    uc22p2251b_exists_bad D hx h61 h119 h17 hH c.toCtx22 hNb hbad
  have hKM : K ≤ D.M := hK.1.le
  have hKN : D.M ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hKM).1 hKn
  obtain ⟨A, hAB, hA, hA7, hAN, hAT, hc⟩ :=
    uc22p2251h_exists_A D Ch hH c.toCtx21 hk (hn3 hH _) h2112 hK hbs
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
    have hN := h923 hk K hK hKM hKN ⟨e5⟩
      (uc22p2251j_uniqueMax D Ch h211 hH c.toCtx21 hk hKM hKN e5)
      (Opp 3 (K ⊓ centralizer (A : Set G))) (PartTwo.close16_opp_idem 3 _)
      (hX.trans inf_le_left) hcov
      (uc22p2251i_r923_hyp D Ch h33 hH c hNb hi hK hKb hKN hAM hA hA7 hc hcov)
    exact hAN (P2251j.le_of_calNOf hN (hX.trans hYN) hAT)
  · exact uc22p2251j_false_of_isL3E3 D hk h847 h920 hK hKn h3 inf_le_left hcov1 hY hYN hAT hAN

@[expose] def S22_5_1R3K2 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx22c D Ch, ∀ (m : ℕ) (Nb : Fin m → Subgroup (MBar D.M D.U)),
    NbarSplit D Nb → ∀ i, D.k ≠ 1 → (∀ p ∈ D.sig, p ∣ Nat.card ↥(Nb i)) →
      ∃ n : ℕ, IsL2Ev ↥(Nb i) n ∧ n ≠ 2

theorem s22_5_1R3_of_s22_5_1R3K2 {D : Data G} {Ch : Choice2011 G} (h1 : S22_5_1K1 D Ch)
    (h2 : S22_5_1R3K2 D Ch) : S22_5_1R3 D Ch := by
  intro hH c m Nb hNb i hi
  by_cases hk : D.k = 1
  · exact h1 hk hH c m Nb hNb i
  · exact h2 hH c m Nb hNb i hk (hi.resolve_left hk)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
