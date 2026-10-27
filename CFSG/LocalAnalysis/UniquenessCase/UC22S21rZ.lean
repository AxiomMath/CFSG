module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229N
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xa
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rX
public import CFSG.LocalAnalysis.UniquenessCase.UC22Standing22
public import CFSG.LocalAnalysis.UniquenessCase.UCFront78Nar
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rS1
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rS2
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

theorem s21_22Use_of_s21_22U3_U4 (D : Data G) (Ch : Choice2011 G) (st : Standing22 D)
    (hr77 : F07.R77E4 D) (he : 3 < CFSG.Open.evenRank G) (h21EB : S21_21EB D Ch)
    (hB : ∃ c : Ctx21 D Ch, c.B ≠ ⊥) (h8E : S21_8E D Ch) (h9 : S21_9N D Ch) (h17 : S21_17 D Ch)
    (hU3 : S21_22U3 D Ch) (hU4 : S21_22U4 D Ch) : S21_22Use D Ch := by
  intro h1930 c H₁ hH₁ H₂ hH₂ hL hfX
  obtain ⟨c₀, hc₀⟩ := hB
  have hS1 := uc22s21rs1_hinf_commutator_le D st hr77 he hH₁ hH₂
    (fun X h1 h2 hF => hfX X h1 h2 (Or.inl hF))
  have hU3' := hU3 h1930 c H₁ hH₁ H₂ hH₂ hL hfX hS1
  have h21E : S21_21E D Ch := fun h1930' _ hH =>
    h21EB h1930' c₀ hc₀ (uc22s21rs2_hyp2120_of c₀ hH.1 hH.2.1 hU3')
  obtain ⟨L, hLC, hc2, hn⟩ :=
    uc22s21rs2_exists_pair D Ch st.dataExt h21E h8E h9 h17 h1930 he c hS1 hU3'
  exact (hU4 h1930 c H₁ hH₁ H₂ hH₂ hL hfX hS1 hU3' he L hLC hc2 hn).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22
