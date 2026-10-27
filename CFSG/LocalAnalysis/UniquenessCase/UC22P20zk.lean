module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20zj
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20zh
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aF

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

variable {G : Type} [Group G] [Finite G]

theorem uc22pw_ch214U
    (hE : UC22P20gExcFacts) (hu38 : uc22p20oU38Witness)
    (hB : ListBNonabelian) (D : Data G) (h1930 : H1930 D) (h20_7 : S20_7 D) :
    ChoiceExists2011 D (Choice214U D) := by
  intro L hL n hn
  obtain ⟨hn2, h1 | h2 | ⟨K, K₂, t, htT, hK, hK₂, hne, hLK, ht, hsh⟩⟩ :=
    uc22pw_cases hE D h1930 h20_7 hL hn
  · exact uc22pw_ch214U_single D hB h1930 hL.prop h1.1 hn2 (Or.inl h1.2)
  · exact uc22pw_ch214U_single D hB h1930 hL.prop h2.1 hn2 (Or.inr h2.2)
  · exact uc22pw_ch214U_two hu38 D hB h1930 hL.prop hK hK₂ hne hLK htT ht hn2 hsh

theorem s21_12aF_of_choice214U
    (hE : UC22P20gExcFacts)
    (hu38 : uc22p20oU38Witness) (hB : ListBNonabelian) (hO : LieOrderFormulasInput)
    (hThin : PartTwo.ThinList13) (hK : PartTwo.S17.K_LieModelNotL2) {D : Data G} {Ch : Choice2011 G}
    (h20_7 : S20_7 D) (h3 : S21_3 D Ch) (hCh : ∀ L₀ B₀ : Subgroup G, Choice214U D L₀ B₀ → Ch L₀ B₀)
    (hF : S21_12aF D (Choice214U D)) : S21_12aF D Ch :=
  s21_12aF_of_s21_12a (s21_12a_transfer (fun hH => uc22pw_ch214U hE hu38 hB D hH h20_7)
    (s21_12a_of_s21_12aF (s21_3_mono hCh h3) hO hThin hK hF))

end CFSG.LocalAnalysis.UniquenessCase.UC22
