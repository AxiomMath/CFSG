module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aUDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S214U
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20g
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aUL2
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aF

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem s21_12aFU_of_residual (hE : UC22P20gExcFacts) {D : Data G} {Ch : Choice2011 G}
    (h20_7 : S20_7 D) (h5 : S21_5 D Ch)
    (hCh : ∀ L₀ B₀ : Subgroup G, Choice214U D L₀ B₀ → Ch L₀ B₀)
    (hR2 : S21_12aFR2 D (Choice214U D)) (hR34 : S21_12aFR34 D (Choice214U D)) :
    S21_12aF D (Choice214U D) := by
  intro hH c L hL p hp hp2 hch hfaith
  by_cases hL2 : ∃ f : ℕ, LieModel (BarInf L) .PSL 2 p f
  · obtain ⟨f, hf⟩ := hL2
    by_cases hinn : ∀ b (hb : b ∈ c.B0) (hbN : b ∈ normalizer (L : Set G)),
        inducedBarInfAutHom L ⟨b, hbN⟩ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range
    · exact (uc22s2112u_l2_false h5 hCh hH c (uc22p20g_hn3_of hE D _ h20_7 hH c) hL hp hp2 hf
        hfaith hinn).elim
    · refine hR2 hH c L hL p hp hp2 f hf hfaith ?_
      by_contra hno
      exact hinn fun b hb hbN => Classical.byContradiction fun hb' => hno ⟨b, hb, hbN, hb'⟩
  · exact hR34 hH c L hL p hp hp2 hch (fun f hf => hL2 ⟨f, hf⟩) hfaith

end CFSG.LocalAnalysis.UniquenessCase.UC22
