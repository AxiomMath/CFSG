module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Defs
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Iso

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.GH74.GLS (InChev2)
open scoped commutatorElement Pointwise

theorem w135_alt_case
    (h86 : W4Lem8_6) (hAt : W4Lem13_5AtChev2)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hctx : Is135Context Y L) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3)
    (hZ : Subgroup.center ↥L = ⊥)
    (hAlt : ∃ n : ℕ, 5 ≤ n ∧ Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin n))) :
    W4Lem13_5Concl W Y L t := by
  obtain ⟨n, hn5, ⟨e⟩⟩ := hAlt
  have hL : IsAlt ↥L n :=
    ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e⟩
  by_cases h5 : n = 5
  · subst h5
    exact hAt W hW Y L t hctx htY ht2 hm (w135_inChev2_of_alt_five ⟨e⟩)
  by_cases h6 : n = 6
  · subst h6
    exact hAt W hW Y L t hctx htY ht2 hm (w135_inChev2_of_alt_six ⟨e⟩)
  by_cases h8 : n = 8
  · subst h8
    exact hAt W hW Y L t hctx htY ht2 hm (w135_inChev2_of_alt_eight ⟨e⟩)
  have hn : n = 7 ∨ 9 ≤ n := by omega
  rcases h86 W hW Y L t n hctx.2.2.1 hctx.2.2.2.1 hL hn hctx.2.2.2.2.2 htY ht2 hm with
    ⟨h7, h4, -⟩ | hnat
  · subst h7
    exact W4Lem13_5Concl.of_alt_seven ⟨hL, h4⟩
  · exact W4Lem13_5Concl.of_alt ⟨n, hL, hnat⟩

end CFSG.LocalAnalysis.WeakClosure81
