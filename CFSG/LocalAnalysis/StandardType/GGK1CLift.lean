module

public import CFSG.LocalAnalysis.StandardType.GGK1CDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldSympMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnSympRed
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpBasic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spEnd IsReciprocalTransversal)
open CFSG.RankThree.PartOne.KCPrimary

theorem ggK1C_exists_lift {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (φ : MulAut (StatedProj (StatedSp r K)))
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K r)) (LargeEvenGSpSet K r))
    (hφp : φ ^ p = 1) :
    ∃ x : ↥(StatedSp r K), x ^ p = 1 ∧ MulAut.conj (proj r K x) = φ := by
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨A, hA⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GFldSympMark.exists_conjAut_eq_of_mem_matConjImage hφ
  obtain ⟨x, hx⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympRed.exists_conjAut_eq_conj h2 A
  have hxφ : MulAut.conj (proj r K x) = φ := hx.symm.trans hA
  refine ⟨x, ?_, hxφ⟩
  refine CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympRed.pow_eq_one_of_conj_pow_eq_one h2 ?_ ?_
  · exact ggNbrLSideSp_center hK
  · rw [← hx, hA]; exact hφp

end CFSG.StandardType

end
