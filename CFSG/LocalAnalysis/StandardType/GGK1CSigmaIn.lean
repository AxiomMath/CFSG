module

public import CFSG.LocalAnalysis.StandardType.GGK1CDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldSympMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnSympRed
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpBasic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

theorem ggK1C_centreless_inner {nf r : ℕ} (hnf : 1 ≤ nf) (hr : 1 ≤ r) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ nf) :
    (∀ z : LargeEvenProj (LargeEvenSpGroup K r), (∀ g, g * z = z * g) → z = 1) ∧
      ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K r))
          (LargeEvenGSpSet K r), ∃ s : LargeEvenProj (LargeEvenSpGroup K r),
        φ = MulAut.conj s := by
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  refine ⟨?_, ?_⟩
  · intro z hz
    have hmem : z ∈ Subgroup.center (LargeEvenProj (LargeEvenSpGroup K r)) :=
      Subgroup.mem_center_iff.mpr fun g => (hz g)
    rw [ggNbrLSideSp_center hK] at hmem
    exact Subgroup.mem_bot.mp hmem
  · intro φ hφ
    obtain ⟨A, hA⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GFldSympMark.exists_conjAut_eq_of_mem_matConjImage hφ
    obtain ⟨x, hx⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympRed.exists_conjAut_eq_conj h2 A
    exact ⟨proj r K x, hA.symm.trans hx⟩

end CFSG.StandardType

end
