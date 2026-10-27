module

public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoverSetting
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLSmall
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLTorusBridge
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLOutsideTop
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLParity
import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
import CFSG.LocalAnalysis.StandardType.GGTableB

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB

theorem ggTwE6OfOutsideAt_of_ne_one {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      Finite R →
      ∀ (s t : MulAut R) (n : ℕ), s ^ 3 = 1 → s ≠ 1 → t ^ 3 = 1 → s * t = t * s → s ∈ I →
        t ∈ I → 3 ∣ 2 ^ n + 1 →
        ∀ J₁ : Subgroup R, IsComponentOf J₁ (ggFix s) →
          LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ =>
            lab' = ⟨.D, 4, n⟩ ∨ lab' = ⟨.triD4, 0, n⟩ ∨ lab' = ⟨.A, 2, 3 * n⟩ ∨
              lab' = ⟨.twA, 2, 3 * n⟩) →
          ¬ GGOutsideInndiag J₁ t) :
    GGTwE6OfOutsideAt lab := by
  refine (largeEvenLabelAll_and h (largeEvenLabelAll_not_ggOutsideInndiag_ggFix_one hlab)).mono
    fun R _ I _ ⟨hI, h1⟩ hR hna hfin s t n hs3 ht3 hst hsI htI hn J₁ hJ₁ hmark hout => ?_
  rcases eq_or_ne s 1 with rfl | hs1
  · exact absurd hout (h1 hR hna t htI J₁ hJ₁)
  · exact absurd hout (hI hR hna hfin s t n hs3 hs1 ht3 hst hsI htI hn J₁ hJ₁ hmark)

end CFSG.StandardType.SCFourCover

end
