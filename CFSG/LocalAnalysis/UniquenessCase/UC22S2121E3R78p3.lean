module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229R78p3
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229R78p3Setup4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Sec7Core4 StronglyEmbeddedThree)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)

variable {G : Type} [Group G] [Finite G]

theorem r7_8R3p3_dataOfSetup (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (hK3 : StronglyEmbeddedThree)
    (hS : Standing G) (hUC : rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G) :
    UC22.R7_8R3p3 (dataOfSetup hS S) := by
  intro H P D₀ hH hP hD₀ hr
  obtain ⟨-, -, hsp, hHt, hHM, h2⟩ := hH
  obtain ⟨hpow, hMN, hirr⟩ := Sec7Core4.r7_8p3_of_config hG3 hRee hK3
    (Sec7Core4.ofThree hS S.M S.witness.maxLocal 3 Nat.prime_three (by norm_num) hsp
      (normalizer_le_of_agl81TheoremC hUC hC S Nat.prime_three (by norm_num) hsp))
    rfl ⟨hHt, hHM, h2⟩ hr hP
  subst hD₀
  rw [CFSG.RankThree.PartOne.CTP.omegaOne_eq_of_pow_eq_one hpow]
  refine ⟨hpow, hMN, fun W hFW hWP hWN => ?_, rfl⟩
  obtain rfl | rfl := hirr W hWP hWN
  · exact Or.inl (le_bot_iff.mp hFW).symm
  · exact Or.inr rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
