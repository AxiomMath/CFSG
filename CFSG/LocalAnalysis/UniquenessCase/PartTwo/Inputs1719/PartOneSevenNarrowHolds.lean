module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOneSevenNarrow
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R78Five.OfConfig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.Setup4Core
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneThree
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.Fstar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.Bad
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (Sec7Core4 StronglyEmbeddedFive BadNoStrongThree)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

variable {G : Type} [Group G] [Finite G]

theorem r7_8At5_dataOfSetup
    (hId : CFSG.AGLEmbedding.KFactSmallIdent) (hLie : CFSG.AGLEmbedding.KFactOneLieIdent)
    (hCyc : CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact)
    (hIrr : CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.KFactStepThreeIrred)
    (hSz : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 →
      CFSG.AGLEmbeddingD2.D2TransLocalAt (.lie d) fun q => q = 5)
    (hT : CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TitsFacts)
    (hM : CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.McLFacts)
    (hSE : StronglyEmbeddedFive) (hS : Standing G) (hUC : rankThreeUC G)
    (hC : AGL81TheoremC G) (S : Setup G) :
    R7_8At5 (PartTwo.Three.dataOfSetup hS S) := by
  intro H P D₀ h7 hP hD₀
  subst hD₀
  let k : Sec7Core4 G := Sec7Core4.ofThree hS S.M S.witness.maxLocal 5 h7.1 h7.2.1 h7.2.2.1
    (PartTwo.Three.normalizer_le_of_agl81TheoremC hUC hC S h7.1 h7.2.1 h7.2.2.1)
  have hH : k.Config H :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.config_of_sec7Hyp k h7 rfl
  have hno := k.kIDExcluded_of_evenRank_le_three (le_of_eq hS.rank)
  have h75 := k.step75 (le_refl 5) hSE
  have h63 := PartTwo.Three.r6_3_dataOfSetup hS hUC hC S
  rcases k.r7_8At5_of_config hId hLie hCyc hIrr hSz hT hM rfl hH
      (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.not_isFi22_of_kIDExcluded
        k hno h75 hH)
      (fun d hd ⟨e⟩ => Sec7Core4.fieldExponent_eq_one_of_r6_3 _ h63 k rfl h7 hd e) hP with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem r7_8At5_dataOfSetup4
    (hId : CFSG.AGLEmbedding.KFactSmallIdent) (hLie : CFSG.AGLEmbedding.KFactOneLieIdent)
    (hCyc : CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact)
    (hIrr : CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.KFactStepThreeIrred)
    (hSz : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 →
      CFSG.AGLEmbeddingD2.D2TransLocalAt (.lie d) fun q => q = 5)
    (hT : CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TitsFacts)
    (hM : CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.McLFacts)
    (hSE : StronglyEmbeddedFive) (hB : BadNoStrongThree) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma) (hPart : PartIAt S.M) :
    R7_8At5 (UC6.dataOfSetup4 hS hU S) := by
  intro H P D₀ h7 hP hD₀
  subst hD₀
  let k : Sec7Core4 G :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.setup4Core hS hU S hPart 5 h7.1
      h7.2.1 h7.2.2.1
  have hH : k.Config H :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.config_of_sec7Hyp k h7 rfl
  have hno := CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.kIDExcluded_of_setup4 hU S
    hMS hB k rfl (le_refl 5)
  have h75 := k.step75 (le_refl 5) hSE
  have h63 := UC6.r6_3_dataOfSetup4 hS hU S hPart.1
  rcases k.r7_8At5_of_config hId hLie hCyc hIrr hSz hT hM rfl hH
      (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.not_isFi22_of_kIDExcluded
        k hno h75 hH)
      (fun d hd ⟨e⟩ => Sec7Core4.fieldExponent_eq_one_of_r6_3 _ h63 k rfl h7 hd e) hP with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
