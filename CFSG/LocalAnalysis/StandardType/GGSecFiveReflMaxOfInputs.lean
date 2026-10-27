module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthExclOfCited
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMPrimeInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCR3OfPump
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCROfInputs
import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxProdHolds
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxStep6
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxFamily
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxBasic
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxSat
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJrOfRootGenL
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxNotG2
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxMain
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxZeroReal
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroOfInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggSecFiveReflMaxInput'_of_inputs
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hPump : GGSecFivePumpReadInput)
    (hFix : GGSecFiveFixInput) (hJA2 : GGSecFiveJA2Input)
    (hUse : ZS.UseInput) (hWit : ZS.WitnessInput)
    (hRT : GGWeylReflTripleInput) (hRQ : GGReflRealizedQFourNbrInput)
    (hTBJ : GGSecFiveTBJTypeD4Input) (hKSL : GGSecFiveOrthKSLInput)
    (hStruct : GGSecFiveOrthD4KStructInput) (hRootGenL : GGSecFiveRootGenLInput)
    (hLev2 : GGSecFiveLevTwoInput') : GGSecFiveReflMaxInput' := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit y K' hnbr
  have hxBs : x ∈ Bs := hcfg.1.1.tableB_facts.2.2.1
  have hCR : GGSecFiveCRInput := ggSecFiveCRInput_of_inputs hL hP hPump
    SecFiveRootRefl.ggSecFiveRootReflInput_holds ggSecFiveCoxProdInput_holds
  have hCR3 : GGSecFiveCR3Input := ggSecFiveCR3Input_of_pump hL hP hPump hRT
  have hJr : GGSecFiveJrInput := ggSecFiveJrInput_of_rootGenL hRootGenL
  have hWeyl : GGSecFiveWeylBranchInput :=
    ggSecFiveWeylBranchInput_of_cited hL hP hPump hFix hJA2 hUse hWit hJr hCR hCR3 hRQ hTBJ hKSL hStruct
  by_cases hC : ∀ b : ↥Bs, (∀ φ ∈ ggAInf p B Bs x L D J, φ b = b) → b = 1
  · exact ggRM_of_witness hcfg.2.2.2
      (ggRM_witness_main hL hP hFix hRootGenL hLev2 hWeyl hcfg hsplit hC) y K' hnbr
  · have hfix := ggRM_zero_fixes_x hFix hcfg hsplit hxBs hC
    by_cases hun : ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
        ∃ t ∈ ggAutomizer K Bs, GGIsReflection p t ∧ ¬ GGRealized p Bs t
    · exact ggRM_of_witness hcfg.2.2.2
        (ggSecFiveCaseZeroInput_of_inputs hL hP hFix hRootGenL G p B Bs x L D J 𝒦 hcfg hsplit hxBs
          hfix hun) y K' hnbr
    · refine ggRM_of_witness hcfg.2.2.2
        (ggRM_witness_zero_realized hL hP hFix hcfg hsplit hxBs hfix ?_) y K' hnbr
      intro y K hK t ht hrefl
      by_contra hnr
      exact hun ⟨y, K, hK, t, ht, hrefl, hnr⟩

end CFSG.StandardType

end
