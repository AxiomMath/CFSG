module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirteenCaseOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirteenCaseRee
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirteenCaseFun
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupProofsA
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsL2Rank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81 CFSG.Quasithin
open CFSG.SignalizerFunctorTheorem.McBride
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem gap17_13_structure_remaining_holds (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) (h9 : R17_9At D V₀ V L r q hC)
    (hRee : K_ReeSylowGeneration) (hFunComm : K_FunCommute)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hNotL2 : K_LieModelNotL2) :
    Gap17_13_structure_remaining D V₀ V L r q hC := by
  refine ⟨fun H hH h1 => ?_, fun H hH => ?_⟩
  · by_cases h2 : P17_12_2 q L
    · obtain ⟨K, hK, hKT, -⟩ := delta17_12_case_ree_triple hRee hC h9 hH h1 h2
      exact ⟨K, hK, hKT⟩
    · obtain ⟨K, hK, hKT, -⟩ := delta17_12_case_fun_triple hFunComm hC h9 hH h1 h2
      exact ⟨K, hK, hKT⟩
  · have hT2 : IsPGroup 2 (CFSG.LocalAnalysis.WeakClosure81.barImage H D.T) := by
      rw [CFSG.LocalAnalysis.WeakClosure81.barImage]
      exact IsPGroup.map D.sylowM.isPGroup.comap_subtype _
    obtain ⟨K, hK, hKT, hcore⟩ : ∃ K : Subgroup (Bar2 H), CFSG.IsComponent K ∧
        orbitClosure K (CFSG.LocalAnalysis.WeakClosure81.barImage H D.T) ⊔
          CFSG.LocalAnalysis.WeakClosure81.barImage H D.T = ⊤ ∧
        OddComponentShapeCore q (↥K ⧸ Subgroup.center ↥K) := by
      by_cases h1 : P17_12_1 r q L
      · exact delta17_12_case_one_triple hO hNotL2 hC h9 hH h1
      · by_cases h2 : P17_12_2 q L
        · exact delta17_12_case_ree_triple hRee hC h9 hH h1 h2
        · exact delta17_12_case_fun_triple hFunComm hC h9 hH h1 h2
    exact hasOddComponentShapes_top_of_component hK hT2 hKT hcore


theorem seventeen_thirteen_of_kgroups (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) (h9 : R17_9At D V₀ V L r q hC)
    (hFunComm : K_FunCommute)
    (h43c : W3Lem45_2Chief) (h410 : W4Lem4_10) (h411 : W4Lem4_11Prime) :
    R17_13At D (fundPred q) V₀ V L r q hC :=
  seventeen_thirteen_of_inputs D V₀ V L r q hC h9 k_ReeSylowGeneration_holds
    k_FunNonempty_holds h43c h410
    CFSG.ComponentClassification.AutL2Facts.cfAutL2Rank
    CFSG.ComponentClassification.AutL2Facts.cfL2Rank
    h411
    (gap17_13_structure_remaining_holds D V₀ V L r q hC h9 k_ReeSylowGeneration_holds hFunComm
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput k_LieModelNotL2_holds)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
