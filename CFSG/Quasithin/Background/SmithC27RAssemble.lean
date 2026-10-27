module

public import CFSG.Quasithin.Background.SmithC27RCaseIMain
public import CFSG.Quasithin.Background.SmithC27RTypeCases

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable (G : Type) [Group G] [Finite G]

@[expose] def ResidueCaseII : Prop :=
  ∀ H R M K : Subgroup G, Hyp27 H R M K → ¬ IsChiBlock2 H K → ¬ IsExcA7Block K →
    ¬ IsSylowTwoOf R (K ⊔ R) → ResidueTypeII R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) →
    C27Three H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))

variable {G}

theorem asc27Residue_of_caseII
    (hC132 : ASInputs.AS_C_1_32) (hA21 : AsA21SQTKSection) (hB51 : AsB51)
    (hI : B5.B51IrrInputs) (hC124 : C124StatementSQTK (G := G)) (hII : ResidueCaseII G) :
    ASC27Residue G := by
  intro H R M K V hyp hK hq hc hn hR hV hnchi hnexc hnS
  subst hV
  have h : Hyp27 H R M K := Hyp27.mk' hyp hK hq hc hn hR
  refine c27Concl_of_parts (c27_one h) (c27_two h) ?_
  rcases residue_cases hA21 hB51 hI hC124 h h.starHyp hnchi hnexc with ⟨hJ, ht⟩ | ht
  · exact three_of_residueTypeI hC132 h h.starHyp hJ hnS ht
  · exact hII H R M K h hnchi hnexc hnS ht

end CFSG.Quasithin.SmithC27
