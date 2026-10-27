module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRk
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVac
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBMeta
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48NbrFieldHolds
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Subgroup

section Certs

theorem ggL48TableBKnownFormsRk_of_rest (h : GGL48TableBKnownFormsRestRk) :
    GGL48TableBKnownFormsRk := by
  have hv : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → GGL48TableBVacLabel p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R I ∧ GGIrredTableB p R I ∧
        GGTorusGenTableB p R I ∧ GGIrredModTableB p R I ∧ GGWPlusTableB p R I :=
    fun p lab hp hlab hs hsm => largeEvenLabelAll_tableBForms_l48Vac hp hlab hsm hs
  obtain ⟨h1, h1r, h2, h3, h3r, h4, h4F, h4r⟩ := h
  refine ⟨fun p lab hp hlab hs hD hrow => ?_, fun p lab hp hlab hs hrow => ?_,
    fun p lab hp hlab hs hD => ?_, fun p lab hp hlab hs hrow => ?_,
    fun p lab hp hlab hs hrow => ?_, fun p lab hp hlab hs hD hF hrow => ?_,
    fun p lab hp hlab hs hF => ?_, fun p lab hp hlab hs hrow => ?_⟩
  · by_cases hsm : GGL48TableBVacLabel p lab
    · exact (hv p lab hp hlab hs hsm).mono fun _ _ _ _ h => h.1
    · exact h1 p lab hp hlab hs hsm hD hrow
  · by_cases hsm : GGL48TableBVacLabel p lab
    · exact (hv p lab hp hlab hs hsm).mono fun _ _ _ _ h =>
        ggCoverPTableBRk_of_coverPTableB _ h.1
    · exact h1r p lab hp hlab hs hsm hrow
  · by_cases hsm : GGL48TableBVacLabel p lab
    · exact (hv p lab hp hlab hs hsm).mono fun _ _ _ _ h => h.2.1
    · exact h2 p lab hp hlab hs hsm hD
  · by_cases hsm : GGL48TableBVacLabel p lab
    · exact (hv p lab hp hlab hs hsm).mono fun _ _ _ _ h => h.2.2.1
    · exact h3 p lab hp hlab hs hsm hrow
  · by_cases hsm : GGL48TableBVacLabel p lab
    · exact (hv p lab hp hlab hs hsm).mono fun _ _ _ _ h =>
        ggTorusGenTableBRk_of_torusGenTableB _ h.2.2.1
    · exact h3r p lab hp hlab hs hsm hrow
  · by_cases hsm : GGL48TableBVacLabel p lab
    · exact (hv p lab hp hlab hs hsm).mono fun _ _ _ _ h => Or.inl h.2.2.2.1
    · exact h4 p lab hp hlab hs hsm hD hF hrow
  · by_cases hsm : GGL48TableBVacLabel p lab
    · exact (hv p lab hp hlab hs hsm).mono fun _ _ _ _ h =>
        ggIrredModTableBRk_of_irredModTableB 5 h.2.2.2.1
    · exact h4F p lab hp hlab hs hsm hF
  · by_cases hsm : GGL48TableBVacLabel p lab
    · exact (hv p lab hp hlab hs hsm).mono fun _ _ _ _ h =>
        Or.inl (ggIrredModTableBRk_of_irredModTableB _ h.2.2.2.1)
    · exact h4r p lab hp hlab hs hsm hrow

end Certs

section Holds

theorem ggL48QuotIOneInput_of_knownFormsRk_holds
    (hsub : GGNbrSubcomponentInput) (hcyc : GGL46CyclicIOneInput)
    (hID : GGBstarInnerDiagLInputOn fun _ _ => True) (h : GGL48TableBKnownFormsRk)
    (hb1 : GGL48F4TwoThreeConfigInput) (hb2 : GGL48TB0TwConfigInputInn) : GGL48QuotIOneInput :=
  ggL48QuotIOneInput_of_knownFormsRk ggL48NbrFieldInput_holds hsub
    (ggRawInnSubgroupInput_of_rawInnField ggRawInnFieldInput_holds) ggLNoncyclicInput_holds hcyc
    hID h hb1 hb2

end Holds

end CFSG.StandardType

end
