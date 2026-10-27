module

public import CFSG.LocalAnalysis.StandardType.GGB36Assembly
public import CFSG.LocalAnalysis.StandardType.GGB36StepOneK0
public import CFSG.LocalAnalysis.StandardType.GGB36D4Slice
public import CFSG.LocalAnalysis.StandardType.GGB36JExc
public import CFSG.LocalAnalysis.StandardType.GGB36StepThree

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGB36JNonExcRK : Prop :=
  GGTablePKnownRK fun p n labJ labX => GGRegimeB36J p n labJ labX ∧
    ¬ (labX.tag = .F4 ∨ labX.tag = .E6 ∨ labX.tag = .twE6 ∨ labX.tag = .E7 ∨ labX.tag = .E8)

private theorem ltqFin_excB_of_excBS (h : GGK0ExcBS) : GGK0ExcB := by
  intro p lab hlab hpair Q hQ
  refine largeEvenRawDatum_mono ?_ (h p lab hlab hpair Q hQ)
  rintro R _ I F ⟨hQ, hP⟩
  refine ⟨hQ, ?_⟩
  intro L' _ _ ψ hψ hker hcomm e hep hind
  obtain ⟨D, hV, ha, hb, hc, hd, he, -⟩ := hP L' ψ hψ hker hcomm e hep hind
  exact ⟨D, hV, ha, hb, hc, hd, he⟩

theorem ggNbrTablePNbrInputOnL_b36
    (hT : GGTPNTransferBNoCorners) (h2 : GGE6ThreeI1Rank) (hInn : GGInnerOnD4) (hBS : GGK0ExcBS)
    (hβ : GGE6CoverThreeLocalRank) (hRest : GGB36JNonExcRK) :
    GGNbrTablePNbrInputOnL GGRegimeB36L := by
  have hRE : GGK0CompREMult := ggK0CompREMult_of_excB (ltqFin_excB_of_excBS hBS)
  refine ggNbrTablePNbrInputOnL_b36_of_pieces hT (ggB36StepOne_of_K0REMult hRE) h2
    (ggB36KernelFail_of_transfer hT hInn)
    (GGTablePKnownRK.mono (GGTablePKnownRK.union hRest (ggTablePKnownRK_b36JExc hBS hβ)) ?_)
    (ggTablePKnownR_b36D4E6 (ggK0CompRE_of_mult hRE))
  intro p n labJ labX hJ
  by_cases hexc : labX.tag = .F4 ∨ labX.tag = .E6 ∨ labX.tag = .twE6 ∨ labX.tag = .E7 ∨ labX.tag = .E8
  · exact Or.inr ⟨hJ, hexc⟩
  · exact Or.inl ⟨hJ, hexc⟩

end CFSG.StandardType

end
