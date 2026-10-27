module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangRest12RegSplitTorAUniv12
public import CFSG.LocalAnalysis.StandardType.GGNbrLangRegNTUnivHolds

public section

namespace CFSG.StandardType

theorem ggNbrLangAxisOn_rest12_of_univ12
    (hZ : KGCenterCoprimeInput) (hpc : GGRawPCyclicOn GGNotD4Three)
    (h : GGNbrLangRest12RegSplitTorAUniv12) : GGNbrLangAxisOn GGNbrLangRest12Label := by
  have hLT := kgLangTorusNTOn_of_univ hZ (fun _ _ h => h.1) h.1
  refine ((ggNbrLangAxisOn_of_torusOn (ggNbrLangTorusAxisOn_of_kgNT hpc hLT)).or
    (ggNbrLangAxisOn_rest12NonReg_of_rank (ggNbrLangAxisOn_typeARank_of_kg h.2.1) h.2.2)).mono ?_
  intro p lab hS
  by_cases hr : GGNbrLangRegLabel p lab
  · exact Or.inl ⟨hr, hS⟩
  · exact Or.inr ⟨hS, hr⟩

end CFSG.StandardType
