module

public import CFSG.LocalAnalysis.StandardType.GGExcCompSLMarking
public import CFSG.LocalAnalysis.StandardType.GGTorsionExcDefs
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGTorsionTwF4Card
import CFSG.LocalAnalysis.StandardType.GGExcCompSLLen

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.LangRat

theorem ggExcNoF4Known_of_lang
    (hF : LangRatCompFieldLenSL) : GGExcNoF4Known := by
  intro p X _ _ hX δ J hdat hJ
  have hFD := ggTorsion_exc_simplyLaced hF
    (P := fun lab : LargeEvenLabel =>
      lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
    (fun _ h => h) hdat
  obtain ⟨_labA, _hlabA, _RA, _hRAgrp, _IA, _FA, _θA, _hsA, _hnaA, ⟨_hPA, hfdA⟩, _hMA⟩ :=
    largeEvenMarking_exists_markedModel hFD
  unfold GGCompFieldDataSL at hfdA
  obtain ⟨_m, _hm, hAt⟩ := hfdA
  unfold GGCompFieldAtSL at hAt
  obtain ⟨labF, hlabF, _hcharF, _hdegF, hslF, hhasF, _RF, _hRFgrp, _hMMF, _hφF⟩ := hAt
  obtain ⟨_c, labT, hlabT, hrawT⟩ := largeEvenMarking_markedModel hJ
  have hasJ : GGHasLabel labT (↥J ⧸ Subgroup.center ↥J) := by
    refine largeEvenRawDatum_mono ?_ hrawT
    intro R _ I F h
    obtain ⟨-, -, θ, -⟩ := h
    exact ⟨θ⟩
  obtain ⟨_RT, _hRTgrp, _IT, _FT, _hsT, _hnaT, _θT, htagT, _hMT⟩ :=
    largeEvenRawDatum_exists hrawT
  have hIso : GGLabelIso labT labF :=
    ggLabelRigidInput_holds labT labF (↥J ⧸ Subgroup.center ↥J) hlabT hlabF hasJ hhasF
  have hTtors : GGL45TorsionTag labT := by
    simp only [GGL45TorsionTag]
    exact Or.inr (Or.inl htagT)
  have hEq : labT = labF := eq_of_ggLabelIso_of_torsionTag hIso hTtors
  have hF4 : labF.tag = .F4 := by
    rw [← hEq]
    exact htagT
  exact absurd hslF (by rw [hF4]; simp [GGSLTag])

theorem ggExcNoF4Known_holds
    : GGExcNoF4Known :=
  ggExcNoF4Known_of_lang langRatCompFieldLenSL_holds

end CFSG.StandardType
