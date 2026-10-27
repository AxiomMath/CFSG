module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreMarked

import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreAmbient
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreCent
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreF4
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreNormF4
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreTableExc

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement


theorem excUntwModelFrame_F4_of_inside (hI : ExcCoreInside 0 .F4) : ExcUntwModelFrame 0 .F4 :=
  excUntwModelFrame_of_lang (Or.inl ⟨rfl, rfl⟩)
    (excLangModelFrame_of_core excCoreDatum_F4 excCoreOccurs_F4 excCoreMarked_F4 excCoreCent_F4 hI
      excCoreNormalizer_F4 excCoreAmbient_F4)

theorem excUntwModelFrame_E7_of_inside (hI : ExcCoreInside 4 .E7) : ExcUntwModelFrame 4 .E7 :=
  excUntwModelFrame_of_lang (Or.inr (Or.inl ⟨rfl, rfl⟩))
    (excLangModelFrame_of_core excCoreDatum_E7 (excCoreOccurs (Or.inr (Or.inl rfl)) (by decide))
      (excCoreMarked (Or.inr (Or.inl rfl)) (by decide)) excCoreCent_E7 hI excCoreNormalizer_E7
      excCoreAmbient_E7)

theorem excUntwModelFrame_E8_of_inside (hI : ExcCoreInside 5 .E8) : ExcUntwModelFrame 5 .E8 :=
  excUntwModelFrame_of_lang (Or.inr (Or.inr ⟨rfl, rfl⟩))
    (excLangModelFrame_of_core excCoreDatum_E8 (excCoreOccurs (Or.inr (Or.inr rfl)) (by decide))
      (excCoreMarked (Or.inr (Or.inr rfl)) (by decide)) excCoreCent_E8 hI excCoreNormalizer_E8
      excCoreAmbient_E8)

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
