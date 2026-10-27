module

public import CFSG.Quasithin.Vol2.Ch12Sec2Inputs
public import CFSG.Quasithin.Background.B5FinS8Core

public section

namespace CFSG.Quasithin.H13

theorem extSqFourAltEight : ExtSqFourAltEight := by
  intro V _ _ _ H U Z hext
  obtain ⟨π, hπ⟩ := hext
  exact ⟨π.comp B5FinS8.alpha, FFModel.RealizesVia.of_surjHom (FFModel.altDn_isActionModel 8) hπ
    B5FinS8.alpha B5FinS8.alpha_surjective B5FinS8.ehat8 B5FinS8.ehat8_surjective
    (fun σ m _ => B5FinS8.qHom_alt σ m.1 m.2) (fun m => B5FinS8.ehat8_ker m)⟩

end CFSG.Quasithin.H13
