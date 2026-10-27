module

public import CFSG.Quasithin.Background.SimsE215KF1Defs
public import CFSG.GH74.GLS.IVK.L2.ExistNotation
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6Over
public import CFSG.Quasithin.Vol2.Ch3E213MOL6

public section

namespace CFSG.Quasithin.SimsE2.KF1

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch3E213M

theorem pkgOddSingleKF1 : PkgOddSingleKF1 := by
  intro G _ _ H T M V K hS hC2 p e hp hp3 he _ hpsl hMK hAut
  refine (OS.false_of_oddSingle GH74.GLS.IVK.ivk_1_2_general GH74.GLS.IVK.ivk_1_3a
    GH74.GLS.IVK.ivk_1_3b ?_ hS hC2 hp hp3 he hpsl hMK hAut).elim
  intro _ _ _ hF h11 _ _ _ e _ hu
  exact GH74.GLS.IVK.Proofs2.isCoatom_centralizer_of_inner hF h11 e hu

theorem pkgOddL3KF1_of (hA : OL.KFactL3U3OuterInv) (hB : OL.KFactL33NoQuadFour) :
    PkgOddL3KF1 := by
  intro G _ _ H T M V K hS hC2 p hp hp2 hK hMK
  exfalso
  by_cases hp3 : p = 3
  · subst hp3
    rcases hK with ⟨h1, -⟩ | ⟨-, hL, -⟩
    · norm_num at h1
    · exact OL.false_of_three hB hS hC2 hL hMK
  · have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      have h4 : p ≠ 4 := by
        rintro rfl
        norm_num at hp
      omega
    exact OL.false_of_ge5 hA hS hC2 hp hp5 (hK.imp (fun h => h) (fun h => ⟨h.1, h.2.1⟩)) hMK

end CFSG.Quasithin.SimsE2.KF1
