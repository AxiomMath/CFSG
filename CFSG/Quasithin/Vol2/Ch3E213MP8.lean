module

public import CFSG.Quasithin.Vol2.Ch3E213MOL6

public section

namespace CFSG.Quasithin.Ch3E213M

theorem pkgOddL3_of (hA : OL.KFactL3U3OuterInv) (hB : OL.KFactL33NoQuadFour) : PkgOddL3 := by
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

end CFSG.Quasithin.Ch3E213M
