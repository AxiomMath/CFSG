module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveResDispatch
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRegionDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

theorem ggSecFiveWeylRest5Res_of_rows
    (hLevi : GGSecFiveLeviData) (hA : GGSecFiveDataResAt (fun M => GGIsWeylMatrixA M))
    (hB : GGSecFiveDataResAt (fun M => GGIsWeylMatrixB M))
    (hD : GGSecFiveDataResAt (fun M => GGIsWeylMatrixD M))
    (hE : GGSecFiveDataResAt (fun M => GGIsWeylMatrixE M))
    (hF : GGSecFiveDataResAt (fun M => GGIsWeylMatrixF4 M))
    (hG : GGSecFiveDataResAt (fun M => GGIsWeylMatrixG2 M)) :
    GGSecFiveWeylRest5Res :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ hR hW _ _ hNotReg =>
      ggSecFiveData_res_of_dataRes hLevi hA hB hD hE hF hG hR hW hNotReg,
    fun _ _ _ _ _ _ _ _ _ _ hR hW _ _ _ hNotReg =>
      ggSecFiveData_res_of_dataRes hLevi hA hB hD hE hF hG hR hW hNotReg,
    fun _ _ _ _ _ _ _ _ _ _ hR hW _ hNotReg =>
      ggSecFiveData_res_of_dataRes hLevi hA hB hD hE hF hG hR hW hNotReg,
    fun _ _ _ _ _ _ _ _ _ _ hR hW _ hNotReg =>
      ggSecFiveData_res_of_dataRes hLevi hA hB hD hE hF hG hR hW hNotReg,
    fun _ _ _ _ _ _ _ _ _ _ hR hW _ hNotReg =>
      ggSecFiveData_res_of_dataRes hLevi hA hB hD hE hF hG hR hW hNotReg⟩

end CFSG.StandardType

end
