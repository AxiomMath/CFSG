module

public import CFSG.Quasithin.Vol2.Ch3E213MP5L
public import CFSG.Quasithin.Vol2.Ch3E215MF

public section

namespace CFSG.Quasithin.Ch3E215M

open Ch3E213M

theorem pkgL3215 :
    PkgL3215 := by
  intro G _ _ H T M V K hS h2 n hn hPSL hD hB
  obtain ⟨T', hT', hP⟩ := pair_of_l3 hS h2 hn hPSL hD hB
  exact e215Concl_of_pair hS hT' hP

end CFSG.Quasithin.Ch3E215M
