module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Main50

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]


theorem r6_13_dataOfSetup4 (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) :
    UC6.R6_13 (UC6.dataOfSetup4 hS hU S) := by
  have hstd := sigma23Std_ofSetup4 hS hU S
  have h61 := UC6.r6_1_dataOfSetup4 hS hU S
  have hsp := sigma2Print_ofSetup4 hS hU S
    (frob4_of_frob4Prime (frob4Prime_holds frobKFacts_holds hS hU S))
  have hcent := r613cent_ofSetup4 hS hU S
  exact uc22p22q_r6_13_of_print _ hstd h61 hsp (uc22p22q_r613ident_of _ hstd h61 hsp) hcent
    (uc22p22q_r613aut_of _ hstd h61 hsp hcent)

end CFSG.LocalAnalysis.UniquenessCase.UC22
