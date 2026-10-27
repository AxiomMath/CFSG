module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Main50

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Four

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]


theorem r6_38_dataOfSetup4 (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G)
    (S : Setup4 G) : UC6.R6_38 (UC6.dataOfSetup4 hS hU S) := by
  have hstd : Sigma23Std (UC6.dataOfSetup4 hS hU S) := sigma23Std_ofSetup4 hS hU S
  have h61 : UC6.R6_1 (UC6.dataOfSetup4 hS hU S) := UC6.r6_1_dataOfSetup4 hS hU S
  have hsp : Sigma2Print (UC6.dataOfSetup4 hS hU S) :=
    sigma2Print_ofSetup4 hS hU S
      (frob4_of_frob4Prime (frob4Prime_holds frobKFacts_holds hS hU S))
  exact UC6.r6_38_of_sigma23_dataOfSetup4 hS hU S
    (uc22p22q_r6_38_23_of_print _ hstd h61 (UC6.r6_11Used_of_sig3_eq_empty rfl) hsp
      (uc22p22q_r613ident_of _ hstd h61 hsp) (r613cent_ofSetup4 hS hU S))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Four
