module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112a
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

theorem s21_12_of_s21_5_setup4 (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    {Ch : Choice2011 G} (h847 : F08.R847 (UC6.dataOfSetup4 hS hU S))
    (h12a : S21_12a (UC6.dataOfSetup4 hS hU S) Ch) :
    S21_5 (UC6.dataOfSetup4 hS hU S) Ch → S21_12 (UC6.dataOfSetup4 hS hU S) Ch := fun h5 =>
  s21_12_of_s21_12a h5 (r847Four_of_r847 _ h847 (by have := hS.rank; omega))
    (UC6S846.sigmaStd_dataOfSetup4 hS hU S).nonempty h12a

end CFSG.LocalAnalysis.UniquenessCase.UC22
