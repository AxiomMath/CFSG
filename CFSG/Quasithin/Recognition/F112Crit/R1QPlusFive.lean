module

public import CFSG.Quasithin.Recognition.F112Crit.APrime.R1QCenterHolds
public import CFSG.Quasithin.Recognition.F112Crit.S3OddThree

public section

namespace CFSG.Quasithin.F112Crit

theorem f112R1QPlus_of_five
    (h5 : S3OddB (5 ≤ ·)) :
    CFSG.Quasithin.H13.F112R1QPlus :=
  f112R1QPlus_of_center_five APrime.r1QCenter_holds h5

theorem dsBPlus_of_sliceS3L2_five
    (hs : CFSG.Quasithin.F112R.F112SliceS3L2 CFSG.Quasithin.F112ConclPredC)
    (h5 : S3OddB (5 ≤ ·)) : CFSG.Quasithin.H13.DSBStatementPlus :=
  CFSG.Quasithin.H13.dsBPlus_of_sliceS3L2_R1QPlus hs (f112R1QPlus_of_five h5)

end CFSG.Quasithin.F112Crit

end
