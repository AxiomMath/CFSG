module

public import CFSG.RankThree.PartTwo.Sec21.FF84S31
public import CFSG.RankThree.PartTwo.Sec21.FF84S32
public import CFSG.RankThree.PartTwo.Sec21.FF84S34

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84


theorem ff84_3_2_of_A7 (hA7 : S3.A7TauStmt) (hKF1 : FF84KF1) (hKS : FF84KSOut) : FF84_3_2 :=
  ff84_3_2_of (S3.ff84_3_1_of_A7 hA7) hKF1 hKS

theorem ff84_3_3_of_A7 (hA7 : S3.A7TauStmt) (hKF1 : FF84KF1) (hKS : FF84KSOut) : FF84_3_3 :=
  ff84_3_3_of (ff84_3_2_of_A7 hA7 hKF1 hKS)

theorem ff84_3_4_of_A7 (hA7 : S3.A7TauStmt) (hKF1 : FF84KF1) (hKS : FF84KSOut) : FF84_3_4 :=
  ff84_3_4_of (S3.ff84_3_1_of_A7 hA7) (ff84_3_3_of_A7 hA7 hKF1 hKS)

end CFSG.RankThree.PartTwo.Sec21.FF84
