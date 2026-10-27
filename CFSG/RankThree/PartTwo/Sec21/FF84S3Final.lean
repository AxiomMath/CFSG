module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3Assembly
public import CFSG.RankThree.PartTwo.Sec21.FF84S3A7

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

theorem ff84_3_1 : FF84_3_1 :=
  S3.ff84_3_1_of_A7 S3.A7_tau

theorem ff84_3_3_of_K (hKF1 : FF84KF1) (hKS : FF84KSOut) : FF84_3_3 :=
  ff84_3_3_of_A7 S3.A7_tau hKF1 hKS

theorem ff84_3_4_of_K (hKF1 : FF84KF1) (hKS : FF84KSOut) : FF84_3_4 :=
  ff84_3_4_of_A7 S3.A7_tau hKF1 hKS

end CFSG.RankThree.PartTwo.Sec21.FF84
