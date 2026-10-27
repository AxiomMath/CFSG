module

public import CFSG.RankThree.PartTwo.Sec21.FF84KF1Holds
public import CFSG.RankThree.PartTwo.Sec21.FF84KSOutHolds
public import CFSG.RankThree.PartTwo.Sec21.FF84S3Final
public import CFSG.RankThree.PartTwo.Sec21.FF84S35C3
public import CFSG.RankThree.PartTwo.Sec21.FF84S3A10

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

theorem ff84_2_3
    : FF84_2_3 := ff84_2_3_of ff84KF1_holds ff84KSOut_holds

section S3

theorem ff84_3_3
    : FF84_3_3 := ff84_3_3_of_K ff84KF1_holds ff84KSOut_holds

theorem ff84_3_4
    : FF84_3_4 := ff84_3_4_of_K ff84KF1_holds ff84KSOut_holds

theorem ff84_3_5
    : FF84_3_5 := ff84_3_5_of_A10 S3.A10_maxE0 ff84_3_1 ff84_3_3 ff84_3_4

end S3

end CFSG.RankThree.PartTwo.Sec21.FF84
