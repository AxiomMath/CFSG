module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R1K
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R38T
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R38V
public import CFSG.RankThree.PartTwo.Sec21.FF84KF1Holds
public import CFSG.RankThree.PartTwo.Sec21.FF84KSOutHolds

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF84

theorem kf_fs79Prop2K_of (hKF1 : FF84KF1) (hKS : FF84KSOut) : KF_FS79Prop2K := by
  have hR1K : KF_FS79Prop2OneK := kf_fs79Prop2OneK_of hKF1 hKS
  exact kf_fs79Prop2K_of_local (fs79R34K_of hR1K) (fs79R38K_of hR1K (fs79D1K_of hR1K))
    (fs79R38'K_of hR1K (fs79R34K_of hR1K) (fs79D2K_of hR1K))


theorem kf_fs79Prop2K
    : KF_FS79Prop2K :=
  kf_fs79Prop2K_of ff84KF1_holds ff84KSOut_holds

end CFSG.RankThree.PartTwo.Sec21.FF81
