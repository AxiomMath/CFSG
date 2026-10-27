module

public import CFSG.RankThree.PartTwo.Sec21.FF84S31Bot
public import CFSG.RankThree.PartTwo.Sec21.FF84LemmaFHolds
public import CFSG.RankThree.PartTwo.Sec21.FF84S3A8TJ

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG

theorem ff84_3_1_of_A
    (hA7 : A7TauStmt) (hA8 : A8TJStmt) : FF84_3_1 := by
  intro G _ _ b L B b₁ b₂ h
  have hZ := P_center_dvd_two h
  have hodd := Z_odd lemmaF_holds hA7 hA8 hZ h
  have hX := Z_X_bot lemmaF_holds hA8 hZ h hodd
  exact ⟨hX, Z_center hZ h hX⟩

theorem ff84_3_1_of_A7
    (hA7 : A7TauStmt) : FF84_3_1 :=
  ff84_3_1_of_A hA7 A8_TJ

end CFSG.RankThree.PartTwo.Sec21.FF84.S3
