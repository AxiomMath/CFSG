module

public import CFSG.RankThree.PartOne.KF.R2Final
public import CFSG.RankThree.PartOne.KF.R3Final
public import CFSG.RankThree.PartOne.KF.R4Final
public import CFSG.RankThree.PartOne.KF.R56Final
public import CFSG.RankThree.PartOne.KF.R7Final
public import CFSG.RankThree.PartOne.KF.R8Final
public import CFSG.RankThree.PartOne.KF.R9Final
public import CFSG.RankThree.PartOne.KF.R10Final
public import CFSG.RankThree.PartOne.KF.R11Final
public import CFSG.RankThree.PartOne.KF.R12Final

public section

namespace CFSG.RankThree.PartOne

theorem kf123Rows
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ r : ℕ, 1 ≤ r → r ≤ 12 → r ≠ 11 → KF123Row r := by
  intro r h1 h2 h3
  interval_cases r
  · exact kf123Row1
  · exact kf123Row2
  · exact kf123Row3
  · exact kf123Row4
  · exact kf123Row5
  · exact kf123Row6
  · exact kf123Row7
  · exact kf123Row8
  · exact kf123Row9_of_multipliers hGA
  · exact kf123Row10
  · exact absurd rfl h3
  · exact kf123Row12

theorem kf123NTRows
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ r : ℕ, 1 ≤ r → r ≤ 12 → r ≠ 11 → KF123NTRow r := by
  intro r h1 h2 h3
  interval_cases r
  · exact kf123NTRow1
  · exact kf123NTRow2
  · exact kf123NTRow3
  · exact kf123NTRow4
  · exact kf123NTRow5
  · exact kf123NTRow6
  · exact kf123NTRow7
  · exact kf123NTRow8
  · exact kf123NTRow9_of_multipliers hGA
  · exact kf123NTRow10
  · exact absurd rfl h3
  · exact kf123NTRow12

theorem kf123_of_classify
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hc : KF123Classify) : KF123 :=
  kf123_of_rows hc (kf123Rows hGA) kf123Row11

theorem kf123NoTransvection_of_classify
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hc : KF123Classify) : KF123NoTransvection :=
  kf123NoTransvection_of_rows hc (kf123NTRows hGA) kf123NTRow11

end CFSG.RankThree.PartOne
