module

public import CFSG.Monster.AxisCount.BabyIdentCheck0
public import CFSG.Monster.AxisCount.BabyIdentCheck1
public import CFSG.Monster.AxisCount.BabyIdentCheck2

public section

namespace CFSG.Monster.AxisCount.Baby

theorem orbitIdent_all :
    ∀ j, j < 10 → OrbitIdent j := by
  intro j hj
  interval_cases j
  · exact orbitIdent_0
  · exact orbitIdent_1
  · exact orbitIdent_2
  · exact orbitIdent_3
  · exact orbitIdent_4
  · exact orbitIdent_5
  · exact orbitIdent_6
  · exact orbitIdent_7
  · exact orbitIdent_8
  · exact orbitIdent_9

end CFSG.Monster.AxisCount.Baby
