module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4RankData

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)
open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem rankP2_tab : rankP2.map FF84.tab = rankP2T := by decide +kernel

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
