module

public import CFSG.RankThree.PartTwo.Sec13.Item138ProofMain
public import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega
public import CFSG.RankThree.PartTwo.Sec13.Item138ProofPGL
public import CFSG.RankThree.PartTwo.Sec13.Item138ProofSylow
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.Asc83Table.Automizer
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec6.Statements
import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem item138N_of_main (h132 : Item132) (hset : Sec17.Item13Setup) (hMain : Item138MainN)
    (hS : Item138SN) : Item138N :=
  rank3II_13_8N_of_three_steps item138ExistsN hMain (item138OmegaN_of h132 hset hS)

theorem item138N_of (h132 : Item132) (hset : Sec17.Item13Setup) (hPGL : Item138PGLN)
    (hSyl : Item138SylowN) (hS : Item138SN) : Item138N :=
  item138N_of_main h132 hset (item138MainN_of hPGL hSyl) hS

theorem item138N_of_outer (h132 : Item132) (hset : Sec17.Item13Setup) (hout : Item138OuterN)
    (hH3 : Item138SylHN) (hS : Item138SN) : Item138N :=
  item138N_of h132 hset (item138PGLN_of hout) (item138SylowN_of hH3) hS

end CFSG.RankThree.PartTwo.Sec13
