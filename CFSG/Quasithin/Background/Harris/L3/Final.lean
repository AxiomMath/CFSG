module

public import CFSG.Quasithin.Background.Harris.L3.RankInputs
public import CFSG.Quasithin.Background.Harris.L3.Ident
public import CFSG.Quasithin.Background.Harris.L3.IdentCase8

public section

namespace CFSG.Quasithin.G11.Harris.L3

theorem oneCompFor_famL3 : OneCompFor FamL3 :=
  oneCompFor_famL3_of case8_holds case17_holds notSelfDual_holds rankSharp_holds rankCrude_holds
    rankTwo_holds

theorem oneCompFor_famCoverSL3Two : OneCompFor FamCoverSL3Two :=
  oneCompFor_famCoverSL3Two_of case8_holds case17_holds notSelfDual_holds rankSharp_holds
    rankCrude_holds rankTwo_holds

end CFSG.Quasithin.G11.Harris.L3
