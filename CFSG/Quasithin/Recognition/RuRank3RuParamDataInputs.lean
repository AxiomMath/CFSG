module

public import CFSG.Quasithin.Recognition.RuRank3RuGraphData
public meta import CFSG.Quasithin.Recognition.RuRank3RuGraphData
public meta import CFSG.Quasithin.Recognition.RuRank3TitsSyl
public meta import CFSG.Sporadic.Schreier.RuOrbit
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Quasithin.RuRank3

open CFSG.Monster.B.Co2.Native

@[expose] def ruCntD (ti : Array ℕ) : ℕ :=
  (List.range 4060).countP fun x => (ruQLab[x]! == ruQLab[1]!) && ruRowA ti x

end CFSG.Quasithin.RuRank3
