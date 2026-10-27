
module

public import CFSG.Quasithin.Recognition.RuRank3RuGraphDataBase
public import CFSG.Quasithin.Recognition.RuRank3TitsClsBase
public import CFSG.Sporadic.Schreier.TitsGraphCheck
public meta import CFSG.Quasithin.Recognition.RuRank3RuGraphDataBase
public meta import CFSG.Quasithin.Recognition.RuRank3TitsClsBase
public meta import CFSG.Quasithin.Recognition.RuRank3TitsSyl
public meta import CFSG.Sporadic.Schreier.TitsGraphCheck
public meta import CFSG.Sporadic.Schreier.RuOrbit
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Quasithin.RuRank3

open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

@[expose] def ruCnt (ti : Array ℕ) : ℕ :=
  (List.range 4060).countP fun x => ruInS x && ruRowA ruTI1 x && ruRowA ti x

@[expose] def ruCountOK (j : ℕ) : Bool :=
  let a := ruTreeArr ruDArr[j]!
  let ti := invCand 4060 a
  isInvA 4060 a ti && ((ruCnt ti == 512) == (titsNbr[0]!).contains j)

@[expose] def ruW : Array ℕ :=
  #[1648, 319, 495, 1445, 265, 189, 402, 552, 1115, 1710, 1612, 261, 1136, 907, 956, 1712,
    1628, 491, 326, 753]

@[expose] def ruWTI : Array (Array ℕ) := ruW.map fun j => ruTI ruDArr[j]!

@[expose] def ruFP (x : ℕ) : ℕ :=
  ((List.range 20).map fun i => ruRowA ruWTI[i]! x).foldl (fun acc b => 2 * acc + b.toNat) 0

@[expose] def ruFPArr : Array ℕ := Array.ofFn (n := 4060) fun x => ruFP x

@[expose] def titsK0Gens : Array (Array ℕ) := Array.ofFn (n := 3) fun i => titsK0Strong[i.val]!

@[expose] def titsK0Lab : Array ℕ := orbLab 1755 titsK0Gens

end CFSG.Quasithin.RuRank3
