module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213HatChk
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24

public section

namespace CFSG.Quasithin.H13.Ch4.HatM

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Quasithin.H13.Ch4.HatChk

@[expose] def parseWord (s : String) : List ℤ :=
  s.toList.map fun ch => if ch = 'a' then 1 else if ch = 'b' then 2 else -2

@[expose] def arr24 (g : Equiv.Perm (Fin 24)) : Array ℕ := Array.ofFn fun i => (g i : ℕ)

@[expose] def m24W (s : String) : Equiv.Perm (Fin 24) := evalCodes [m24gA, m24gB] (parseWord s)

@[expose] def s1WordStrs : List String :=
  ["baBababaBabababaBabaBabababababaBabaBabaBabaBabaBaBabababaBabababaBabaBabababababaBabaBa" ++
     "baBabaBabaBabaBaBababababaBaBabaBaBaBaBabaBababababaBababaBabaBaBababaBabababaBaBaBaBaba" ++
     "baBabaBaBababaBaBaBababababaBabababaBababababababababaBabababaBabaBabababababaBabaBabaBa" ++
     "baBabaBaBabababaBabababaBabaBabababababaBabaBabaBabaBabaBabaBaBababababaBaBabaBaBaBaBaba" ++
     "BababababaBababaBabaBaBababaBaBaBaBaBababababaBaBabaBaBaBaBabaBababababaBababaBabaBaBaba" ++
     "baBabaB",
   "baBababaBabababaBabaBabababababaBabaBabaBabaBabaBabaBaBababababaBaBabaBaBaBaBabaBabababa" ++
     "baBababaBabaBaBababaBabababaBaBaBaBababaBabaBaBababaBaBaBababababaBabababaBabaBabababaBa" ++
     "BabaBaBaBaBabaBababababaBababaBabaBaBababaBaBaBaBaBababababaBaBabaBaBaBaBabaBababababaBa" ++
     "babaBabaBaBabaBaBabababaBabaBabababababaBabaBabaBabaBabaBaBaBaB",
   "babaBaBaBababababaBaBabaBaBaBaBabaBababababaBababaBabaBaBababaBabababaBaBaBaBababaBabaBa" ++
     "BababaBaBaBababababaBabababaBababababababababaBabababaBabaBabababababaBabaBabaBabaBabaBa" ++
     "BaBababaBaBaBaBababaBabaBaBababaBaBaBababababaBabababaBabaBabababaBaBabaBaBaBaBabaBababa" ++
     "babaBababaBabaBaBababaBabababaBaBaBaBababaBabaBaBababaBaBaBababababaBabababaBabaBabababa" ++
     "BaBabaBaBaBaBabaBababababaBababaBabaBaBababaBaBaBaBaBababababaBaBabaBaBaBaBabaBababababa" ++
     "BababaBabaBaBababaBabaB",
   "babaBaBaBababababaBaBabaBaBaBaBabaBababababaBababaBabaBaBababaBabababaBaBaBaBababaBabaBa" ++
     "BababaBaBaBababababaBabababaBabaBabababaBaBabaBaBaBaBabaBababababaBababaBabaBaBabaBaBaba" ++
     "babaBabaBabababababaBabaBabaBabaBabaBaBaBababaBaBaBaBababaBabaBaBababaBaBaBababababaBaba" ++
     "babaBabababababaBababaBaBaBaBababaBabaBaBababaBaBaBababababaBabababaBababababababababaBa" ++
     "bababaBabaBabababababaBabaBabaBabaBabaBaBaBaB",
   "babaBaBaBababababaBaBabaBaBaBaBabaBababababaBababaBabaBaBababaBaBaBaBaBababababaBaBabaBa" ++
     "BaBaBabaBababababaBababaBabaBaBababaBaBaBaBaBababababaBaBabaBaBaBaBabaBababababaBababaBa" ++
     "baBaBabaBaBabababaBabaBabababababaBabaBabaBabaBabaBabaBaBababababaBaBabaBaBaBaBabaBababa" ++
     "babaBababaBabaBaBabaBaBabababaBabaBabababababaBabaBabaBabaBabaBaBabababaBabababaBabaBaba" ++
     "babababaBabaBabaBabaBabaBaBaBababaBaBaBaBababaBabaBaBababaBaBaBababababaBabababaBabababa" ++
     "babaBaB",
   "baBababaBabababaBabaBabababababaBabaBabaBabaBabaBaBaBababaBaBaBaBababaBabaBaBababaBaBaBa" ++
     "babababaBabababaBabababababaBababaBaBaBaBababaBabaBaBababaBaBaBababababaBabababaBabababa" ++
     "babaBababaBaBaBaBababaBabaBaBababaBaBaBababababaBabababaBabaBabababaBaBabaBaBaBaBabaBaba" ++
     "bababaBababaBabaBaBababaBabababaBaBaBaBababaBabaBaBababaBaBaBababababaBabababaBababababa" ++
     "baBaB",
   "BabaBaBaBaBababaBabaBaBababaBaBaBababababaBabababaBabaBabababaBaBabaBaBaBaBabaBababababa" ++
     "BababaBabaBaBababaBabababaBaBaBaBababaBabaBaBababaBaBaBababababaBabababaBabaBabababaBaBa" ++
     "baBaBaBaBabaBababababaBababaBabaBaBababaBaBaBaBaBababababaBaBabaBaBaBaBabaBababababaBaba" ++
     "baBabaBaBabaBaBabababaBabaBabababababaBabaBabaBabaBabaBaBaBababaBaBaBaBababaBabaBaBababa" ++
     "BaBaBababababaBabababaBabababababaBababaBaBaBaBababaBabaBaBababaBaBaBababababaBabababaBa" ++
     "bababababaBaB",
   "babaBaBaBababababaBaBabaBaBaBaBabaBababababaBababaBabaBaBabaBaBabababaBabaBabababababaBa" ++
     "baBabaBabaBabaBaBabababaBabababaBabaBabababababaBabaBabaBabaBabaBaBaBababaBaBaBaBababaBa" ++
     "baBaBababaBaBaBababababaBabababaBababababababababaBabababaBabaBabababababaBabaBabaBabaBa" ++
     "baBaBabababaBabababaBabaBabababababaBabaBabaBabaBabaBaBabababaBabababaBabaBabababababaBa" ++
     "baBabaBabaBabaBaBaBababaBaBaBaBababaBabaBaBababaBaBaBababababaBabababaBabababababaBaB",
   "baBababaBabababaBabaBabababababaBabaBabaBabaBabaBaBabababaBabababaBabaBabababababaBabaBa" ++
     "baBabaBabaBaBaBababaBaBaBaBababaBabaBaBababaBaBaBababababaBabababaBabababababaBababaBaBa" ++
     "BaBababaBabaBaBababaBaBaBababababaBabababaBabababababaBababaBaBaBaBababaBabaBaBababaBaBa" ++
     "BababababaBabababaBabaBabababaBaBabaBaBaBaBabaBababababaBababaBabaBaBababaBabababaBaBaBa" ++
     "BababaBabaBaBababaBaBaBababababaBabababaBababababababababaBabababaBabaBabababababaBabaBa" ++
     "baBabaBabaBaBabababaBabababaBabaBabababababaBabaBabaBabaBabaBaBaBaB"]

@[expose] def p1WordStrs : List String :=
  ["BabaBaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBaba" ++
     "BaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBabababaBaBaBaBaBa" ++
     "BaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababa" ++
     "BaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababa" ++
     "BaBabababaBaBaBaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBa" ++
     "BababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBabababaBaBaBaBaBaBa" ++
     "BaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBa" ++
     "bababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBabababaBaBaBaBaBaBaBaBaBaBaba" ++
     "BabaBabababaBaBabababaBaBabab",
   "BabaBaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBabababaBaBaBaBaBaBaBa" ++
     "BaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBaBa" ++
     "BaBabababaBabaBabaBaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababa" ++
     "BaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababa" ++
     "BaBabababaBaBaBaBaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBaba" ++
     "babaBabaBabaBaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBababa" ++
     "baBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBabaBaBababababa" ++
     "BaBaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBa" ++
     "baBabaBaBababababaBaBaBababaBaBab",
   "BabaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBa" ++
     "BaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBaba" ++
     "BabaBaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBabababaBaBaBa" ++
     "BaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBaba" ++
     "babaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBaBa" ++
     "BabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBa" ++
     "baBaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBabababaBaBaBaBa" ++
     "BaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBababa" ++
     "BaBab",
   "BabaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBa" ++
     "bababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBabababaBaBaBaBaBa" ++
     "BaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBa" ++
     "bababaBaBaBaBaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababa" ++
     "BabaBabaBaBababababaBaBaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBa" ++
     "BaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBaba" ++
     "babaBaBabababaBaBabab",
   "BabaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBa" ++
     "BaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBaba" ++
     "BabaBaBababababaBaBaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBa" ++
     "BaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBaBaBaba" ++
     "babaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBaba" ++
     "babaBaBabababaBaBaBaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBabababaBaBaBaBaBaBa" ++
     "BaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBaba" ++
     "babaBaBaBaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBabababaBaBaBaBaBaBaBaBaBaBaba" ++
     "BabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBaBaBaBababa" ++
     "baBabaBabaBaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBaBaBababaBaBab",
   "BabaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBa" ++
     "BaBabababaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBabababa" ++
     "baBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBabababaBaBaBaBaBaBaBaBaBaBa" ++
     "baBabaBabababaBaBabababaBaBaBaBaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBa" ++
     "BaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBaBa" ++
     "BababaBaBab",
   "BabaBaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBaba" ++
     "BaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBaBaBaBabababaBaba" ++
     "BabaBaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBabababaBaBaBa" ++
     "BaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBaba" ++
     "babaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBabaBa" ++
     "BababababaBaBaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBababa" ++
     "baBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBabababaBaBaBaBaBaBaBaBaBaBabaBaba" ++
     "BabababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBaBaBaBabababaBa" ++
     "baBabaBaBababababaBaBaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaba" ++
     "b",
   "BabaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBa" ++
     "BaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBaba" ++
     "BabaBaBababababaBaBaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBa" ++
     "BaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababa" ++
     "BaBabababaBaBaBaBaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBabababaBa" ++
     "BaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBabaBaBababababaBaBa" ++
     "BabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBa" ++
     "baBaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBaBaBaBabababaBa" ++
     "baBabaBaBababababaBaBaBababaBaBab",
   "BabaBaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBaba" ++
     "BaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBaBaBaBabababaBaba" ++
     "BabaBaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBaBaBaBabababa" ++
     "BabaBabaBaBababababaBaBaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBa" ++
     "BaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBaBa" ++
     "BabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBabababaBaBaBaBaBaBa" ++
     "BaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBa" ++
     "BaBaBabababaBabaBabaBaBababababaBaBaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBa" ++
     "BabababaBaBabab",
   "BabaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBa" ++
     "BaBabababaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBa" ++
     "baBabababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBaBaBaBabababa" ++
     "BabaBabaBaBababababaBaBaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBa" ++
     "BaBaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBabababaBaBaBaBaBaBaBaBa" ++
     "BaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBaBaBa" ++
     "BabababaBabaBabaBaBababababaBaBaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBaba" ++
     "babaBaBabab"]

@[expose] def cWordStr : String :=
  "BabaBaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBaba" ++
    "BaBababababaBaBaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBa" ++
    "BaBabababaBabaBabaBaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababa" ++
    "BabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBabababaBaBaBaBaBaBaBaBaBaBa" ++
    "baBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBaBaBaBaba" ++
    "babaBabaBabaBaBababababaBaBaBabababaBaBaBaBabababaBabaBabaBaBababababaBaBaBabababaBababa" ++
    "baBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBabaBabaBaBababababa" ++
    "BaBaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBaBaBaBaBaBabababaBa" ++
    "baBabaBaBababababaBaBaBabababaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBaBa" ++
    "BaBabababaBaBaBaBaBaBaBaBaBaBabaBabaBabababaBaBabababaBaBabab"

@[expose] def s1Gens : Array (Array ℕ) := (s1WordStrs.map fun s => arr24 (m24W s)).toArray

@[expose] def p1Gens : Array (Array ℕ) := (p1WordStrs.map fun s => arr24 (m24W s)).toArray

@[expose] def cArr : Array ℕ := arr24 (m24W cWordStr)

@[expose] def p2Gens : Array (Array ℕ) := p1Gens.map (conjA 24 cArr)

@[expose] def r1Arr : Array ℕ := arr24 m24Rep1

@[expose] def r2Arr : Array ℕ := arr24 m24Rep2

@[expose] def ps24 : List ℕ := List.range 24

@[expose] def cS1 : ArrCert := enumBfs 24 s1Gens ps24 1000

@[expose] def cP1 : ArrCert := enumBfs 24 p1Gens ps24 2000

@[expose] def cP2 : ArrCert := enumBfs 24 p2Gens ps24 2000

@[expose] def clsP : Array ℕ := greedyCover 24 ps24 cP1 cP2

@[expose] def hatM24Check : Bool :=
  fpfA 24 r1Arr &&
    enumOK 24 s1Gens ps24 cS1 && cS1.pts.size == 512 &&
    allLt s1Gens.size (fun k => cmA 24 s1Gens[k]! r1Arr) && fpfPairOK 24 s1Gens cS1 r1Arr &&
    validA 24 cArr && cmA 24 cArr r2Arr &&
    enumOK 24 p1Gens ps24 cP1 && cP1.pts.size == 1024 &&
    allLt p1Gens.size (fun k => cmA 24 p1Gens[k]! r2Arr) &&
    enumOK 24 p2Gens ps24 cP2 && cP2.pts.size == 1024 &&
    coverOK 24 63 ps24 cP1 cP2 clsP

end CFSG.Quasithin.H13.Ch4.HatM
