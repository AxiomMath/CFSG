module

public import Certificates.Data.CoreD2LinesOne
public import CFSG.Sporadic.Schreier.RuDefs
public import CFSG.Sporadic.Schreier.RuEnum
public import Mathlib.GroupTheory.Schreier

public section

namespace Certificates.CoreD2Perm

open CFSG.Sporadic.RuSchreier

@[expose] def ruFiveLinesEW : String :=
  "ABABBABBAbABABABBABAAABABABAAABabababaBABAABABABAAAABBABBABBBABabbaBaBabbaBBAABAAABABABABBAbAb\
  AbAbababaBabbaBababABABABBAABBABBAAAAABABABBBBBBAAABABBABABBABababbababbaBabbaBAABAAABABABABBA\
  bAbAbABABAABABABAAAABBABBABBBABabbaBaBabbaBAAABABABAAABabababaBababaBabbaBababABABABBAABBABBAB\
  BABBABABABAbABBABABBAABAbAbAbABABAbABAbAbAbAbABBABABBB,bbbABABABABAbAbAbABABABABABAbAbAbAbABAB\
  ABABAbAbAbABababbaBaBababaBaBaBabaaBaBaBabbabababaaabaBAbABBABB,bbABABAbABABAbABBaBababbaBabbA\
  bABBABABBABABBABABAbABABABABAbaaabababaaababbababaBABAbABBAbABABAbABBAbAbABBAbabbbabbabbaaaaba\
  babaababABABABAbaaabababaaabABBAbAbABBAbabbbabbabbaaaabababaababbABABABAbaaabababaaababbabaBaB\
  ababba,bbABABABABBAbAbAbAbbABABABABAbAbAbaBaBaBaBababababaBaBaBaBababababaBABABABAbaaabababaaa\
  bABABABAbaaabababaaababbababaBABAbABBAbABABAbABABABAbaaabababaaabABBAbAbABBAbabbbabbabbaaaabab\
  abaababaBaBaBabbabababaaabaabABBAbABBABABBABAbabbababbabaaabbbbbbababaaaaabbabbaaBabababABABAb\
  AbABBABABAbAb,BabababbabbabbababbabababbabaBaBabababaBaBababaBBBAAABABABAAABababababABABABABAb\
  AbAbAbaBaBaBabababababaBaBaBababababaBBaBaBaBabbabababa,ABABBabbaBaBabbabaBaBBBABAABABABAAAABB\
  ABBABBBABabbaBaBabbaBAAABABABAAABabababaBBABAABABABAAAABBABBABBBABabbaBaBabbaBababaBabbaBababA\
  BABABBABBBAAABABABAAABabababaBBBAAABABABAAABababababABABABABAbAbAbAbABABABABAbAbAbAbABaBaBabab\
  abababaBaBaBabbabababa,bbbABABABABBAbAbAbABABAbAbABBABBABABAbABBABBABABBAbabaBaBaBaBababaBaBaB\
  aBababbabbababaBABAbABBAbABABABABBAbAbABBAbabbbabbabbaaaabababaababABABABAbaaabababaaabABBAbAb\
  ABBAbabbbabbabbaaaabababaababABBAbAbABBAbabbbabbabbaaaabababaababABABABAbaaabababaaabABBAbAbAB\
  BAbabbbabbabbaaaabababaababAbABABABBABBABAbba"

@[expose] def ruFiveLinesGW : String :=
  "bbABABABABBAbAbAbAbbABABABABAbAbAbaBaBaBaBababababaBaBaBaBaBabababaBABABABAbaaabababaaabbbabba\
  bbabbababaBaBabaBaBaBaBabbAbABBAbABABBAbba,BabaBaBabbabaBaBABAABABABAAAABBABBABBBABabbaBaBabba\
  BBAAABABABAAABabababaBababaBabbaBababABABABBAABBABBAAAAABABABBBBBBAAABABBABABBABababbababbaBab\
  baBAABAAABABABABBAbAbAbABABAABABABAAAABBABBABBBABabbaBaBabbaBAAABABABAAABabababaBababaBabbaBab\
  abABABABBABAABAAABABABAAABabababaBABABABABAbAbAbAbaBaBaBabababababaBaBaBaBAbAbAbAbbaBaBaBabbab\
  ababaB,bbABABABABBAbAbAbABABABABABAbAbAbaBaBaBaBababababaBaBaBaBaBabababaBABABABAbaaabababaaab\
  ABABABAbaaabababaaabABBAbAbABABAbABBAbABABAABBAbAbABBAbabbbabbabbaaaabababaababbABABABAbaaabab\
  abaaabAbABBAbAB,bababbaBabaBaBBAABAAABABABABBAbAbAbABAAABABABAAABabababaBABAABABABAAAABBABBABB\
  BABabbaBaBabbaBAAABABABAAABababababbababaBabbaBababaBaBBBAAAAABABABBBBBBAAABABBABABBABababbaba\
  bbaBabbaBAABAAABABABABBAbAbAbABABAABABABAAAABBABBABBBABabbaBaBabbaBAAABABABAAABabababaBababaBa\
  bbaBababABABABBAAbAbABBAbABBAbABBABBAbAbABABABBAbABBAbAbABBABBababbababbabaBaBaBaBabbabababa,a\
  babbaBababbabbaBABAABABABAAAABBABBABBBABabbaBaBabbaBABAABABABAAAABBABBABBBABabbaBaBabbaBABAABA\
  BABAAAABBABBABBBABabbaBaBabbaBAAABABABAAABabababaBababaBabbaBababABABABBABBBAAABABABAAABababab\
  abaBaBaBababababaBABABABAbAbAbAbABABaBaBaBAbAbAbABBB,ABABABABBABAbAbbbaBaBabbababbababbaBabaBa\
  abbababaBABAbABBAbABABAbabaBaBaBaBababababbaBababbaBBABABBAbAbAbAbbaBaBaBabbabababaB,BABBABBAB\
  BABABABAbabbaBababbabABABABBABABABABBABAABAAABABABAAABabababaBABABABABAbAbAbAbABABABABAbAbAbAB\
  ABaBaBaBAbAbAbAB,bababbaBaBababbABAAABABABABBAbAbAbbabbabbababbaBabbaBababbaBaBABBAAAAABABABBB\
  BBBAAABABBABABBABababbababbaBabbaBAABAAABABABABBAbAbAbABABAABABABAAAABBABBABBBABabbaBaBabbaBAA\
  ABABABAAABabababaBababaBabbaBababABABABBABBBAABAAABABABAAABabababaBAAABABABAAABabababaBABABABA\
  BAbAbAbAbABABABABAbAbAbABABaBaBababababaBBaBaBaBabbabababaBBB"

@[expose] def ruFiveLinesWA : String :=
  "cbcacaaCCBABACACAACaaCBAAABAAAAccAbaaCbaaCBACACCaBCCACCBBCAACCABAbaccbAACBAACBACacACbcbcabCaCa\
  abaCaBCAACCABAbaccbAACBAACBACacACbcbcabCaCaabaCabaaaBaBabAbAbaa,AAAABDAADABDAAABAAbaaaaBABAAba\
  aaaBABAAbaaaaBABdBDBdBDDDbabAbaBDBAAdaBdadABaDAB,EEABaeBeABaBEABaaEAAeeabaebaEAAABaaaBAbaEEEEE\
  a,FAAFFBAfBABAAABAABABAABAABaBaBaaFbfAFaafbfafbabFFafAAABaFAABFbaFAABFFAAA,AggaGGaBGABAgBaBaBa\
  BaBaBGABAgBGABAgBaBabGAbAgbabaGAgAGAgBgagAggbGGba,HHHBHBHAHBHBHAHbAhabaaHHBBHBHHAAHHHHHBABHBHA\
  AHbhahahAAbabAAHAAAABABBBBBHHHBHbHahabAHahhAAABABHHHAAHHBBAHBHbHaHaHHAAHHBBHHBHAAABHBAHHAHBHbH\
  ahaBHHAAHHHHHBABHBHAAHbhahahAAbabAAbhbahbABABHHHAAHHBBAHBHbHaHaHHAAHHBBHAHAAAABABBBBBHHHBHbHah\
  abAHahhAAAAHAAAABABBBBBHHHBHbHahabAHahhAAAHBBHBHHAAHHHHHBABHBHAAHbhahahAAbabAHH"

@[expose] def ruFiveLinesWB : String :=
  "ABAcACaBBCAACCABAbaccbACACAACaaCaCCAACACAACaaCaCACAACaaCaaaabAACCaabaabAbAbaa,dbdbdaDABDAADDbA\
  ddAAdaddAdaaabAAAbaadaBAdadABaDAB,eebAAeABaBAEABeBEBeaababaBEABaaeaEaaBAABaaEEEEEa,AAFABFBAABA\
  baabAbFAbaafBFbAfAAABAfaBAbaaabaFFAABFbaFAABFFAAA,AGAAGBABGBaaBAgbAGAbaGAGGGAGAgA,aaHbHaBHHAAH\
  HHHHBABHBHAAHbhahahAAbabAAABAhAAHBBHBHHAAHHHHHBABHBHAAHbhahahAAbabABHHAAHHHHHBABHBHAAHbhahahAA\
  babAAHAAAABABBBBBHHHBHbHahabAHahhAAABABHHHAAHHBBAHBHbHaHaHHAAHHHBBBHABBAHBHAABHBAABHbHbhbaBAHH\
  BBHHAAHHHHHBABHBHAAHbhahahAAbabABHHAAHHHHHBABHBHAAHbhahahAAbabABABHHHAAHHBBAHBHbHaHaHHAAHAHAAA\
  ABABBBBBHHHBHbHahabAHahhAAABHHAAHHHHHBABHBHAAHbhahahAAbabAHH"

@[expose] def ruFiveLinesData : VData where
  base :=
    { n := 4060
      p := 5
      aT := ruArr4060 0
      bT := ruArr4060 1
      eW := wordsOfString ruFiveLinesEW
      eK := 3
      pairs := []
      gWs := wordsOfString ruFiveLinesGW
      fd := []
      wA := []
      wB := [] }
  ys := [1, 2, 3, 4, 5, 6]
  gk := [⟨1, 0, 1, 0, 3, 0⟩, ⟨1, 0, 1, 0, 4, 0⟩, ⟨1, 0, 0, 1, 4, 0⟩, ⟨1, 1, 0, 1, 3, 0⟩,
    ⟨1, 2, 0, 1, 2, 0⟩, ⟨1, 3, 0, 1, 2, 0⟩, ⟨1, 4, 0, 1, 4, 0⟩, ⟨1, 5, 0, 1, 2, 0⟩]
  wAs := wordsOfString ruFiveLinesWA
  wBs := wordsOfString ruFiveLinesWB

end Certificates.CoreD2Perm
