module

public import CFSG.Sporadic.Recognition.McLASInputs
public meta import CFSG.Sporadic.Recognition.McLASInputs

public section

namespace CFSG.Sporadic.Recognition.McLAS

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.SmallOddCore

@[expose] def fixedPtCount (n : Nat) (T : Table) : Nat :=
  ((List.range n).filter fun i => ap T i == i).length

@[expose] def pairHex : String :=
  "0D70A80F40120B600B01D01E04E04D02E0CF0D609C03601A0200860AE05110B0CC04C04802909A0330CA097093092\
  0380DC02B0FB0140A50F20FF06C0260CD07405A0A900405908A0AB0CE04A00F0941090DF0C00EC0EB07F0B502706D1\
  0A1000960BE06008803F07C00806F08D0D00800300680E304604F0C90980D11030D30310FC05707500A0210000660E\
  904505310C0760DE0BA01B0AF0F801C0160490A607803C0CB09108907003E0DD0E20F307907E09E07B05801506B05E\
  03B0610840320561100B403A0430E70BD0850470D90190D20170340410350F900700608E0730D506701310808B0C80\
  D80500FE0630E60FD0B10220870C10D40820DB0C60AA04B0AD0C50030F61060E40620C710F07D02D0F109B10409F0\
  B90370A408F0990BC0240390B30A00AC02C0C30B809D06403D07A0180550050690FA10511106A0400EF05B00D02F07\
  20010100DA0B200E0F50E00950090A20F70C40110B71120A10C201F02510200C0020E80ED02A0F00E106510D05C06E\
  0520A30810EA0770280440EE10105F0BB08C1070B00BF0900710230420E510E0830A705405D"

@[expose] def pairTbl : Table := hexT 3 275 0 pairHex

@[expose] def pairSel (a b : Table) : Bool :=
  ordTest 275 3 b && fixedPtCount 275 b == 5 && !tblEq 275 b (idT 275) && !tblEq 275 b a &&
    !tblEq 275 b (compT 275 a a)

@[expose] def pairCheckAux (a : Table) (cg cgInv : Array Table) (C o : Closure) : Bool :=
  fixedPtCount 275 a == 5 && permOK 275 pairTbl && mclSift pairTbl && commTT 275 pairTbl a &&
    pairSel a pairTbl && cg.all (fun c => permOK 275 c && invOK 275 c (invT 275 c)) &&
    conjTreeOK 275 cg cgInv pairTbl o.1 o.2.1 o.2.2 && hkeysDistinct 275 o.1.toList &&
    o.1.size == 180 && C.1.all fun e => !pairSel a e || memT 275 o.1 e

@[expose] def pairCheck : Bool :=
  let cg := threeRow₁.centGens.toArray
  let cgInv := cg.map (invT 275)
  pairCheckAux (threeTbl 0) cg cgInv (mulClosureH 275 cg 924000)
    (conjClosureH 275 cg cgInv pairTbl 200)

end CFSG.Sporadic.Recognition.McLAS
