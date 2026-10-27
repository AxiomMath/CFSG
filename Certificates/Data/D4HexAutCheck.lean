module

public import Certificates.Data.D4HexLocCheck

public section

namespace CFSG.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Monster.B.Co2.Native

@[expose] def onLine (l p : ℕ) : Bool := p == lnPt l 0 || p == lnPt l 1 || p == lnPt l 2

@[expose] def stabsLine (a : Array ℕ) (l : ℕ) : Bool :=
  onLine l a[lnPt l 0]! && onLine l a[lnPt l 1]! && onLine l a[lnPt l 2]!

@[expose] def lineMoved : Bool :=
  allLt 2457 fun l => l == 0 ||
    (List.range cWords.length).any fun k => !(stabsLine (locWordArr (cWords.getD k [])) l)

@[expose] def autQWord : List ℕ := [3]

@[expose] def autQCheck (eT eQ : EnumData) : Bool :=
  autQWord.all (fun k => decide (k < 8)) && (locWordArr autQWord)[0]! == 0 &&
    allLt eT.El.size fun i =>
      !(memR eT.El eT.idx
        (conjI (wordR d4Gens autQWord.reverse) (wordR d4Gens autQWord) eT.El[i]!)) ||
        memR eQ.El eQ.idx eT.El[i]!

@[expose] def autCheck : Bool := lineMoved && autQCheck locET locEQ

end CFSG.D4Hex
