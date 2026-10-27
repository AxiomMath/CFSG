module

public import Certificates.Data.D4HexLinkCheck

public section

namespace CFSG.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Monster.B.Co2.Native

@[expose] def lineKleinOK (T : Array (Array Nat)) : Bool :=
  allLt 2457 fun l =>
    mulR T[lnPt l 0]! T[lnPt l 1]! == T[lnPt l 2]! &&
      mulR T[lnPt l 1]! T[lnPt l 0]! == T[lnPt l 2]!

@[expose] def kleinLineOK (cz : ClassData) : Bool :=
  allLt 819 fun q =>
    q == 0 || !(mulR cz.T[0]! cz.T[q]! == mulR cz.T[q]! cz.T[0]!) ||
      !(memR cz.T cz.idx (mulR cz.T[0]! cz.T[q]!)) ||
      (List.range 2457).any fun l =>
        lnPt l 0 == 0 && lnPt l 1 == min q (cz.idx (mulR cz.T[0]! cz.T[q]!)) &&
          lnPt l 2 == max q (cz.idx (mulR cz.T[0]! cz.T[q]!))

@[expose] def lineCharOn (cz : ClassData) : Bool := lineKleinOK cz.T && kleinLineOK cz

@[expose] def lineCharCheck : Bool := lineCharOn (mkClass d4Gens z0R)

end CFSG.D4Hex
