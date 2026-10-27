module

public import CFSG.Sporadic.SmallOddCore.CentData
public import CFSG.Sporadic.Schreier.Co3SylowCheck
public meta import CFSG.Sporadic.SmallOddCore.CentData
public meta import CFSG.Sporadic.Schreier.Co3SylowCheck

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.Schreier.Co3 CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def co3FusionHex : String := include_str "Co3Fusion.txt"

@[expose] def co3FusionTbl (k : ℕ) : Table := hexT 3 276 (276 * k) co3FusionHex

@[expose] def co3FusionFlags : List Bool :=
  [true, false, true, false, false, true, false, false, false, false, false, false, false, true,
    false, true, false, false, false, false, false, false, false, true, false, true, false,
    false, true, false, true, false, false, true, false, false, false, false, true, false, false,
    false, false, false, true, false, false, false, false, false, true, false, false, false,
    false, true, true, false, true, false, false, false, true, false, true, false, false, false,
    false, true, true, false, false, true, false, false, false, false, true, false, true, false,
    false, true, false, false, false, false, false, true, false, false, false, true, false,
    false, false, true, false, false, false, false, false, false, true, false, false, false,
    true, true, true, false, false, false, true, false, false, false, false, false, false, true,
    false, true, true, true, false, true, false, true, false, false, false, true, false, false,
    false, false, false, true, false, false, true, false, true, true, false, true, false, true,
    true, false, false, true, true, false, false, false, true, false, false, false, false, true,
    true, false, false, false, false, false, false, false, false, false, true, false, true,
    false, false, false, true, false, false, false, false, false, false, true, false, false,
    false]

@[expose] def co3FusionWits : List (Table × Bool) :=
  (List.range 191).map fun k => (co3FusionTbl k, co3FusionFlags.getD k false)

@[expose] def co3TTbls : Array Table := (co3TArrs.extract 0 8).map fun a => a.map UInt32.ofNat

@[expose] def co3ZTbl : Table := co3ZArr.map UInt32.ofNat

@[expose] def co3TtTbl : Table := co3TtArr.map UInt32.ofNat

@[expose] def co3Sift (T : Table) : Bool := siftA 276 co3ChainLevels co3ChainBaseArr 0 (natArr T)

@[expose] def co3FusesTo (s : Table) (w : Table × Bool) : Bool :=
  tblEq 276 (conjT 276 w.1 (invT 276 w.1) s) (if w.2 then co3ZTbl else co3TtTbl)

@[expose] def co3FusionOK : Bool :=
  let E := mulClosureH 276 co3TTbls 2000
  let I := E.1.filter (involOK 276)
  co3TTbls.all (fun g => permOK 276 g && invOK 276 g (invT 276 g)) &&
    mulTreeOK 276 co3TTbls E.1 E.2.1 E.2.2 &&
    closedOK 276 (co3TTbls ++ co3TTbls.map (invT 276)) E.1 &&
    hkeysDistinct 276 E.1.toList && E.1.size == 1024 &&
    co3FusionWits.all (fun w => permOK 276 w.1 && invOK 276 w.1 (invT 276 w.1) && co3Sift w.1) &&
    I.size == 191 && I.all (fun s => co3FusionWits.any (co3FusesTo s)) &&
    (I.filter fun s => co3FusionWits.any fun w => w.2 && co3FusesTo s w).size == 55 &&
    (I.filter fun s => co3FusionWits.any fun w => !w.2 && co3FusesTo s w).size == 136

end CFSG.Sporadic.SmallOddCore
