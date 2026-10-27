module

public import CFSG.Sporadic.FischerOddCore.Fi22CentData
public import CFSG.Monster.B.Fischer.Fi22OuterCheck
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentData
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheck
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

@[expose] def fi22CentBytes : ByteArray := fi22Cent3510Text.toUTF8

@[expose] def fi22CentArr (L : Nat) : Array Nat := hexLine fi22CentBytes 3 3510 L

@[expose] def fi22SearchNodeDataOK : Bool :=
  fi22SearchNodeData.length == 138 &&
    fi22SearchNodeData.all fun N =>
      N.2.1.all (fun rk => decide (rk.2 < 138)) && N.2.2.1.all (fun j => decide (j < 64)) &&
        decide (N.2.2.2.1 ≤ 2) && decide (N.2.2.2.2 < 2)

end CFSG.Sporadic.FischerOddCore
