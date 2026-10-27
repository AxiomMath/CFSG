module

public import CFSG.Sporadic.Co2Schreier.Arrays
public import CFSG.Sporadic.Schreier.Co3OrbitTCheck
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import CFSG.Sporadic.Schreier.Co3OrbitTCheck
public meta import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.InvariantMerge
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native

@[expose] def izList : List ℕ := fixedList 2300 zArr

@[expose] def itList : List ℕ := fixedList 2300 tArr

@[noinline, expose] def orbitRecordOK (start : List ℕ) (bound : ℕ)
    (O : Array (List ℕ) × Array ℕ × Array ℕ) : Bool :=
  translatesOK aArrs start O.1 O.2.1 O.2.2 && keysSortedOK O.1 && O.1.size == bound

end CFSG.Sporadic.Co2Schreier
