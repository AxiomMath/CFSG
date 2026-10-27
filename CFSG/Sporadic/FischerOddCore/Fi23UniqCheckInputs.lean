module

public import Certificates.Data.CFSGNative.Fi23.Classes
public import Certificates.Data.CFSGNative.Fi23.Centralizer
public meta import Certificates.Data.CFSGNative.Fi23.Classes
public meta import Certificates.Data.CFSGNative.Fi23.Centralizer

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi23.Native

@[expose] def fi23UniqFix (P : Table) : Nat := (List.range 31671).countP fun i => ap P i == i

@[expose] def fi23UniqOK (O : WOrbit) : Bool :=
  let X := compT 31671 (dTab O) (treeActTab O (dTab O) (genTables O (-2)) 1)
  allIn 0 31671 fun k => k == 0 || k == 1 || ap X k != k ||
    fi23UniqFix (compT 31671 (treeActTab O (dTab O) (genTables O (-2)) k) X) != 3511

@[expose] def fi23TripOK (O : WOrbit) : Bool :=
  let X := compT 31671 (compT 31671 (dTab O) (treeActTab O (dTab O) (genTables O (-2)) 1))
    (treeActTab O (dTab O) (genTables O (-2)) 39)
  allIn 0 31671 fun k => k == 0 || k == 1 || k == 39 || ap X k != k ||
    fi23UniqFix (compT 31671 (treeActTab O (dTab O) (genTables O (-2)) k) X) != 695

end CFSG.Sporadic.FischerOddCore
