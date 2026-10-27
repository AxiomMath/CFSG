module

public import CFSG.Sporadic.J4.QT2LocX0Native
public import Certificates.Data.CFSGNative.J4.FixScan

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

@[expose] def scanBs : BFSState := bfs (frTable rowsA) (frTable rowsB) rootV nPts

@[expose] def chkScanX0 : Bool :=
  fixScanOK scanBs.keys nPts (frTable (x0GenRows[0]!)) x0Pts 3

end CFSG.Sporadic.J4.QT2
