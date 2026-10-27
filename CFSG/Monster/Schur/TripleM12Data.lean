module

public import Certificates.Data.CFSGNative.Bridge.SurjA
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Monster.Schur.TripleM12Words

public section

namespace CFSG.Monster.Schur

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge.TwoGen.Native CFSG.Sporadic.Mathieu.Native

@[expose] def m12w1 : List (Nat × Bool) :=
  [(0, true), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true),
    (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false),
    (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
    (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true),
    (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true),
    (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true),
    (1, true), (0, true), (1, true), (1, true), (0, false), (1, true), (0, false), (1, false),
    (0, false), (1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, true),
    (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (1, true), (0, true),
    (1, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true),
    (0, false), (1, true), (0, false), (0, false), (1, true), (0, false), (1, false), (0, false),
    (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false),
    (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, true),
    (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false),
    (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false),
    (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false),
    (0, false), (1, true), (0, false), (1, false), (1, false), (0, false), (1, true), (0, false),
    (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false)]

@[expose] def m12w2 : List (Nat × Bool) :=
  [(0, true), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true),
    (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false),
    (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
    (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true),
    (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true),
    (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false),
    (1, false), (0, false), (1, true), (0, false), (1, false), (1, false), (0, true), (1, false),
    (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false),
    (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false),
    (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false),
    (1, true), (0, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false),
    (0, false), (1, true), (0, false), (1, true), (1, true), (0, true), (1, true), (0, true),
    (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true),
    (1, false), (0, true), (1, false), (0, true), (1, false), (1, false), (0, false), (1, false),
    (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (1, true), (0, true),
    (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
    (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
    (1, false), (0, true), (1, true), (1, true), (0, false), (1, true), (0, false), (1, false),
    (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false),
    (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true),
    (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
    (0, true), (1, false), (0, true), (1, true)]

@[expose] def m24TabBinv : Table :=
  #[5, 13, 14, 0, 9, 3, 6, 7, 2, 17, 10, 11, 15, 20, 8, 16, 12, 4, 22, 19, 1, 21, 23, 18]

@[expose] def m12TabH1 : Table := wordTab 24 m24Data.tA m24Data.tA m24Data.tB m24TabBinv m12w1

@[expose] def m12TabH2 : Table := wordTab 24 m24Data.tA m24Data.tA m24Data.tB m24TabBinv m12w2

@[noinline, expose] def m12Check : Bool :=
  relCheck 24 m12TabH1 (invT 24 m12TabH1) m12TabH2 (invT 24 m12TabH2) [m12R1, m12R2, m12R3] &&
    invOK 24 m12TabH1 (invT 24 m12TabH1) && invOK 24 m12TabH2 (invT 24 m12TabH2) &&
    ap m12TabH1 1 != 1

end CFSG.Monster.Schur
