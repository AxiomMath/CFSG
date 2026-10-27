module

public import Certificates.Data.CFSGNative.MonsterAxis.Dense

@[expose] public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMSeven

open CFSG.Monster.AxisCount.Native

def qZ : List Gen :=
  [.xi, .rho (false, 0, 4026), .rho (false, 0, 4),
  .perm #[4, 0, 1, 8, 2, 18, 21, 15, 3, 23, 17, 14, 9, 12, 13, 5, 11, 19, 6, 16, 10, 7, 20, 22]]

def qF : List Gen :=
  [.rho (false, 2915, 920), .rho (false, 0, 357), .rho (false, 0, 6),
  .perm #[21, 9, 18, 5, 1, 3, 0, 14, 15, 12, 2, 13, 8, 23, 4, 17, 10, 6, 16, 20, 22, 7, 11, 19],
  .xi, .rho (false, 0, 40),
  .perm #[11, 7, 5, 4, 18, 14, 3, 23, 19, 12, 1, 20, 6, 8, 10, 9, 17, 2, 21, 15, 16, 22, 13, 0]]

def qA : List Gen :=
  [.rho (false, 2161, 2274), .rho (false, 0, 2223), .rho (false, 0, 30),
  .perm #[0, 1, 8, 9, 12, 5, 13, 4, 15, 7, 6, 14, 21, 22, 19, 17, 3, 11, 10, 2, 23, 16, 20, 18],
  .xi, .rho (false, 0, 20),
  .perm #[0, 20, 1, 22, 5, 11, 6, 9, 2, 23, 3, 21, 4, 8, 7, 10, 15, 17, 18, 14, 13, 12, 16, 19]]

def qX : List Gen :=
  [.rho (false, 3066, 2629), .rho (false, 0, 114),
  .perm #[0, 16, 13, 12, 20, 1, 19, 22, 8, 18, 11, 2, 9, 23, 7, 15, 21, 5, 14, 10, 17, 4, 3, 6],
  .xi, .rho (false, 0, 24),
  .perm #[6, 14, 13, 7, 3, 18, 17, 1, 12, 5, 4, 15, 16, 2, 0, 19, 20, 21, 10, 8, 11, 22, 9, 23],
  .xi, .rho (false, 0, 4),
  .perm #[17, 2, 23, 18, 13, 16, 6, 9, 5, 12, 11, 19, 1, 7, 4, 20, 3, 14, 21, 15, 8, 10, 22, 0]]

def qT : List Gen :=
  [.rho (true, 0, 0)]

def qChecksAt (ev : List Gen → DVec → DVec) (v : DVec) : Bool :=
  let z1 := ev qZ v
  let z2 := ev qZ z1
  let z3 := ev qZ z2
  let z4 := ev qZ z3
  let z5 := ev qZ z4
  let z6 := ev qZ z5
  let f1 := ev qF v
  let f2 := ev qF f1
  let f3 := ev qF f2
  let f4 := ev qF f3
  let a1 := ev qA v
  let a2 := ev qA a1
  let a3 := ev qA a2
  let x1 := ev qX v
  let t1 := ev qT v
  [qZ, qF, qA, qX, qT].all (fun w => w.all fun g => g.validB) &&
    (ev qZ z6).eqv v && (ev qF f4).eqv v && (ev qT t1).eqv v &&
    (ev qF z1).eqv (ev qZ f1) && (ev qT z1).eqv (ev qZ t1) && (ev qT f1).eqv (ev qF t1) &&
    (ev qA z1).eqv (ev qZ a1) && (ev qX z1).eqv (ev qZ x1) && (ev qA a3).eqv t1 &&
    (ev qX x1).eqv t1 && (ev qA (ev qX a1)).eqv x1

def qAt (v : DVec) : Bool :=
  qChecksAt evalWord v

end CFSG.HardMathSupport.Dickson.I271.TabMSeven
