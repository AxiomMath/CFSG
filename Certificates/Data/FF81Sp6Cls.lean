module

public import Certificates.Data.RudvalisFF81Sp6RefS

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Cls

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6RefS (c7P)

@[expose] def hCode : List ℕ :=
  [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1,
    0, 0, 1, 1, 0]

@[expose] def hInv : List ℕ :=
  [1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1,
    1, 0, 0, 0, 0]

@[expose] def gam0C : List ℕ :=
  [0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0,
    1, 1, 1, 1, 1]

@[expose] def gam0I : List ℕ :=
  [1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1,
    0, 1, 0, 1, 0]

@[expose] def k0C : List ℕ :=
  [0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 1, 1]

@[expose] def gam1C : List ℕ :=
  [1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0,
    1, 1, 0, 0, 0]

@[expose] def gam1I : List ℕ :=
  [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1,
    1, 1, 0, 0, 1]

@[expose] def k1C : List ℕ :=
  [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0,
    0, 0, 0, 0, 1]

@[expose] def gam2C : List ℕ :=
  [1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1,
    0, 1, 1, 1, 0]

@[expose] def gam2I : List ℕ :=
  [1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0,
    0, 1, 1, 0, 1]

@[expose] def k2C : List ℕ :=
  [1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 1, 1, 1, 0]

@[expose] def gam3C : List ℕ :=
  [0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1,
    0, 0, 0, 0, 1]

@[expose] def gam3I : List ℕ :=
  [0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0,
    1, 0, 0, 1, 0]

@[expose] def k3C : List ℕ :=
  [0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0,
    1, 1, 0, 1, 0]

@[expose] def clsPairs : List (List ℕ × List ℕ) :=
  [(hCode, hInv), (gam0C, gam0I), (gam1C, gam1I), (gam2C, gam2I), (gam3C, gam3I), (k0C, k0C),
    (k1C, k1C), (k2C, k2C), (k3C, k3C)]

@[expose] def t0pC : List ℕ := mul6 (mul6 hInv t0C) hCode

@[expose] def invC : Fin 4 → List ℕ := ![t0C, t1C, t2C, t3C]

@[expose] def gamP : Fin 4 → List ℕ × List ℕ :=
  ![(gam0C, gam0I), (gam1C, gam1I), (gam2C, gam2I), (gam3C, gam3I)]

@[expose] def kC : Fin 4 → List ℕ := ![k0C, k1C, k2C, k3C]

@[expose] def repC : Fin 4 → List ℕ := ![zCode 1, zCode 1, zCode 1, mul6 (zCode 0) (zCode 1)]

@[expose] def gamC (i : Fin 4) : List ℕ := mul6 (mul6 (gamP i).1 (repC i)) (gamP i).2

@[expose] def pairsChk899111 : Bool :=
  clsPairs.all pairCheck

@[expose] def c7Chk899111 : Bool :=
  (closureT (c7P.map Prod.fst)).all fun c =>
    !(mul6 c c == one6) || c == one6 || !(orbit0.contains c)

@[expose] def witChk899111 : Bool :=
  (List.finRange 4).all fun i =>
    commutes6 (gamC i) (invC i) && commutes6 (kC i) (invC i) && mul6 (kC i) (kC i) == one6 &&
      !(kC i == one6) && mul6 (mul6 (kC i) (gamC i)) (kC i) == mul6 (gamC i) (gamC i)

@[expose] def sylChk899111 : Bool :=
  sylowP.all (fun p => commutes6 p.1 t0pC) && sylowT.contains t0pC &&
    sylowT.all fun y => !(sylowP.all fun p => commutes6 y p.1) || !(mul6 y y == one6) ||
      y == one6 || !(orbit0.contains y) || y == t0pC

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Cls
