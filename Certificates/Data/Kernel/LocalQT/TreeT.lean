module

public import Certificates.Data.Kernel.LocalQT.RankB

public section

namespace CFSG.KC.LQT.TT

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.RW CFSG.KC.LQT.RF CFSG.KC.LQT.RB

@[expose] noncomputable def codesL (TF : Nat → Nat) (N : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) [] (fun j ih => List.cons (TF j) ih) N

@[expose] noncomputable def treeTH (n w W : Nat) (B ta tb : List Nat) (prog qp : List (Nat × Nat))
    (TF : Nat → Nat) (K m k fuel dd zi PK CK RP RC : Nat) (PT CT : Nat → Nat) : Bool :=
  (fun (N : Nat) => (fun (R : List Nat) => allBs [tabL n ta, tabL n tb, slpOKK prog 2,
    Nat.beq (TF 0) (codeK w ta), Nat.beq (TF 1) (codeK w tb), Nat.ble N (Nat.mul K m),
    qpW n w B R qp,
    rankBE W (lenA qp) k fuel zi 1 254 PK CK RP RC PT CT
      (enumW w (lenA B) (lenA qp) (imgsW w) (fstN R qp) (ptsW w B (fstN R qp)) dd)])
    (codesL TF N))
  (Nat.add (lenA prog) 2)

end CFSG.KC.LQT.TT

end
