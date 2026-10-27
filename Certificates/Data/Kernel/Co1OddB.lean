module

public import Certificates.Data.Kernel.Co1BW
public import CFSG.Sporadic.Schreier.Co1OddData

public section

namespace CFSG.KC.Co1OddB

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.F2W

@[expose] noncomputable def rowU (HP : List Nat) (u i : Nat) : Nat := vmF 24 (trK 24 (HP.getD i 0)) u

@[expose] noncomputable def usK (HP : List Nat) (u0 u1 : Nat) : Nat :=
  orN 24 fun i =>
    (if CFSG.Sporadic.Co1Schreier.Data.oddSel.getD i 0 = 0 then rowU HP u0 i else rowU HP u1 i) <<<
      (24 * i)

@[expose] noncomputable def candK (X Y S : Nat) (HP : List Nat) (BT BTI u0 u1 : Nat) : Bool :=
  let U := usK HP u0 u1
  let T := trK 24 (mulW 24 BTI U)
  eqK (mulW 24 BT (trK 24 T)) U &&
    (!(eqK (mulW 24 T X) (mulW 24 X T) && eqK (mulW 24 T Y) (mulW 24 Y T) &&
        eqK (mulW 24 T S) (mulW 24 S T) && !eqK T oneK) ||
      [3, 5, 7, 13].all fun p => !eqK (powWK T p) oneK)

@[expose] noncomputable def candM (XT YT ST BT BTI U : Nat) : Bool :=
  let M := mulW 24 BTI U
  eqK (mulW 24 BT M) U &&
    (!(eqK (mulW 24 XT M) (mulW 24 M XT) && eqK (mulW 24 YT M) (mulW 24 M YT) &&
        eqK (mulW 24 ST M) (mulW 24 M ST) && !eqK M oneK) ||
      [3, 5, 7, 13].all fun p => !eqK (powWK M p) oneK)

end CFSG.KC.Co1OddB

end
