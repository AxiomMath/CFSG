module

public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

@[expose] noncomputable def anyN (n : Nat) (f : Nat → Bool) : Bool :=
  bIf(allN n (fun i => bIf(f i, false, true)), false, true)

@[expose] noncomputable def kappaK (n w k w' IP CP CIP M K : Nat) : Bool :=
  bAnd(szOK n w, bAnd(szOK k w',
  bAnd(allN k (fun i => Nat.blt (pg w (mask w) IP i) n),
  bAnd(allN k (fun i => allN i (fun j =>
    bIf(Nat.beq (pg w (mask w) IP i) (pg w (mask w) IP j), false, true))),
  bAnd(permOK k w' (mask w') (Nat.mul k w') CP CIP,
  bAnd(canonK k w' (mask w') (Nat.mul k w') K,
  allN k (fun i => Nat.beq (pg w (mask w) M (pg w (mask w) IP i))
    (pg w (mask w) IP (pg w' (mask w') CIP (pg w' (mask w') K (pg w' (mask w') CP i)))))))))))

@[expose] noncomputable def coversK (n w : Nat) (G : Nat → Nat) (kg : Nat) (H : Nat → Nat)
    (kh : Nat) : Bool :=
  bAnd(allN kg (fun i => canonK n w (mask w) (Nat.mul n w) (G i)),
  bAnd(allN kh (fun j => canonK n w (mask w) (Nat.mul n w) (H j)),
  bAnd(allN kg (fun i => bIf(Nat.beq (G i) (pidn n w), true,
    anyN kh (fun j => Nat.beq (G i) (H j)))),
  allN kh (fun j => anyN kg (fun i => Nat.beq (H j) (G i))))))

end CFSG.KS.SporSch

end
