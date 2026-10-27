module

public import Certificates.Data.Kernel.LocalQT.PermW
public import Certificates.Data.Kernel.E64F

public noncomputable section

namespace CFSG.KC.SLCls

open CFSG.KC.LQT.PW CFSG.KC.E64F

@[expose] def eqOnN (n : Nat) (f g : Nat → Nat) : Bool := (List.range n).all fun p => f p == g p

@[expose] def clsOK (L : Nat → Nat → Nat) (n : Nat) (x : Nat → Nat) (ws : List (List Nat))
    (cs : List Nat) : Bool :=
  !cs.isEmpty && decide (cs.length ≤ 4) && eqOnN n (imgW 9 (cs.headD 0)) x &&
    ws.all fun w => cs.all fun u => cs.any fun v =>
      eqOnN n (fun p => wordF L w (imgW 9 u p)) (fun p => imgW 9 v (wordF L w p))

end CFSG.KC.SLCls

end
