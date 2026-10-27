module

public import Certificates.Data.Kernel.SlpCls

public section

namespace CFSG.KC.SlpPc

open CFSG.KC.Ord

@[expose] noncomputable def clsPc (mul : Nat → Nat → Nat) (ONE A B Xg : Nat)
    (prg : List (Nat × Nat)) (rx : Nat) (sg : List Nat) (rel es : List (List Nat))
    (lp : List (Nat × Nat)) (ab : List Nat) : Bool :=
  runP mul ONE prg List.nil [B, A, ONE] 3 fun bl cur n =>
    sB (lk ONE bl cur n rx) fun X =>
    mapS (lk ONE bl cur n) sg fun hs =>
    pows mul ONE hs fun pw =>
      andB (Nat.beq (lenN hs) 6) (andB (notB (Nat.beq X ONE))
        (andB (Nat.beq (pw1 mul X 4) ONE) (andB (Nat.beq X Xg)
          (andB (relsOK mul ONE hs pw rel 0 0)
            (clK mul ONE A B (lk ONE bl cur n) pw hs X es lp ab)))))

end CFSG.KC.SlpPc

end
