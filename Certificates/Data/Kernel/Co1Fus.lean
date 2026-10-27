module

public import Certificates.Data.Kernel.F2Dag

public section

namespace CFSG.KC.F2Dag

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2

@[expose] noncomputable def fusAt (d T x c w p : Nat) : Bool :=
  andB (andB (canonF d (mulF d x T)) (canonF d (mulF d T x)))
  (andB (andB (canonF d (mulF d c T)) (canonF d (mulF d T c)))
  (andB (andB (canonF d (powL d x p)) (andB (canonF d x) (canonF d (idF d))))
  (andB (andB (canonF d (mulF d c c)) (andB (canonF d (mulF d w w)) (canonF d w)))
  (andB (Nat.beq (mulF d x T) (mulF d T x)) (andB (Nat.beq (mulF d c T) (mulF d T c))
  (andB (Nat.beq (powL d x p) (idF d)) (andB (notB (Nat.beq x (idF d)))
  (andB (Nat.beq (mulF d c c) (idF d)) (andB (Nat.beq (mulF d w w) (idF d))
    (notB (Nat.beq w (idF d))))))))))))

@[expose] noncomputable def fusK (d T : Nat) (E : List Nat) (ix ic p k : Nat) : Bool :=
  strictB (E.getD ix (idF d)) fun x => strictB (E.getD ic (idF d)) fun c =>
    strictB (powL d (mulF d (mulF d (mulF d (powL d x (p - 1)) c) x) c) k) fun w =>
      fusAt d T x c w p

end CFSG.KC.F2Dag

end
