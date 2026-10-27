module

public import CFSG.Certificates.Kernel.Schur.ModelM24
public import CFSG.Certificates.Kernel.Schur.Words

public section

namespace CFSG.KC.Schur.Id

@[expose] def winvK (w : List (Nat × Bool)) : List (Nat × Bool) :=
  (w.map fun x => (x.1, !x.2)).reverse

@[expose] def substK (ims : List (List (Nat × Bool))) (w : List (Nat × Bool)) :
    List (Nat × Bool) :=
  w.flatMap fun x => if x.2 then ims.getD x.1 [] else winvK (ims.getD x.1 [])

@[expose] noncomputable def idOK (w : List (Nat × Bool)) : Bool :=
  w.all (fun x => Nat.blt x.1 2) &&
    Nat.beq (McL.evalW Schur.M24.MG 24 (Schur.Pack.pk w) w.length) (McL.pid 24)

end CFSG.KC.Schur.Id

end
