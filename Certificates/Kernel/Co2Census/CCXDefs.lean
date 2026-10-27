module

public import Certificates.Kernel.Co2Census.HPDefs

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.KC.Co2InvS CFSG.KC.Co2Census CFSG.KC.Loop

@[expose] noncomputable def commK (a b : Nat) : Bool := Nat.beq (mulV a b) (mulV b a)

@[expose] noncomputable def dlK (QK : Nat → Nat) (R : Nat) : List Nat :=
  (List.range 512).filter fun e => commK (QK e) R

@[expose] noncomputable def certX (QK : Nat → Nat) (o c m : Nat) : Nat :=
  mulV (SK (fld21 c (o + 4 * m + 1))) (QK (fld21 c (o + 4 * m)))

@[expose] noncomputable def certXI (QK : Nat → Nat) (o c m : Nat) : Nat :=
  mulV (SK (fld21 c (o + 4 * m + 3))) (QK (fld21 c (o + 4 * m + 2)))

@[expose] noncomputable def certProd (QK : Nat → Nat) (o c d len : Nat) : Nat :=
  (List.range len).foldr (fun m acc =>
    mulV (mulV (mulV (certX QK o c m) d) (certXI QK o c m)) acc) IDP

@[expose] noncomputable def certXOK (QK : Nat → Nat) (o c R len : Nat) : Bool :=
  (List.range len).all fun m =>
    Nat.blt (fld21 c (o + 4 * m)) 512 && Nat.blt (fld21 c (o + 4 * m + 2)) 512 &&
      commK (certX QK o c m) R && Nat.beq (mulV (certX QK o c m) (certXI QK o c m)) IDP

end CertificateChecks.KernelCo2Census

end
