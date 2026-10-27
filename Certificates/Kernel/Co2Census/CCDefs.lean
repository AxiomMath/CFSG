module

public import Certificates.Kernel.Co2Census.HPDefs

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.KC.Co2InvS CFSG.KC.Co2Census CFSG.KC.Loop

@[expose] noncomputable def fcC (QK : Nat → Nat) (n nr nc RR CR : Nat) (comm : Bool) : Nat :=
  strictN RR fun RR => strictN CR fun CR =>
    if s0Cond n nr nc comm then
      strictN (SK n) fun S =>
        ((List.range 512).filter fun e => letB (mulV S (QK e)) fun Y =>
          Nat.beq (mulV Y Y) CR && (!comm || Nat.beq (mulV Y RR) (mulV RR Y))).length
    else 0

@[expose] noncomputable def genOKC (QK G GR GI : Nat → Nat) (er nr l : Nat) : Bool :=
  letB (G l) fun g => letB (fld21 g 0) fun e => letB (fld21 g 1) fun m =>
    letB (SK m) fun Sm => letB (mulV (SK nr) (QK er)) fun R => letB (mulV Sm (QK e)) fun W =>
    Nat.blt e 512 && Nat.beq (GR l) Sm && Nat.beq (mulV (GR l) (GI l)) IDP &&
      Nat.blt (GI l) (2 ^ 484) && Nat.beq (mulV W R) (mulV R W)

@[expose] noncomputable def rootOKC (Pt IX RT : Nat → Nat) (N j : Nat) : Bool :=
  letB (RT j) fun rr => letB (fld21 rr 0) fun k => letB (fld21 rr 1) fun n =>
    Nat.blt k N && Nat.beq (rtOf IX k) k && Nat.beq (Pt k) (SK n) && Nat.blt n 1451520 &&
      (Nat.beq j 0 || Nat.blt (fld21 (RT (j - 1)) 0) k)

@[expose] noncomputable def totalC (QK IX RT : Nat → Nat) (N hi nroots nr nc RR CR : Nat)
    (comm : Bool) : Nat :=
  ((List.range nroots).map fun j =>
    rootCount IX N hi (fld21 (RT j) 0) * fcC QK (fld21 (RT j) 1) nr nc RR CR comm).sum

@[expose] noncomputable def fibOKC (QK F : Nat → Nat) (er nr j : Nat) : Bool :=
  letB (F j) fun f => letB (fld21 f 0) fun e2 => letB (fld21 f 1) fun eh =>
    letB (fld21 f 2) fun nh => letB (mulV (SK nh) (QK eh)) fun H => letB (SK nr) fun Sr =>
      Nat.blt e2 512 && Nat.blt eh 512 &&
        (Nat.beq j 0 || Nat.blt (fld21 (F (j - 1)) 0) e2) &&
        Nat.beq (mulV H (mulV Sr (QK er))) (mulV (mulV Sr (QK e2)) H)

@[expose] noncomputable def repOKC (R Z : Nat) : Bool :=
  Nat.beq (mulV R R) IDP && !Nat.beq R IDP && !Nat.beq R Z

@[expose] noncomputable def ceK (QK : Nat → Nat) (R : Nat) : Nat :=
  ((List.range 512).filter fun e => letB (QK e) fun q => Nat.beq (mulV q R) (mulV R q)).length

@[expose] noncomputable def invEK (QK : Nat → Nat) (R : Nat) : Nat :=
  ((List.range 512).filter fun e => letB (mulV R (QK e)) fun Y => Nat.beq (mulV Y Y) IDP).length

end CertificateChecks.KernelCo2Census

end
