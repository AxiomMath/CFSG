module

public import Certificates.Kernel.Co2Census.S0Defs
public import Certificates.Kernel.Co2Census.SpinData
public import Certificates.Kernel.Co2SmithS.Lets

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.KC.Co2InvS CFSG.KC.Co2Census CFSG.KC.Loop

@[expose] noncomputable def Z0 : Nat := KernelCo2SmithS.LT 0

@[expose] def v0 : List Nat := [1, 0, 0, 0, 0, 0, 0, 0]

@[expose] def nzV (b : List Nat) : Bool := b.any fun x => !Nat.beq x 0 && Nat.blt x spP

@[expose] def sgnV (a b : List Nat) : Nat := if a == b then 0 else if a == negVP b then 1 else 2

@[expose] noncomputable def twistK (k X : Nat) : Nat := if k = 1 then mulV X Z0 else X

@[expose] noncomputable def s0Cond (n nr nc : Nat) (comm : Bool) : Bool :=
  Nat.beq (mulV (SK n) (SK n)) (SK nc) &&
    (!comm || Nat.beq (mulV (SK n) (SK nr)) (mulV (SK nr) (SK n)))

@[expose] noncomputable def kComm (n nr : Nat) : Nat :=
  sgnV (spinMV n (spinMV nr v0)) (spinMV nr (spinMV n v0))

@[expose] noncomputable def kSq (n nc : Nat) : Nat := sgnV (spinMV n (spinMV n v0)) (spinMV nc v0)

@[expose] noncomputable def fcK (QK : Nat → Nat) (n nr nc RR CR : Nat) (comm : Bool) : Nat :=
  strictN RR fun RR => strictN CR fun CR =>
    if s0Cond n nr nc comm then
      strictN (kComm n nr) fun k1 => strictN (kSq n nc) fun k2 => strictN (SK n) fun S =>
        strictN (twistK k2 CR) fun T2 =>
          ((List.range 512).filter fun e => letB (mulV S (QK e)) fun Y =>
            Nat.beq (mulV Y Y) T2 && (!comm || Nat.beq (mulV Y RR) (twistK k1 (mulV RR Y)))).length
    else 0

@[expose] noncomputable def fcOK (n nr nc : Nat) (comm : Bool) : Bool :=
  !s0Cond n nr nc comm || ((!comm || (Nat.blt (kComm n nr) 2 &&
      nzV (spinMV nr (spinMV n v0)))) && Nat.blt (kSq n nc) 2 && nzV (spinMV nc v0))

@[expose] def fld21 (r j : Nat) : Nat := Nat.land (Nat.shiftRight r (Nat.mul 21 j)) 2097151

@[expose] noncomputable def genOK (QK G GR GI : Nat → Nat) (er nr l : Nat) : Bool :=
  letB (G l) fun g => letB (fld21 g 0) fun e => letB (fld21 g 1) fun m =>
    letB (SK m) fun Sm => letB (SK nr) fun Sr => letB (kComm m nr) fun k =>
    Nat.blt e 512 && Nat.beq (GR l) Sm && Nat.beq (mulV (GR l) (GI l)) IDP &&
      Nat.blt (GI l) (2 ^ 484) && Nat.beq (mulV Sm Sr) (mulV Sr Sm) &&
      Nat.blt k 2 && nzV (spinMV nr (spinMV m v0)) &&
      Nat.beq (mulV (mulV Sm (QK e)) (mulV Sr (QK er)))
        (twistK k (mulV (mulV Sr (QK er)) (mulV Sm (QK e))))

@[expose] noncomputable def rootOK (Pt IX RT : Nat → Nat) (N nr nc : Nat) (comm : Bool)
    (j : Nat) : Bool :=
  letB (RT j) fun rr => letB (fld21 rr 0) fun k => letB (fld21 rr 1) fun n =>
    Nat.blt k N && Nat.beq (rtOf IX k) k && Nat.beq (Pt k) (SK n) && Nat.blt n 1451520 &&
      fcOK n nr nc comm && (Nat.beq j 0 || Nat.blt (fld21 (RT (j - 1)) 0) k)

@[expose] noncomputable def coverRootK (IX RT : Nat → Nat) (nroots i : Nat) : Bool :=
  (List.range nroots).any fun j => Nat.beq (rtOf IX i) (fld21 (RT j) 0)

@[expose] noncomputable def totalK (QK IX RT : Nat → Nat) (N hi nroots nr nc RR CR : Nat)
    (comm : Bool) : Nat :=
  ((List.range nroots).map fun j =>
    rootCount IX N hi (fld21 (RT j) 0) * fcK QK (fld21 (RT j) 1) nr nc RR CR comm).sum

@[expose] noncomputable def fibOK (QK F : Nat → Nat) (er nr j : Nat) : Bool :=
  letB (F j) fun f => letB (fld21 f 0) fun e2 => letB (fld21 f 1) fun eh =>
    letB (fld21 f 2) fun nh => letB (SK nh) fun Sh => letB (SK nr) fun Sr =>
      letB (kComm nh nr) fun k =>
      Nat.blt e2 512 && Nat.blt eh 512 && Nat.blt nh 1451520 &&
        (Nat.beq j 0 || Nat.blt (fld21 (F (j - 1)) 0) e2) &&
        Nat.beq (mulV Sh Sr) (mulV Sr Sh) &&
        Nat.blt k 2 && nzV (spinMV nr (spinMV nh v0)) &&
        Nat.beq (mulV (mulV Sh (QK eh)) (mulV Sr (QK er)))
          (twistK k (mulV (mulV Sr (QK e2)) (mulV Sh (QK eh))))

end CertificateChecks.KernelCo2Census

end
