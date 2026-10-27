module

public import Certificates.Kernel.Co1M.Data10072
public import Certificates.Kernel.Co1Cover.Data
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.J4Q.VOrb
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.J4Q CFSG.KD.Co1M CFSG.KC.LQT.Syl CFSG.KC.Co1F2 CertificateChecks.KernelCo1Cover

@[expose] def cmCode4 : Nat := 10075731

@[expose] noncomputable def CH72 : List (List Nat) :=
  [FC0, FC1, FC2, FC3, FC4, FC5, FC6, FC7, FC8, FC9, FC10, FC11, FC12, FC13, FC14, FC15, FC16, FC17,
    FC18, FC19, FC20, FC21, FC22, FC23, FC24, FC25, FC26, FC27, FC28, FC29, FC30, FC31]

@[expose] noncomputable def SPC72 : List (List Nat) :=
  [FS0, FS1, FS2, FS3, FS4, FS5, FS6, FS7, FS8, FS9, FS10, FS11, FS12, FS13, FS14, FS15, FS16, FS17,
    FS18, FS19, FS20, FS21, FS22, FS23, FS24, FS25, FS26, FS27, FS28, FS29, FS30, FS31]

@[expose] noncomputable def cmPch : List (List Nat) :=
  List.cons (List.cons cmCode4 List.nil) (List.map (List.map fun e => Nat.land e RM112) CH72)

@[expose] noncomputable def cm72T (i : Nat) : Bool :=
  vtChunkK RM112 GT3 (vptsK RM112 cmCode4 CH72.flatten) (CH72.getD i []) (FCP0.getD i 0) (1 + 1024 * i)

@[expose] noncomputable def cm72I (i : Nat) : Bool := inSK (cmPch.getD i []) SPC72.flatten

@[expose] noncomputable def cm72S (i : Nat) : Bool := spInK (SPC72.getD i []) cmPch

@[expose] noncomputable def cm72C (i : Nat) : Bool := clK GT3 (cmPch.getD i []) SPC72.flatten

#j4q_all CFSG.KD.Co1M.T72 CertificateChecks.KernelCo1M.cm72T 32
#j4q_all CFSG.KD.Co1M.I72 CertificateChecks.KernelCo1M.cm72I 33
#j4q_all CFSG.KD.Co1M.S72 CertificateChecks.KernelCo1M.cm72S 32
#j4q_all CFSG.KD.Co1M.C72 CertificateChecks.KernelCo1M.cm72C 33

theorem cm72_size : andB (Nat.beq (CH72.flatten.length + 1) 32400)
    (andB (Nat.beq SPC72.flatten.length 32400)
      (andB (allR 31 fun i => Nat.beq (CH72.getD i []).length 1024)
        (andB (CH72.all fun ch => Nat.ble ch.length 1024) (SPC72.all fun sc => Nat.ble sc.length 1024)))) =
    true := by quickRfl

theorem cm72_sinc : sincK SPC72.flatten 0 = true := by quickRfl

end CertificateChecks.KernelCo1M

end
