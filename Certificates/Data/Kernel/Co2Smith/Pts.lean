module

public import Certificates.Data.Kernel.Co2Smith.Rows
public import Certificates.Data.Kernel.SporSch.Co2M
public import Certificates.Data.Kernel.M1F2

public section

namespace CFSG.KC.Co2Smith

open CFSG.KC.Enum CFSG.KS.Co2M CFSG.KC.M1F2

@[expose] noncomputable def bindVK (PV P T : Nat) : Bool :=
  allN (nat_lit 2300) fun i => Nat.blt (pg (nat_lit 12) (nat_lit 4095) P i) (nat_lit 2300) &&
    Nat.beq (VG PV (pg (nat_lit 12) (nat_lit 4095) P i)) (vmF (nat_lit 22) T (VG PV i))

@[expose] noncomputable def fixCntK (P : Nat) : Nat :=
  ((List.range 2300).filter fun i => Nat.beq (pg (nat_lit 12) (nat_lit 4095) P i) i).length

end CFSG.KC.Co2Smith
