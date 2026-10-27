module

public import CFSG.RankThree.Native.F2K
public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.Certificates.Kernel.RankThree.F2Perm
public import Std.Data.HashMap

public section

namespace CFSG.KS.Co2M

open CFSG.KC.Enum CFSG.RankThree.Native.F2

@[expose] noncomputable def M22 : ℕ := nat_lit 4194303

@[expose] noncomputable def L22 : ℕ :=
  nat_lit 11908528498073666995947969347157480251659827695481117700305989184378417062648132460131015248306064568667840854116287251142124832390176047105

@[expose] noncomputable def I22 : ℕ :=
  nat_lit 24973991379659707467621756579723706896969316949376236904045051527405272766968242940994766581490570014503808294292943339053779062356439532262391809

@[expose] noncomputable def vmK (v M : ℕ) : ℕ := vmulK (nat_lit 22) M22 v M

@[expose] noncomputable def mmK (A B : ℕ) : ℕ := mulK (nat_lit 22) M22 L22 A B

@[expose] noncomputable def VG (PV i : ℕ) : ℕ := pg (nat_lit 22) M22 PV i

@[expose] noncomputable def bindK (PV P M MI : ℕ) : Bool :=
  allN (nat_lit 2300) (fun i => Nat.blt (pg (nat_lit 12) (nat_lit 4095) P i) (nat_lit 2300) &&
    Nat.beq (VG PV (pg (nat_lit 12) (nat_lit 4095) P i)) (vmK (VG PV i) M)) &&
  Nat.beq (mmK M MI) I22 && Nat.beq (mmK MI M) I22

end CFSG.KS.Co2M

end
