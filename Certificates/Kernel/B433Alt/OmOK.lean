module

public import Certificates.Kernel.B433Alt.Data.St
public import Certificates.Kernel.B433Alt.Data.Om
public import Certificates.Data.Kernel.B433Alt.Om
public import CFSG.YGroups.Defs

public section

namespace CFSG.KD.B4AN

open CFSG.KC.B4A

@[expose] def LIVE : Nat := 0xbe7fffe85f0efff

@[expose] def F432W : List Nat := (List.replicate 9 [0, 5, 6, 7, 8, 9, 1]).flatten

@[expose] def omRels : List (List Nat) := CFSG.YGroups.yRels 4 3 2 ++ [F432W]

@[expose] noncomputable def masksChk (_ : Nat) : Bool := masksOK19 MS

@[expose] noncomputable def netColChk (k : Nat) : Bool := netColOK MS CB (k / 19) (k % 19)

@[expose] noncomputable def relChk (i : Nat) : Bool := relOK MS (omRels.getD i [])

@[expose] noncomputable def orbChk (_ : Nat) : Bool := omOrbitOK MS 72

@[expose] noncomputable def tFixChk (c : Nat) : Bool := Nat.beq (colAt CB c 0) 0

@[expose] def NSEG : Nat := 1975

@[expose] noncomputable def segK (k : Nat) : Bool :=
  segChk MS CFSG.KD.B4A.RD CFSG.KD.B4A.RW CFSG.KD.B4A.PW CB LIVE RN RL GS XO SJ ST SA SN STL NSEG k

@[expose] noncomputable def finK (j : Nat) : Bool :=
  finChk CFSG.KD.B4A.RD CFSG.KD.B4A.RW CFSG.KD.B4A.PW CB LIVE RN RL GS GN XO SJ ST SA SN STL NSEG j

end CFSG.KD.B4AN

end
