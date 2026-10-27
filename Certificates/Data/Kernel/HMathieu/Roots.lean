module

public import Certificates.Data.Kernel.HMathieu.Bfs
public import Certificates.Data.Kernel.TreeK
public import Certificates.Data.Kernel.MathieuAut.InAutK

public section

namespace CFSG.KC.HMathieu

open CFSG.KC.Enum CFSG.KS CFSG.KS.MathieuAut

@[expose] noncomputable def stabK : Nat → Nat → Bool
  | 0, _ => true
  | 1, g => Nat.beq (pg 5 (mask 5) g 0) 0
  | _ + 2, g => Nat.beq (pg 5 (mask 5) g 0 + pg 5 (mask 5) g 1) 1

@[expose] noncomputable def genK (t g : Nat) : Bool :=
  vpK g && inAutKL ((List.range 24).map (pg 5 (mask 5) g)) && stabK t g

@[expose] noncomputable def rootK (t np : Nat) (gs E : List Nat) : Bool :=
  gs.all (genK t) && CFSG.KC.TreeK.closedK (fun l x => pc24 (gs.getD l 0) x) gs.length np E

end CFSG.KC.HMathieu

end
