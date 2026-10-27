module

public import Certificates.Data.Kernel.L34Scan2

public section

namespace CFSG.KC.L34Pow

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.L34Scan2

@[expose] noncomputable def with945 (x : Nat) (k : Nat → Bool) : Bool :=
  strictB (ppowK x 3) fun a => strictB (ppowK a 3) fun b => strictB (ppowK b 3) fun c =>
    strictB (ppowK c 5) fun d => strictB (ppowK d 7) k

@[expose] noncomputable def with944 (x : Nat) (k : Nat → Bool) : Bool :=
  strictB (ppowK x 2) fun a => strictB (ppowK a 2) fun b => strictB (ppowK b 2) fun c =>
    strictB (ppowK c 2) fun d => strictB (ppowK d 59) k

end CFSG.KC.L34Pow

end
