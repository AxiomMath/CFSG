module

public import Certificates.Data.Kernel.Ivk8NormP
public import Certificates.Data.Kernel.Ivk8Cent

public section

namespace CFSG.KS.Ivk8NormP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Ivk8Cent

@[expose] noncomputable def chkPK (n w p c ci cnt : Nat) (T : Nat → Nat) (hs : List (Nat × Nat)) :
    Bool :=
  allN cnt (fun i => strictB (pc n w c (pc n w (T i) ci)) (fun x => okP n w p hs x))

end CFSG.KS.Ivk8NormP

end
