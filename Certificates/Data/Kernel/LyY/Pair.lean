module

public import Certificates.Data.Kernel.LyY.Scan

public section

namespace CFSG.KC.LyY

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Child3 CFSG.KC.J2Enum CFSG.KS.Mathieu

@[expose] noncomputable def wordFix (n w X XI Y YI : Nat) (wd : List Int) : Bool :=
  allN n (fun p => Nat.beq (wP (fun q => pg w (mask w) X q) (fun q => pg w (mask w) XI q)
    (fun q => pg w (mask w) Y q) (fun q => pg w (mask w) YI q) wd p) p)

end CFSG.KC.LyY

end
