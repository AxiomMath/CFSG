module

public import Certificates.Data.OmegaTypes
public import Certificates.Data.OmegaInv

public section

namespace Certificates.OmegaSwap

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Sporadic.Schreier

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def swapAll (A0 KAl KBl : List P45) (tAe : P45) : Bool :=
  A0.all fun u =>
    !decide (u * u = 1) || decide (u = 1) || !decide (u * tAe = tAe * u) ||
      !decide (Certificates.OmegaInv.fixCnt u = 15) || Certificates.OmegaTypes.swapChk KAl KBl u

@[expose] def check (_ : Unit := ()) : Bool :=
  let KAl := Certificates.OmegaTypes.kaList ()
  swapAll (elemsT QA45) KAl (Certificates.OmegaPk.kbList (Certificates.OmegaPk.g0 ()) KAl)
    (Certificates.P43Twin.tA ())

end Certificates.OmegaSwap
