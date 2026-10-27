module

public import Certificates.Data.OmegaPk

public section

namespace Certificates.OmegaTypes

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ClassicalInvolution.Q3.TA3.Check Certificates.P43Twin Certificates.OmegaPk

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def swapChk (KAl KBl : List P45) (u : P45) : Bool :=
  (KAl.all fun k => memB KBl (u * k * u⁻¹)) && KBl.all fun k => memB KAl (u * k * u⁻¹)

@[expose] def stabChk (KAl KBl : List P45) (u : P45) : Bool :=
  (KAl.all fun k => memB KAl (u * k * u⁻¹)) && KBl.all fun k => memB KBl (u * k * u⁻¹)

@[expose] def kaList (_ : Unit := ()) : List P45 := (allSL ()).map (rhoOf (rhoTab ()))

end Certificates.OmegaTypes
