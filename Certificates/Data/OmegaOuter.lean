module

public import Certificates.Data.OmegaB0
public import Certificates.Data.OmegaInv

public section

namespace Certificates.OmegaOuter

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Sporadic.Schreier

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def b0Elems (_ : Unit := ()) : List P45 :=
  Certificates.OmegaB0.bElems (Certificates.OmegaB0.phiTable (Certificates.OmegaB0.bl ()))
    (Certificates.OmegaB0.allVecs ())

@[expose] def outerChk (A0 P0 Bl : List P45) : Bool :=
  A0.all fun a =>
    !decide (a * a = 1) || decide (a ∈ P0) || !(Bl.all fun x => decide (a * x * a⁻¹ ∈ Bl)) ||
      Bl.any fun β => decide (a * β = β * a) && decide (Certificates.OmegaInv.fixCnt (a * β) = 15)

@[expose] def check (_ : Unit := ()) : Bool :=
  outerChk (elemsT QA45) (elemsT QP45) (b0Elems ())

end Certificates.OmegaOuter
