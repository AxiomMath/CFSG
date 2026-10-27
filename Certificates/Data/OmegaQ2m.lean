module

public import Certificates.Data.OmegaInv
public import Certificates.Data.P43Twin

public section

namespace Certificates.OmegaQ2m

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Sporadic.Schreier

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def conjChk (P0 : List P45) (a z : P45) : Bool :=
  P0.any fun g => decide (g * a * g⁻¹ = z)

@[expose] def qChk (A0 Q : List P45) (z : P45) : Bool :=
  Q.all fun q => !decide (q * q = 1) || decide (q = 1) || decide (q = z) ||
    decide (Certificates.OmegaInv.cntL A0 q = 192)

@[expose] def check (_ : Unit := ()) : Bool :=
  let z := Certificates.OmegaT0.z0 ()
  conjChk (elemsT QP45) (Certificates.P43Twin.tA ()) z &&
    qChk (elemsT QA45) (Certificates.OmegaF1051.q0l ()) z

end Certificates.OmegaQ2m
