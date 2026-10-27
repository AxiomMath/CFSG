module

public import Certificates.Data.GH74EvSporCheck
public meta import Certificates.Data.GH74EvSporCheck

public section

namespace Certificates.IvkCent

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.GH74.Generic.S45.EvSpor
open CFSG.ComponentClassification.M12Cover (q2Gens)
open CFSG.Sporadic.Schreier (toTable)

@[expose] def m12Q2Gens : List Table := q2Gens.map toTable

@[expose] def m12C2B : Array Table := closArr 24 cap m12Q2Gens

@[expose] def m12CentKaOK : Bool :=
  enumOK 24 cap m12Q2Gens 384 && invsOK 24 m12C2B &&
    m12C2B.all (fun x => !commTT 24 x m12KaB || tblEq 24 x (idT 24) || tblEq 24 x m12ZT ||
      tblEq 24 x m12ST || tblEq 24 x (compT 24 m12ST m12ZT))

end Certificates.IvkCent
