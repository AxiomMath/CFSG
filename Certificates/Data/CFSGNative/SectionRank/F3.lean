module

public import Certificates.Data.CFSGNative.SectionRank.Elem3
public import Certificates.Data.CFSGNative.F3.Basic

public section

namespace CFSG.SectionRank.Native

open CFSG.F3.Native

@[expose] def ops3 (d : Nat) : Ops (Array V) V where
  decode := rowsOf d
  mul := mul d
  one := idM d
  eq := eqM d
  vmul v X := comb d X v
  unit k := ⟨1 <<< k, 0⟩
  vne u w := (List.range d).any fun j => u.get j != w.get j

end CFSG.SectionRank.Native
