module

public import CFSG.Sporadic.HN.F5Chain
public import Certificates.Data.Kernel.HNLocal.W
public import Certificates.Data.CFSGNative.HN.Local.InvData
public import Certificates.Data.CFSGNative.HN.Local.AltData
public import Certificates.Data.CFSGNative.HN.Local.TypeData
public import CFSG.Certificates.Kernel.HNLocal.Defs

public section

namespace CFSG.Sporadic.HN.LocalK

open CFSG.Sporadic.F5 CFSG.Sporadic.Fi23

abbrev dHN : CFSG.Sporadic.F5.Native.F5Data := CFSG.Sporadic.HN.Native.hnData

noncomputable abbrev wG (j : ℕ) : J dHN :=
  slpG (genG dHN) CFSG.Sporadic.HN.Local.Native.invWords j

@[expose] noncomputable def rootV : Vec dHN := CFSG.KS.HNLocal.cvec CFSG.KD.HNLocal.V0

@[expose] noncomputable def hnW (k : Fin 462) : Vec dHN :=
  CFSG.KS.HNLocal.cvec (CFSG.KC.HNLocal.recX CFSG.KD.HNLocal.WC (2 ^ 399 - 1) k.val)

@[expose] def pi2 (k : Fin 462) : Fin 462 :=
  ⟨CFSG.Sporadic.HN.Local.Native.altPi2[k.val]! % 462, Nat.mod_lt _ (by norm_num)⟩

@[expose] def pi3 (k : Fin 462) : Fin 462 :=
  ⟨CFSG.Sporadic.HN.Local.Native.altPi3[k.val]! % 462, Nat.mod_lt _ (by norm_num)⟩

@[expose] def pit2 (k : Fin 462) : Fin 462 :=
  ⟨CFSG.Sporadic.HN.Local.Native.typePi2[k.val]! % 462, Nat.mod_lt _ (by norm_num)⟩

@[expose] def pit4 (k : Fin 462) : Fin 462 :=
  ⟨CFSG.Sporadic.HN.Local.Native.typePi4[k.val]! % 462, Nat.mod_lt _ (by norm_num)⟩

end CFSG.Sporadic.HN.LocalK
