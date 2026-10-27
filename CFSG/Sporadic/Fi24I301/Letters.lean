module

public import CFSG.Sporadic.FischerOddCore.Fi24R2Order

public section

namespace CFSG.Sporadic.Fi24I301

open CFSG.Sporadic.FischerOddCore

@[expose] noncomputable def kLet (z : ℤ) : Equiv.Perm (Fin 504) :=
  if z = 1 then fi24Sa else if z = -1 then fi24Sa⁻¹ else if z = 2 then fi24Sb else fi24Sb⁻¹

@[expose] noncomputable def pLet (z : ℤ) : Equiv.Perm (Fin 378) :=
  if z = 1 then fi24Pa else if z = -1 then fi24Pa⁻¹ else if z = 2 then fi24Pb else fi24Pb⁻¹

end CFSG.Sporadic.Fi24I301

end
