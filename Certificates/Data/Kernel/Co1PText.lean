module

public import Certificates.Data.Kernel.Griess13.Packed

public section

namespace CFSG.KC.Co1P

@[expose] noncomputable def natsC (L : List Nat) : List Char := [','].intercalate (L.map CFSG.KC.G13.natC)

@[expose] noncomputable def pairC (p : Nat × Nat) : List Char :=
  [','].intercalate [CFSG.KC.G13.natC p.1, CFSG.KC.G13.natC p.2]

@[expose] noncomputable def pairsC (P : List (Nat × Nat)) : List Char := [';'].intercalate (P.map pairC)

end CFSG.KC.Co1P

end
