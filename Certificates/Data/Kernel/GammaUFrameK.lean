module

public import Certificates.Data.Kernel.GammaUNormK

public section

namespace CFSG.KC.GUV

open CFSG.KC.IF4C

@[expose] noncomputable def intoOK (A : Nat) (ds S : List Nat) : Bool :=
  ds.all fun d => memN (ap12 A d) S

@[expose] noncomputable def sjAt (D0 : List Nat) (g gi T T' : Nat) : Bool :=
  intoOK (mulP g T) D0 (CFSG.GF2Type.Smith1979.GammaU.spanList (D0.map (ap12 T'))) &&
    intoOK (mulP gi T') D0 (CFSG.GF2Type.Smith1979.GammaU.spanList (D0.map (ap12 T)))

@[expose] noncomputable def dtOK (TH T : Nat) : Bool := guOK TH T && Nat.beq (ap12 T 3072) 3072

end CFSG.KC.GUV

end
