module

public import Certificates.Data.Kernel.Hall82K.C5
public import Certificates.Data.Kernel.Hall82K.Bridge
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaData

public section

namespace CFSG.KC.Hall82K

@[expose] def hexaMGensK : List Nat := [4439643498, 34633937090]

@[expose] noncomputable def kPresK (g : Nat) : Bool :=
  allN (fun v => bor (Bool.rec (motive := fun _ => Bool) true false (inKK v)) (inKK (apL g v))) 64

end CFSG.KC.Hall82K
