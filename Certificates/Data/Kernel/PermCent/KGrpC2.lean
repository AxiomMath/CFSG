module

public import Certificates.Data.Kernel.PermCent.CV

public section

namespace CFSG.Certificates.Kernel.PkCV.KGrp

variable {n : Nat} [Small n]

@[expose] noncomputable def centInC (LA LS : List (CV n)) : Bool :=
  LA.all fun σ => !(LS.all fun q => eq22C σ q q σ) || decide (σ ∈ LS)

@[expose] noncomputable def oddCoreAtC (m : Nat) (CA CP : List (CV n)) : Bool :=
  CA.all fun x =>
    bif !decide (x = 1) && decide (x ^ m = 1) then
      CP.any fun c => !decide ((x * c * x⁻¹ * c⁻¹) ^ m = 1)
    else true

@[expose] noncomputable def oddCoreCheckC (m : Nat) (LA LP : List (CV n)) : Bool :=
  LA.all fun τ =>
    bif powOneC τ 2 && !decide (τ = 1) then
      oddCoreAtC m (LA.filter fun g => eq22C g τ τ g) (LP.filter fun c => eq22C c τ τ c)
    else true

end CFSG.Certificates.Kernel.PkCV.KGrp

end
