module

public import Certificates.Data.Kernel.PermCent.CV

public section

namespace CFSG.Certificates.Kernel.PkCV.KGrp

instance smallTen : Small 10 := ⟨by decide⟩
instance smallEleven : Small 11 := ⟨by decide⟩

variable {n : Nat} [Small n]

@[expose] noncomputable def q8c2atC (c : CV n) (C : List (CV n)) : Bool :=
  C.all fun a => bif powOneC a 4 && !powOneC a 2 && !decide (c = a ^ 2) then
    C.all fun b => !(decide (b ^ 2 = a ^ 2) && eq22C b a a⁻¹ b) else true

@[expose] noncomputable def q8c2freeC (L : List (CV n)) : Bool :=
  L.all fun c => bif powOneC c 2 && !decide (c = 1) then
    q8c2atC c (L.filter fun g => eq22C g c c g) else true

end CFSG.Certificates.Kernel.PkCV.KGrp

end
