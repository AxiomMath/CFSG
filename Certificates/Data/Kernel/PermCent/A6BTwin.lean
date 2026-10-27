module

public import Certificates.Data.Kernel.PermCent.SmallB
public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamA6Inputs
public import CFSG.GH74.KGroups.A6Inputs

public section

namespace CFSG.Certificates.Kernel.PkCV.A6B

open CFSG.GH74.KGroups.A6

@[expose] noncomputable def evenOrdC (g : CV 10) : Bool := orderIsP g 2 [2] || orderIsP g 4 [2]

@[expose] noncomputable def witC (κ : CV 10) (H : List (CV 10)) : Bool :=
  H.any fun g => H.any fun h => evenOrdC ((κ * g * κ⁻¹ * g⁻¹) * (h * (κ * g * κ⁻¹ * g⁻¹) * h⁻¹))

@[expose] noncomputable def a6C : Bool :=
  ((elemsC QP).all fun g => orderIsP g 1 [] || orderIsP g 2 [2] || orderIsP g 3 [3] ||
    orderIsP g 4 [2] || orderIsP g 5 [5]) &&
  ((elemsC QA).all fun τ => bif decide (τ * τ = 1 ∧ τ ≠ 1) then
    (let H := (elemsC QP).filter fun κ => decide (τ * κ = κ * τ)
     H.all fun κ => bif orderIsP κ 3 [3] then witC κ H else true)
   else true)

end CFSG.Certificates.Kernel.PkCV.A6B

end
