
module

public import CFSG.Monster.B.E6.StdF4Opposite
import CFSG.Certificates.Kernel.TabBThreeL1.Inverters

public section

open CFSG.HardMathSupport.Dickson.I271.TabBThreeL1

namespace Certificates

open CFSG.LieType.Chevalley.C2E6Std CFSG.Monster.B.E6.StdF4 in
theorem certificate17575 : ∀
    {x : stdGroup}, x ∈ rootClass → x * (rootInv * tMinus) * x⁻¹ = (rootInv * tMinus)⁻¹ →
      x = rootInv ∨ x = tMinus ∨ x = rootInv * tMinus * rootInv :=
  fun hx hinv => ch17575_inverts_of_certificates hx hinv

end Certificates
