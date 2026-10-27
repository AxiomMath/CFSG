module

public import CFSG.CGT.Stroth77.NonSplit.Type100MnsInputs

public section

namespace CertificateChecks.KernelDirect.C778704

open CFSG.CGT.Stroth77

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem toA_add : ∀ x y : Torus (Type100.k 1), toA (x + y) = toA x * toA y := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem toA_inj : ∀ x y : Torus (Type100.k 1), toA x = toA y → x = y := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem toA_mem : ∀ x : Torus (Type100.k 1), toA x ∈ bfsList gensA 60 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem toA_uv :
    ∀ x : Torus (Type100.k 1), toA ((Type100.action 1).φuv x) = mnsUV⁻¹ * toA x * mnsUV := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem toA_t :
    ∀ x : Torus (Type100.k 1), toA ((Type100.action 1).φt x) = mnsT⁻¹ * toA x * mnsT := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem toA_u :
    ∀ x : Torus (Type100.k 1), toA ((Type100.action 1).φu x) = mnsU⁻¹ * toA x * mnsU := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem toA_rho :
    ∀ x : Torus (Type100.k 1), toA ((Type100.action 1).φρ x) = mnsRho⁻¹ * toA x * mnsRho := by
  decide +kernel

end CertificateChecks.KernelDirect.C778704
