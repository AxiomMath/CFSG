
module

public import Certificates.Certificate4182Base

public import Certificates.Data.TwoF4LocCheck
public import Certificates.Data.TitsLocData
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Schreier.TitsActionCheckInputs
public import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
public import Certificates.Data.TwoF4LieCheck
public import CFSG.Sporadic.Schreier.TitsAction
public import Mathlib.Logic.Relation
public import CFSG.Sporadic.Schreier.TitsCert
import Certificates.Kernel.TitsLoc.Glue
import Certificates.Kernel.TwoF4Lie.Glue
import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Spec
public import Certificates.Certificate4180Base

public section

open CFSG.Sporadic.Schreier.Tits

open scoped Pointwise

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier.Tits in
open scoped Pointwise in
theorem certificate4182 :
    c4180T ∈ titsD ∧
    (c4182S c4182Q ∧ c4182Q * c4182Q = titsZ ∧ c4182Q * c4180T = c4180T * c4182Q ∧
      c4182Q * (c4180C * titsZ * c4180C⁻¹) = c4180C * titsZ * c4180C⁻¹ * c4182Q) ∧
    (∀ x, c4182S x → x * x = 1 → x ≠ 1 →
      Relation.ReflTransGen c4182Step titsZ x ∨ Relation.ReflTransGen c4182Step c4180T x) ∧
    ∀ p : Fin 1755, c4180T p = p → ∃ m ∈ titsA, m 0 = p ∧
      (m * titsZ * m⁻¹ = titsZ ∨ m * titsZ * m⁻¹ = c4180C * titsZ * c4180C⁻¹ ∨
        m * titsZ * m⁻¹ = c4180C⁻¹ * titsZ * c4180C ∨
        (c4182S (m * titsZ * m⁻¹) ∧ ∃ b, c4182S b ∧
          (∃ q, (∃ w : Fin 2925, (0 : Fin 1755) ∈ titsLine w ∧ q ∈ titsLine w) ∧ b q ≠ q) ∧
          Relation.ReflTransGen c4182Pair (m * titsZ * m⁻¹, c4180T) (titsZ, b))) :=
  KernelTitsLoc.facts4182 CFSG.Quasithin.H13.F431.TwoF4.card_twoF4S

end Certificates
