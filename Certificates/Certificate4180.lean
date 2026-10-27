
module

public import Certificates.Certificate4180Base

public import Certificates.Data.TwoF4LieCheck
public import CFSG.Sporadic.Schreier.TitsActionCheckInputs
public import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
public import CFSG.Sporadic.Schreier.TitsAction
public import Mathlib.Logic.Relation
import Certificates.Kernel.TwoF4Lie.Glue
import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4SpecBase

public section

open CFSG.Sporadic.Schreier.Tits

open scoped Pointwise

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier.Tits in
open scoped Pointwise in
theorem certificate4180 :
    (c4180T 0 = 0 ∧ c4180T • titsLine 0 = titsLine 0 ∧ c4180T * c4180T = 1 ∧ c4180T ≠ 1 ∧
      (Finset.univ.filter fun p : Fin 1755 => c4180T p = p).card = 27 ∧
      (Finset.univ.filter fun p : Fin 1755 => titsZ p = p).card = 91) ∧
    (c4180C ^ 3 = 1 ∧ c4180C ≠ 1 ∧ c4180C * c4180T = c4180T * c4180C) ∧
    ((∀ p ∈ titsLine 0, c4180T p = p) ∧
      (∀ p ∈ titsLine 0, ∃ w : Fin 2925, (∀ q ∈ titsLine w, c4180T q = q) ∧ w ≠ 0 ∧
        p ∈ titsLine w) ∧
      ∀ v : Fin 2925, (∀ q ∈ titsLine v, c4180T q = q) →
        (∀ p ∈ titsLine v, ∃ w : Fin 2925, (∀ q ∈ titsLine w, c4180T q = q) ∧ w ≠ v ∧
          p ∈ titsLine w) → v = 0) ∧
    ∀ x ∈ titsA, x 0 = 0 → x • titsLine 0 = titsLine 0 → x * x = 1 → x ≠ 1 →
      Relation.ReflTransGen c4180Step titsZ x ∨ Relation.ReflTransGen c4180Step c4180T x :=
  KernelTwoF4Lie.facts CFSG.Quasithin.H13.F431.TwoF4.card_twoF4S

end Certificates
