
module

public import Certificates.Certificate16009Base
import all Certificates.Certificate16009Base

public import Certificates.Certificate8955

public section

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.AxisCount CFSG.Monster.Griess
  CFSG.Monster.Generated CFSG.Monster.B CFSG.Monster.B.Short
open CFSG.Sporadic.Bridge (wordProd)
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels)

namespace CertificateChecks.Batch16009

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.AxisCount CFSG.Monster.Griess
  CFSG.Monster.Generated CFSG.Monster.B CFSG.Monster.B.Short
open CFSG.Sporadic.Bridge (wordProd)
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels)

end CertificateChecks.Batch16009

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.AxisCount CFSG.Monster.Griess
  CFSG.Monster.Generated CFSG.Monster.B CFSG.Monster.B.Short in
open CFSG.Sporadic.Bridge (wordProd) in
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels) in
theorem certificate16009 : (
    ∀ v ∈ rels, ∀ l ∈ v, l.1 < 10
  ) ∧ (
    ∀ v ∈ rels, ∀ l ∈ v, l.2 = true
  ) := by
  exact ⟨CertificateChecks.Batch16009.fiRels_lt_0, CertificateChecks.Batch16009.fiRels_pos_1⟩

end Certificates
