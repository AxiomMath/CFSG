
module

public import Certificates.Certificate16034Base
import all Certificates.Certificate16034Base

public import Certificates.Certificate8955

public section

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.AxisCount CFSG.Monster.Griess
open CFSG.Sporadic.Bridge (wordProd)
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels)

namespace CertificateChecks.Batch16034

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.AxisCount CFSG.Monster.Griess
open CFSG.Sporadic.Bridge (wordProd)
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels)

end CertificateChecks.Batch16034

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.AxisCount CFSG.Monster.Griess in
open CFSG.Sporadic.Bridge (wordProd) in
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels) in
theorem certificate16034 : ∀ i < 10, [(i, true), (i, true)] ∈ rels := by
  exact CertificateChecks.Batch16034.gx_square_mem_rels_0

end Certificates
