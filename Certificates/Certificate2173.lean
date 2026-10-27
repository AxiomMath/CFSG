
module

public import Certificates.Certificate2173Base
import all Certificates.Certificate2173Base

public import CFSG.Sporadic.Schreier.J4SFiveBase
public import CFSG.Sporadic.Schreier.J4SPointwise
public meta import CFSG.Sporadic.J4.PrimSpec
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase

public section

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native
open CFSG.LocalAnalysis.ComponentInitial MulAction

namespace CertificateChecks.Batch2173

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native
open CFSG.LocalAnalysis.ComponentInitial MulAction

end CertificateChecks.Batch2173

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native in
open CFSG.LocalAnalysis.ComponentInitial MulAction in
theorem certificate2173 : ∀ c ∈ ({2, 5, 6} : Finset (Fin 7)), ∀ T : Finset (Fin 7),
    (c ∈ T → (∑ i ∈ T, subSizesF i) ∣ 501397585920 → T = {c}) ∧
      ((∑ i ∈ T, subSizesF i) = subSizesF c → T = {c}) := by
  exact CertificateChecks.Batch2173.classes_check_0

end Certificates
