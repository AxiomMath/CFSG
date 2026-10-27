
module


public import Certificates.Data.CFSGNative.MonsterB.Short
import Certificates.Kernel.MonsterB.Short3014Orbit

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Short in
theorem certificate3014 : Native.shortCertOK = true := by
  obtain ⟨S, h1, h2, h3⟩ := Short3014.orbit
  exact CFSG.KC.KSearch.shortCertOK_of_orbit S h1 h2 h3

end Certificates
