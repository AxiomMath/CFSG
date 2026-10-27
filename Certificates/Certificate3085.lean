
module


public import CFSG.Sporadic.Ly.WordFacts
public import CFSG.Sporadic.Ly.FiveFacts
public import Certificates.Certificate2184
public import Certificates.Certificate2185
public import Certificates.Certificate2187
public import Certificates.Certificate2189
public import Certificates.Certificate2190
public import Certificates.Certificate9120
import Certificates.Kernel.Ly3085.Facts3085
import Certificates.Kernel.Ly3085.SeedFacts
import Certificates.Kernel.Ly3085.FiveFacts

public section

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Omega CFSG.Sporadic.LySchreier.Native TauCeti

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Omega CFSG.Sporadic.LySchreier.Native TauCeti in
theorem certificate3085 : (∃ _ : LySeed, LyFacts ∧ LyWordFacts ∧ LyFiveFacts) ∧ coverCertificate () = true ∧
    bpRootChecks () = true ∧
    r3eCertificate () = true ∧ sevenCertificate () = true ∧ sylowCertificate () = true ∧
    (Finite TauCeti.SporadicName.Ly.Group ∧
      Nat.card TauCeti.SporadicName.Ly.Group ≤ 51765179004000000) ∧
    ∃ φ : Sporadic.Lyons.presentation.Group →* GL (Fin 111) (ZMod 5),
      ∀ g : GL (Fin 111) (ZMod 5), g.val = CFSG.Sporadic.Ly.mA ∨ g.val = CFSG.Sporadic.Ly.mB → g ∈ φ.range := by
  have : CFSG.Sporadic.Ly.LySeed := KernelLy.Omega.seedFacts
  exact ⟨⟨this, KernelLy.Omega.lyFacts, KernelLy.Omega.wordFacts, KernelLy.Omega.fiveFacts⟩,
    certificate2184, certificate2185,
    certificate2187, certificate2189, certificate2190, certificate9120,
    certificate9213⟩

end Certificates

namespace Certificates

open CertificateChecks

instance certificate3085.lySeed : LySeed := Certificates.certificate3085.1.fst

theorem certificate3085.bridge_hom :
    ∃ φ : Sporadic.Lyons.presentation.Group →* GL (Fin 111) (ZMod 5),
      ∀ g : GL (Fin 111) (ZMod 5), g.val = mA ∨ g.val = mB → g ∈ φ.range :=
  Certificates.certificate3085.2.2.2.2.2.2.2

end Certificates
