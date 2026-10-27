module

public import CFSG.ThirdParty.BrauerInduction.Background.Group.PRegularClass
import Certificates.Kernel.SporSch.Pair.J2OddMain
public import CFSG.Sporadic.Schreier.PairJ2CertBase

public section

namespace Certificates

open CertificateChecks

theorem certificate260410 :
    (∀ g : ↥CFSG.Sporadic.Schreier.j2P, CFSG.IsPRegular 2 g → orderOf g ∈ [1, 3, 5, 7, 15]) ∧
      Fintype.card (CFSG.PRegularClass 2 ↥CFSG.Sporadic.Schreier.j2P) ≤ 10 :=
  KernelSporSch.PJ2C260410G.j2OddFacts

end Certificates
