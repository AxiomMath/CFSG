
module

public import Certificates.Certificate2152Base

public import CFSG.Sporadic.Schreier.Co3Arrays
import Certificates.Kernel.SporSch.Co3.Cert2152

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.Monster.B.Co2.Native in
open CFSG.Sporadic.Schreier.Co3.Native in
theorem certificate2152 : (layoutOK co3Bytes276 3 276 111 = true ∧ layoutOK co3Bytes36 2 36 83 = true ∧
      layoutOK co3Bytes12 1 12 14 = true ∧ layoutOK co3FormsBytes 1 64 276 = true ∧
      (∀ L < 111, isInvA 276 (co3Arr276 L) (invCand 276 (co3Arr276 L)) = true) ∧
      (∀ L < 83, isInvA 36 (co3Arr36 L) (invCand 36 (co3Arr36 L)) = true) ∧
      (∀ L < 14, isInvA 12 (co3Arr12 L) (invCand 12 (co3Arr12 L)) = true) ∧
      (∀ r < 276, co3FormWord r < 2 ^ 253)
    )
    ∧ (CFSG.Sporadic.Schreier.Co3.Native.wordsOK 2 14 co3ChainDerivations = true ∧ CFSG.Sporadic.Schreier.Co3.Native.wordsOK 2 14 co3CoprimeDerivations = true ∧
      CFSG.Sporadic.Schreier.Co3.Native.wordsOK 8 10 co3TDerivations = true ∧ CFSG.Sporadic.Schreier.Co3.Native.wordsOK 7 14 co3MDerivations = true ∧
      CFSG.Sporadic.Schreier.Co3.Native.wordsOK 6 11 co3M1Derivations = true ∧ CFSG.Sporadic.Schreier.Co3.Native.wordsOK 4 8 co3MCommDerivations = true ∧
      CFSG.Sporadic.Schreier.Co3.Native.wordsOK 3 8 co3M1CommDerivations = true ∧ CFSG.Sporadic.Schreier.Co3.Native.wordsOK 13 25 co3JointDerivations = true ∧
      CFSG.Sporadic.Schreier.Co3.Native.wordsOK 63 66 co3Sp36Derivations = true ∧ CFSG.Sporadic.Schreier.Co3.Native.wordsOK 6 16 co3M36Derivations = true ∧
      CFSG.Sporadic.Schreier.Co3.Native.wordsOK 5 13 co3M112Derivations = true
    ) :=
  ⟨KernelSporSch.Co3Cert.layout, KernelSporSch.Co3Cert.words⟩

end Certificates
