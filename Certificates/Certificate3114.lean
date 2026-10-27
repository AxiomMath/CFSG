module

public import Certificates.Kernel.MonsterB.Bridge3114

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Binary.Native CFSG.Monster.B.Co2Catalog CFSG.Sporadic.SmallF2.Native in
theorem certificate3114 : bridgeRec.nativeAWord = [15] ∧ bridgeRec.nativeBWord.length = 80 ∧
    (∀ l ∈ bridgeRec.nativeBWord, l ≠ 0 ∧ l.natAbs ≤ 24) ∧
    bridgeRec.nativeRows.length = 2 ∧ bridgeRec.catalogTransposeRows.length = 2 ∧
    bridgeRec.changeOfBasisRows.length = 22 ∧ (∀ x ∈ bridgeRec.changeOfBasisRows, x < 2 ^ 22) ∧
    (∀ i < 24, (quotRows i).size = 22 ∧
      mulRows 22 (quotRows i) (CFSG.Monster.B.Max2.Native.inv22 (quotRows i)) = idRows 22) ∧
    bridgeWordRows bridgeRec.nativeAWord = bridgeNativeArr 0 ∧
    bridgeWordRows bridgeRec.nativeBWord = bridgeNativeArr 1 ∧
    transposeRows 22 (catalogRows 0) = bridgeCatalogArr 0 ∧
    transposeRows 22 (catalogRows 1) = bridgeCatalogArr 1 ∧
    mulRows 22 bridgeCRows (CFSG.Monster.B.Max2.Native.inv22 bridgeCRows) = idRows 22 ∧
    mulRows 22 (bridgeNativeArr 0) bridgeCRows = mulRows 22 bridgeCRows (bridgeCatalogArr 0) ∧
    mulRows 22 (bridgeNativeArr 1) bridgeCRows = mulRows 22 bridgeCRows (bridgeCatalogArr 1) := Bridge3114.facts

end Certificates
