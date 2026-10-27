module

public import CFSG.Monster.B.Co2CatalogData
public import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import Certificates.Data.CFSGNative.MonsterB.Max2Tower
public import Certificates.Data.CFSGNative.MonsterB.BinarySha
public import Certificates.Data.CFSGNative.HS.SmallF2
public import Certificates.Data.CFSGNative.Co2.Data
public meta import CFSG.Monster.B.Co2CatalogData
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Max2Tower
public meta import Certificates.Data.CFSGNative.MonsterB.BinarySha
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.Co2.Data
public import CFSG.Monster.B.Co2CatalogCheckInputs
public import Certificates.Certificate3114

public section

namespace CFSG.Monster.B.Co2Catalog

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Binary.Native

theorem bridge_check :
    bridgeRec.nativeAWord = [15] ∧ bridgeRec.nativeBWord.length = 80 ∧
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
    mulRows 22 (bridgeNativeArr 1) bridgeCRows = mulRows 22 bridgeCRows (bridgeCatalogArr 1) :=
  Certificates.certificate3114

end CFSG.Monster.B.Co2Catalog
