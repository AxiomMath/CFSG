module

public import CFSG.Monster.B.Co2CatalogCheck
public import CFSG.Monster.B.Co2.MatrixW
public import CFSG.Sporadic.Co2Cert.FaithfulBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Co2Catalog

open CFSG.Monster CFSG.Monster.VisQuot CFSG.Monster.B.Short CFSG.Monster.B.Co2
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Binary.Native

@[expose] noncomputable def bridgeU1 : OLq := alphaWord bridgeRec.nativeAWord

@[expose] noncomputable def bridgeU2 : OLq := alphaWord bridgeRec.nativeBWord

@[expose] noncomputable def bridgeC : Matrix (Fin 22) (Fin 22) (ZMod 2) := rowsMatrix 22 bridgeCRows

@[expose] noncomputable def bridgeNativeMat (k : ℕ) : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  rowsMatrix 22 (bridgeNativeArr k)

@[expose] noncomputable def bridgeCatalogMat (k : ℕ) : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  rowsMatrix 22 (bridgeCatalogArr k)

theorem bridgeU1_mem :
    bridgeU1 ∈ Kstab v0 := alphaWord_mem _

theorem bridgeU2_mem :
    bridgeU2 ∈ Kstab v0 := alphaWord_mem _

theorem mon_catalog_co2_bridge_data :
    bridgeRec.nativeAWord = [15] ∧ bridgeU1 = alpha ⟨14, by norm_num⟩ ∧
    bridgeRec.nativeBWord.length = 80 ∧ (∀ l ∈ bridgeRec.nativeBWord, l ≠ 0 ∧ l.natAbs ≤ 24) ∧
    bridgeU2 = alphaWord bridgeRec.nativeBWord ∧ bridgeU1 ∈ Kstab v0 ∧ bridgeU2 ∈ Kstab v0 ∧
    bridgeRec.changeOfBasisRows.length = 22 ∧ (∀ x ∈ bridgeRec.changeOfBasisRows, x < 2 ^ 22) ∧
    bridgeC = rowsMatrix 22 bridgeRec.changeOfBasisRows.toArray ∧
    bridgeRec.nativeRows.length = 2 ∧ bridgeRec.catalogTransposeRows.length = 2 ∧
    (∀ k, bridgeNativeMat k = rowsMatrix 22 (bridgeRec.nativeRows.getD k []).toArray) ∧
    (∀ k, bridgeCatalogMat k = rowsMatrix 22 (bridgeRec.catalogTransposeRows.getD k []).toArray) ∧
    CFSG.Sporadic.Co2Cert.co2A1 =
      Blueprint.NativeSporadic.decode 2 22 1 Blueprint.NativeSporadic.Co2Seed1 ∧
    CFSG.Sporadic.Co2Cert.co2A2 =
      Blueprint.NativeSporadic.decode 2 22 1 Blueprint.NativeSporadic.Co2Seed2 := by
  obtain ⟨hA, hB, hBl, hN, hT, hC, hCl, -⟩ := bridge_check
  refine ⟨hA, ?_, hB, hBl, rfl,
    bridgeU1_mem, bridgeU2_mem, hC, hCl, rfl, hN, hT, fun _ => rfl, fun _ => rfl, rfl, rfl⟩
  simp [bridgeU1, hA, alphaWord, alphaN]

end CFSG.Monster.B.Co2Catalog
