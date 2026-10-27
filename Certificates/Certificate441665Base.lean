module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.IotaDef
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.WordSub
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.FData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableIData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.EichlerDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elems

@[expose] public section

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel
  CFSG.EvenSporadicStandard.HNRecog.HaradaLA Subgroup

namespace Certificates

structure R0Facts : Prop where
  r0_card : Nat.card ↥(wordSubgroupP nWords1) = 2 ^ 8
  r0_le_centralizer : wordSubgroupP nWords1 ≤ centralizer ({pZ} : Set ↥P1408)
  r0_normal : ∀ c ∈ centralizer ({pZ} : Set ↥P1408), ∀ x ∈ wordSubgroupP nWords1,
    c * x * c⁻¹ ∈ wordSubgroupP nWords1
  r0_sq : ∀ x ∈ wordSubgroupP nWords1, x ^ 2 ∈ zpowers pZ
  r0_inter : ∀ v : V6, iotaFun v ∈ wordSubgroupP nWords1 ↔ bil v (Pi.single 0 1) = 0
  r0_eichler : ∀ r ∈ wordSubgroupP nWords1, ∃ u : V6, bil u (Pi.single 0 1) = 0 ∧
    lam u = 0 ∧ ∀ x : V6, r * iotaFun x * r⁻¹ = iotaFun (eichF (Pi.single 0 1) u x)
  r0_surj : ∀ u : V6, bil u (Pi.single 0 1) = 0 → lam u = 0 →
    ∃ r ∈ wordSubgroupP nWords1, ∀ x : V6, r * iotaFun x * r⁻¹ = iotaFun (eichF (Pi.single 0 1) u x)
  r0_faith : ∀ c ∈ centralizer ({pZ} : Set ↥P1408),
    (∀ x ∈ wordSubgroupP nWords1, c * x * c⁻¹ * x⁻¹ ∈ zpowers pZ) → c ∈ wordSubgroupP nWords1
  f_le_centralizer : wordSubgroupP fWords ≤ centralizer ({pZ₁} : Set ↥P1408)
  f_iso : Nonempty (↥(wordSubgroupP fWords) ≃* alternatingGroup (Fin 5))

end Certificates

