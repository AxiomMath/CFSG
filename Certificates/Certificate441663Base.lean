module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.IotaDef
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.WordSub
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elems

@[expose] public section

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel Subgroup

namespace Certificates

structure AFacts : Prop where
  u_sq : ∀ i < 6, uElem i * uElem i = 1
  u_comm : ∀ i < 6, ∀ j < 6, uElem i * uElem j = uElem j * uElem i
  iota_ne_one : ∀ k < 64, k ≠ 0 → iotaFun (vecOfCode k) ≠ 1
  iota_z₁ : iotaFun (vecOfCode 45) = pZ₁
  halves : ∀ k < 64,
    ((iotaFun (vecOfCode k) : ↥P1408) : Equiv.Perm (Fin 1408)) ∈ blocks1408 ↔ lamC k = 0
  cent : Nat.card ↥P1408 = 177408000 → ∀ x : ↥P1408,
    (∀ i < 6, x * uElem i = uElem i * x) → ∃ k < 64, iotaFun (vecOfCode k) = x
  norm : ∀ w ∈ normGens, ∀ i < 6, ∃ k < 64,
    elemW w * ((uElem i : ↥P1408) : Equiv.Perm (Fin 1408)) * (elemW w)⁻¹ =
      ((iotaFun (vecOfCode k) : ↥P1408) : Equiv.Perm (Fin 1408))
  fuse : ∀ kv < 64, ∀ kw < 64, kv ≠ 0 → kv ≠ 16 → kw ≠ 0 → kw ≠ 16 → typeIdx kv = typeIdx kw →
    ∃ n ∈ wordSubgroup normGens,
      n * ((iotaFun (vecOfCode kv) : ↥P1408) : Equiv.Perm (Fin 1408)) * n⁻¹ =
        ((iotaFun (vecOfCode kw) : ↥P1408) : Equiv.Perm (Fin 1408))
  conj_z₁ : Nat.card ↥P1408 = 177408000 → ∀ k < 64, ∀ g ∈ P1408,
    g * ((iotaFun (vecOfCode k) : ↥P1408) : Equiv.Perm (Fin 1408)) * g⁻¹ = elemZ₁ →
      typeIdx k = 2

end Certificates

