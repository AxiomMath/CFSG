module

public import CFSG.LieType.Multipliers.L34Data
import Certificates.Kernel.Multipliers.L34Facts

public section

namespace Certificates

open CertificateChecks.KernelL34 in
open CFSG.LieType CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.Fischer CFSG.CosetTable in
theorem certificate10005 :
    (aMat.det = 1 ∧ aInvMat.det = 1 ∧ bMat.det = 1 ∧ bInvMat.det = 1)
    ∧ (∀ i j k l : Fin 3, ∀ c : F4, i ≠ j →
      (if k = l then 1 else if k = i ∧ l = j then c else 0) =
      (if k = l then (1 : F4) else 0) + (if i = k ∧ j = l then c else 0))
    ∧ (rels.all (fun r => (wordMat r).isScalar) = true)
    ∧ (coverWs.all (fun r => decide (wordMat r = Mat3.one)) = true)
    ∧ (wordMat zOne = Mat3.one)
    ∧ (wordMat zTwo = Mat3.one)
    ∧ ((wordMat zThree).isScalar = true)
    ∧ (∀ i j : Fin 3, ∀ c : F4, i ≠ j → wordMat (transWord i j c) = transMat i j c)
    ∧ (∀ d₀ d₁ d₂ : F4, d₀ * d₁ * d₂ = 1 →
      wordMat (diagWord d₀ d₁) = diagMat d₀ d₁ d₂)
    ∧ (Finite (PG 2 rels) ∧ Nat.card (PG 2 rels) ≤ 20160)
    ∧ (Finite (PG (subsetOf 2 [1]).length (restrictWords (subsetOf 2 [1]) coverWs)) ∧
      Nat.card (PG (subsetOf 2 [1]).length (restrictWords (subsetOf 2 [1]) coverWs)) ≤ 5)
    ∧ ((genSub {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk} (subsetOf 2 [1])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk}
        (subsetOf 2 [1])).index ≤ 193536 ∧
      ∀ p ∈ walkWords, p.2 ∣ orderOf (PresentedGroup.mk
        {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk} (FreeGroup.mk p.1))) :=
  ⟨mats.1, mats.2.1, mats.2.2.1, mats.2.2.2.1, mats.2.2.2.2.1, mats.2.2.2.2.2.1,
    mats.2.2.2.2.2.2.1, mats.2.2.2.2.2.2.2.1, mats.2.2.2.2.2.2.2.2, cyclic_card_le,
    restrict_card_le, cover_index_walks⟩

end Certificates
