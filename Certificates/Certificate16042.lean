module

public import CFSG.Monster.B.Classical.HyperovalInputs
public import CFSG.Monster.B.Classical.PlaneIncidence

public section

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Classical CFSG.Monster.B.Classical.Plane
  CFSG.Fischer
open scoped LinearAlgebra.Projectivization

namespace CertificateChecks.Batch16042

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Classical CFSG.Monster.B.Classical.Plane
  CFSG.Fischer
open scoped LinearAlgebra.Projectivization

private theorem mask_ofMask_orbMasks_0 :
    ∀ i : Fin 3, ∀ m ∈ orbMasks i, mask (ofMask m : Finset (Fin 21)) = m := by
  decide +kernel

private theorem orbMasks_nodup_1 : ∀ i : Fin 3, (orbMasks i).Nodup := by
  decide +kernel

private theorem card_O_2 : ∀ i : Fin 3, (orbMasks i).length = 56 := by
  decide +kernel

private theorem orbMasks_disjoint_3 : ∀ i j : Fin 3, i ≠ j → ∀ m ∈ orbMasks i, m ∉ orbMasks j := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem listed_isHyperoval_0_0_4 :
    ∀ m ∈ (orbMasks 0).take 14,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem listed_isHyperoval_0_1_5 :
    ∀ m ∈ ((orbMasks 0).drop 14).take 14,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem listed_isHyperoval_0_2_6 :
    ∀ m ∈ ((orbMasks 0).drop 28).take 14,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem listed_isHyperoval_0_3_7 :
    ∀ m ∈ (orbMasks 0).drop 42,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem listed_isHyperoval_1_0_8 :
    ∀ m ∈ (orbMasks 1).take 14,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem listed_isHyperoval_1_1_9 :
    ∀ m ∈ ((orbMasks 1).drop 14).take 14,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem listed_isHyperoval_1_2_10 :
    ∀ m ∈ ((orbMasks 1).drop 28).take 14,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem listed_isHyperoval_1_3_11 :
    ∀ m ∈ (orbMasks 1).drop 42,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem listed_isHyperoval_2_0_12 :
    ∀ m ∈ (orbMasks 2).take 14,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem listed_isHyperoval_2_1_13 :
    ∀ m ∈ ((orbMasks 2).drop 14).take 14,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem listed_isHyperoval_2_2_14 :
    ∀ m ∈ ((orbMasks 2).drop 28).take 14,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem listed_isHyperoval_2_3_15 :
    ∀ m ∈ (orbMasks 2).drop 42,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem search_16 :
    ∀ x₀ x₁ : Fin 21, x₀ < x₁ → ∀ x₂ : Fin 21, x₁ < x₂ → colB x₀ x₁ x₂ = false →
      ∀ x₃ : Fin 21, x₂ < x₃ →
        (colB x₀ x₁ x₃ = false ∧ colB x₀ x₂ x₃ = false ∧ colB x₁ x₂ x₃ = false) →
      ∀ x₄ : Fin 21, x₃ < x₄ →
        (colB x₀ x₁ x₄ = false ∧ colB x₀ x₂ x₄ = false ∧ colB x₀ x₃ x₄ = false ∧
          colB x₁ x₂ x₄ = false ∧ colB x₁ x₃ x₄ = false ∧ colB x₂ x₃ x₄ = false) →
      ∀ x₅ : Fin 21, x₄ < x₅ →
        (colB x₀ x₁ x₅ = false ∧ colB x₀ x₂ x₅ = false ∧ colB x₀ x₃ x₅ = false ∧
          colB x₀ x₄ x₅ = false ∧ colB x₁ x₂ x₅ = false ∧ colB x₁ x₃ x₅ = false ∧
          colB x₁ x₄ x₅ = false ∧ colB x₂ x₃ x₅ = false ∧ colB x₂ x₄ x₅ = false ∧
          colB x₃ x₄ x₅ = false) →
      2 ^ (x₀ : ℕ) + 2 ^ (x₁ : ℕ) + 2 ^ (x₂ : ℕ) + 2 ^ (x₃ : ℕ) + 2 ^ (x₄ : ℕ) + 2 ^ (x₅ : ℕ) ∈
        allMasks := by
  decide +kernel

end CertificateChecks.Batch16042

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Classical CFSG.Monster.B.Classical.Plane
  CFSG.Fischer in
open scoped LinearAlgebra.Projectivization in
theorem certificate16042 : (
    ∀ i : Fin 3, ∀ m ∈ orbMasks i, mask (ofMask m : Finset (Fin 21)) = m
  ) ∧ (
    ∀ i : Fin 3, (orbMasks i).Nodup
  ) ∧ (
    ∀ i : Fin 3, (orbMasks i).length = 56
  ) ∧ (
    ∀ i j : Fin 3, i ≠ j → ∀ m ∈ orbMasks i, m ∉ orbMasks j
  ) ∧ (
    ∀ m ∈ (orbMasks 0).take 14,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false
  ) ∧ (
    ∀ m ∈ ((orbMasks 0).drop 14).take 14,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false
  ) ∧ (
    ∀ m ∈ ((orbMasks 0).drop 28).take 14,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false
  ) ∧ (
    ∀ m ∈ (orbMasks 0).drop 42,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false
  ) ∧ (
    ∀ m ∈ (orbMasks 1).take 14,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false
  ) ∧ (
    ∀ m ∈ ((orbMasks 1).drop 14).take 14,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false
  ) ∧ (
    ∀ m ∈ ((orbMasks 1).drop 28).take 14,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false
  ) ∧ (
    ∀ m ∈ (orbMasks 1).drop 42,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false
  ) ∧ (
    ∀ m ∈ (orbMasks 2).take 14,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false
  ) ∧ (
    ∀ m ∈ ((orbMasks 2).drop 14).take 14,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false
  ) ∧ (
    ∀ m ∈ ((orbMasks 2).drop 28).take 14,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false
  ) ∧ (
    ∀ m ∈ (orbMasks 2).drop 42,
      (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21,
        m.testBit x = true → m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z →
          colB x y z = false
  ) ∧ (
    ∀ x₀ x₁ : Fin 21, x₀ < x₁ → ∀ x₂ : Fin 21, x₁ < x₂ → colB x₀ x₁ x₂ = false →
      ∀ x₃ : Fin 21, x₂ < x₃ →
        (colB x₀ x₁ x₃ = false ∧ colB x₀ x₂ x₃ = false ∧ colB x₁ x₂ x₃ = false) →
      ∀ x₄ : Fin 21, x₃ < x₄ →
        (colB x₀ x₁ x₄ = false ∧ colB x₀ x₂ x₄ = false ∧ colB x₀ x₃ x₄ = false ∧
          colB x₁ x₂ x₄ = false ∧ colB x₁ x₃ x₄ = false ∧ colB x₂ x₃ x₄ = false) →
      ∀ x₅ : Fin 21, x₄ < x₅ →
        (colB x₀ x₁ x₅ = false ∧ colB x₀ x₂ x₅ = false ∧ colB x₀ x₃ x₅ = false ∧
          colB x₀ x₄ x₅ = false ∧ colB x₁ x₂ x₅ = false ∧ colB x₁ x₃ x₅ = false ∧
          colB x₁ x₄ x₅ = false ∧ colB x₂ x₃ x₅ = false ∧ colB x₂ x₄ x₅ = false ∧
          colB x₃ x₄ x₅ = false) →
      2 ^ (x₀ : ℕ) + 2 ^ (x₁ : ℕ) + 2 ^ (x₂ : ℕ) + 2 ^ (x₃ : ℕ) + 2 ^ (x₄ : ℕ) + 2 ^ (x₅ : ℕ) ∈
        allMasks
  ) := by
  exact ⟨CertificateChecks.Batch16042.mask_ofMask_orbMasks_0, CertificateChecks.Batch16042.orbMasks_nodup_1, CertificateChecks.Batch16042.card_O_2,
    CertificateChecks.Batch16042.orbMasks_disjoint_3, CertificateChecks.Batch16042.listed_isHyperoval_0_0_4,
    CertificateChecks.Batch16042.listed_isHyperoval_0_1_5, CertificateChecks.Batch16042.listed_isHyperoval_0_2_6,
    CertificateChecks.Batch16042.listed_isHyperoval_0_3_7, CertificateChecks.Batch16042.listed_isHyperoval_1_0_8,
    CertificateChecks.Batch16042.listed_isHyperoval_1_1_9, CertificateChecks.Batch16042.listed_isHyperoval_1_2_10,
    CertificateChecks.Batch16042.listed_isHyperoval_1_3_11, CertificateChecks.Batch16042.listed_isHyperoval_2_0_12,
    CertificateChecks.Batch16042.listed_isHyperoval_2_1_13, CertificateChecks.Batch16042.listed_isHyperoval_2_2_14,
    CertificateChecks.Batch16042.listed_isHyperoval_2_3_15, CertificateChecks.Batch16042.search_16⟩

end Certificates
