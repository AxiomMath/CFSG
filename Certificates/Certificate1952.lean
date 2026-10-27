module

public import CFSG.RankThree.PartOne.KE.E8A2NativeModuleCertificate1952Inputs
public import CFSG.RankThree.PartOne.KE.E7A2NativeModule

public section

open CFSG CFSG.RankThree CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley Matrix
open CFSG.RankThree.E6 (chainRoot)

namespace CertificateChecks.Batch1952

open CFSG CFSG.RankThree CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley Matrix
open CFSG.RankThree.E6 (chainRoot)

private theorem length_e8Certificate_roots_0 :  e8Certificate.roots.length = 240 := by
  decide +kernel

private theorem exists_e8RootVec_e8a2Weight_1 :     ∀ k : Fin 3, ∃ m : Fin 240, e8RootVec m = e8a2Weight k := by
  decide +kernel

private theorem e8a2Weight_ne_single_2 :  ∀ k : Fin 3, ∀ i : Fin 8, (i = 0 ∨ i = 2) →
    e8a2Weight k ≠ Pi.single (e8Index i) 1 ∧ e8a2Weight k ≠ -Pi.single (e8Index i) 1 := by
  decide +kernel

private theorem e8a2Weight_add_single_3 :  ∀ k : Fin 3, ∀ i : Fin 8, (i = 0 ∨ i = 2) →
    (∀ m : Fin 240, e8RootVec m ≠ e8a2Weight k + Pi.single (e8Index i) 1) ∨
      ∃ k', e8a2Weight k' = e8a2Weight k + Pi.single (e8Index i) 1 := by
  decide +kernel

private theorem e8a2Weight_sub_single_4 :  ∀ k : Fin 3, ∀ i : Fin 8, (i = 0 ∨ i = 2) →
    (∀ m : Fin 240, e8RootVec m ≠ e8a2Weight k - Pi.single (e8Index i) 1) ∨
      ∃ k', e8a2Weight k' = e8a2Weight k - Pi.single (e8Index i) 1 := by
  decide +kernel

private theorem e8a2Mat_x1_5 : ∀ i j : Fin 3, e8a2Weight j + Pi.single (e8Index 0) 1 = e8a2Weight i ↔ (i = 0 ∧ j = 1) := by
  decide +kernel

private theorem e8a2Mat_y1_6 : ∀ i j : Fin 3, e8a2Weight j - Pi.single (e8Index 0) 1 = e8a2Weight i ↔ (i = 1 ∧ j = 0) := by
  decide +kernel

private theorem e8a2Mat_x3_7 : ∀ i j : Fin 3, e8a2Weight j + Pi.single (e8Index 2) 1 = e8a2Weight i ↔ (i = 1 ∧ j = 2) := by
  decide +kernel

private theorem e8a2Mat_y3_8 : ∀ i j : Fin 3, e8a2Weight j - Pi.single (e8Index 2) 1 = e8a2Weight i ↔ (i = 2 ∧ j = 1) := by
  decide +kernel

private theorem e8a2Weight_pairing_9 :  ∀ k : Fin 3,
    (∑ j, Tag.E8.cartan (e8Index 0) j * e8a2Weight k j) = (![1, -1, 0] : Fin 3 → ℤ) k ∧
    (∑ j, Tag.E8.cartan (e8Index 2) j * e8a2Weight k j) = (![0, 1, -1] : Fin 3 → ℤ) k := by
  decide +kernel

private theorem e8chainRoot13_mem_10 :  ∀ k l : Fin 3, k ≠ l → ∃ m : Fin 240,
    e8RootVec m = chainRoot e8chain13 k l ∧
      ∀ i, ¬(i = e8Index 0 ∨ i = e8Index 2) → e8RootVec m i = 0 := by
  decide +kernel

private theorem exists_e8chainRoot13_of_support13_11 :  ∀ m : Fin 240,
    (∀ i, ¬(i = e8Index 0 ∨ i = e8Index 2) → e8RootVec m i = 0) →
      ∃ k l : Fin 3, k ≠ l ∧ chainRoot e8chain13 k l = e8RootVec m := by
  decide +kernel

private theorem e8chainRoot13_eq_sub_12 :     ∀ i j : Fin 3, chainRoot e8chain13 i j = e8a2Weight i - e8a2Weight j := by
  decide +kernel

private theorem e8chainRoot13_values_13 :     chainRoot e8chain13 0 1 = Pi.single (e8Index 0) 1 ∧
    chainRoot e8chain13 1 2 = Pi.single (e8Index 2) 1 ∧
    chainRoot e8chain13 1 0 = -Pi.single (e8Index 0) 1 ∧
    chainRoot e8chain13 2 1 = -Pi.single (e8Index 2) 1 := by
  decide +kernel

private theorem e8chainRoot13_sums_14 :     (chainRoot e8chain13 0 1 + chainRoot e8chain13 1 2 = chainRoot e8chain13 0 2 ∧
      chainRoot e8chain13 0 1 ≠ chainRoot e8chain13 1 2 ∧
      chainRoot e8chain13 0 1 ≠ -chainRoot e8chain13 1 2) ∧
    (chainRoot e8chain13 2 1 + chainRoot e8chain13 1 0 = chainRoot e8chain13 2 0 ∧
      chainRoot e8chain13 2 1 ≠ chainRoot e8chain13 1 0 ∧
      chainRoot e8chain13 2 1 ≠ -chainRoot e8chain13 1 0) := by
  decide +kernel

end CertificateChecks.Batch1952

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley Matrix in
open CFSG.RankThree.E6 (chainRoot) in
theorem certificate1952 : (
 e8Certificate.roots.length = 240
)
    ∧ (
    ∀ k : Fin 3, ∃ m : Fin 240, e8RootVec m = e8a2Weight k
)
    ∧ (
 ∀ k : Fin 3, ∀ i : Fin 8, (i = 0 ∨ i = 2) →
    e8a2Weight k ≠ Pi.single (e8Index i) 1 ∧ e8a2Weight k ≠ -Pi.single (e8Index i) 1
)
    ∧ (
 ∀ k : Fin 3, ∀ i : Fin 8, (i = 0 ∨ i = 2) →
    (∀ m : Fin 240, e8RootVec m ≠ e8a2Weight k + Pi.single (e8Index i) 1) ∨
      ∃ k', e8a2Weight k' = e8a2Weight k + Pi.single (e8Index i) 1
)
    ∧ (
 ∀ k : Fin 3, ∀ i : Fin 8, (i = 0 ∨ i = 2) →
    (∀ m : Fin 240, e8RootVec m ≠ e8a2Weight k - Pi.single (e8Index i) 1) ∨
      ∃ k', e8a2Weight k' = e8a2Weight k - Pi.single (e8Index i) 1
)
    ∧ (
∀ i j : Fin 3, e8a2Weight j + Pi.single (e8Index 0) 1 = e8a2Weight i ↔ (i = 0 ∧ j = 1)
)
    ∧ (
∀ i j : Fin 3, e8a2Weight j - Pi.single (e8Index 0) 1 = e8a2Weight i ↔ (i = 1 ∧ j = 0)
)
    ∧ (
∀ i j : Fin 3, e8a2Weight j + Pi.single (e8Index 2) 1 = e8a2Weight i ↔ (i = 1 ∧ j = 2)
)
    ∧ (
∀ i j : Fin 3, e8a2Weight j - Pi.single (e8Index 2) 1 = e8a2Weight i ↔ (i = 2 ∧ j = 1)
)
    ∧ (
 ∀ k : Fin 3,
    (∑ j, Tag.E8.cartan (e8Index 0) j * e8a2Weight k j) = (![1, -1, 0] : Fin 3 → ℤ) k ∧
    (∑ j, Tag.E8.cartan (e8Index 2) j * e8a2Weight k j) = (![0, 1, -1] : Fin 3 → ℤ) k
)
    ∧ (
 ∀ k l : Fin 3, k ≠ l → ∃ m : Fin 240,
    e8RootVec m = chainRoot e8chain13 k l ∧
      ∀ i, ¬(i = e8Index 0 ∨ i = e8Index 2) → e8RootVec m i = 0
)
    ∧ (
 ∀ m : Fin 240,
    (∀ i, ¬(i = e8Index 0 ∨ i = e8Index 2) → e8RootVec m i = 0) →
      ∃ k l : Fin 3, k ≠ l ∧ chainRoot e8chain13 k l = e8RootVec m
)
    ∧ (
    ∀ i j : Fin 3, chainRoot e8chain13 i j = e8a2Weight i - e8a2Weight j
)
    ∧ (
    chainRoot e8chain13 0 1 = Pi.single (e8Index 0) 1 ∧
    chainRoot e8chain13 1 2 = Pi.single (e8Index 2) 1 ∧
    chainRoot e8chain13 1 0 = -Pi.single (e8Index 0) 1 ∧
    chainRoot e8chain13 2 1 = -Pi.single (e8Index 2) 1
)
    ∧ (
    (chainRoot e8chain13 0 1 + chainRoot e8chain13 1 2 = chainRoot e8chain13 0 2 ∧
      chainRoot e8chain13 0 1 ≠ chainRoot e8chain13 1 2 ∧
      chainRoot e8chain13 0 1 ≠ -chainRoot e8chain13 1 2) ∧
    (chainRoot e8chain13 2 1 + chainRoot e8chain13 1 0 = chainRoot e8chain13 2 0 ∧
      chainRoot e8chain13 2 1 ≠ chainRoot e8chain13 1 0 ∧
      chainRoot e8chain13 2 1 ≠ -chainRoot e8chain13 1 0)
) := by
  exact ⟨CertificateChecks.Batch1952.length_e8Certificate_roots_0, CertificateChecks.Batch1952.exists_e8RootVec_e8a2Weight_1, CertificateChecks.Batch1952.e8a2Weight_ne_single_2, CertificateChecks.Batch1952.e8a2Weight_add_single_3, CertificateChecks.Batch1952.e8a2Weight_sub_single_4, CertificateChecks.Batch1952.e8a2Mat_x1_5, CertificateChecks.Batch1952.e8a2Mat_y1_6, CertificateChecks.Batch1952.e8a2Mat_x3_7, CertificateChecks.Batch1952.e8a2Mat_y3_8, CertificateChecks.Batch1952.e8a2Weight_pairing_9, CertificateChecks.Batch1952.e8chainRoot13_mem_10, CertificateChecks.Batch1952.exists_e8chainRoot13_of_support13_11, CertificateChecks.Batch1952.e8chainRoot13_eq_sub_12, CertificateChecks.Batch1952.e8chainRoot13_values_13, CertificateChecks.Batch1952.e8chainRoot13_sums_14⟩

end Certificates
