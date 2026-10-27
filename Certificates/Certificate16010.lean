module

public import CFSG.Monster.B.Fischer.InducedCodeInputs
public import CFSG.Monster.B.Fischer.HexadQuot

public section

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Fischer CFSG.Monster.Code
  CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu

namespace CertificateChecks.Batch16010

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Fischer CFSG.Monster.Code
  CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu

private theorem isEchelon_K_0 : IsEchelon 12 pivK rowK := by
  unfold IsEchelon
  decide +kernel

private theorem rowK_eq_1 : ∀ l < 12, rowK l = xorSel (coefK l).testBit genQ 12 := by
  decide +kernel

private theorem red_genK_2 : ∀ j < 12, red 12 pivK rowK (genQ j) = 0 := by
  decide +kernel

private theorem red_spreadW_3 : ∀ u < 1024, red 12 pivK rowK (spreadW u) = 0 → u = 0 := by
  decide +kernel

private theorem matW_check_4 :
    ∀ g < 2, ∀ u < 1024,
      red 12 pivK rowK (xorSel (spreadW u).testBit (fun t => 2 ^ genAB' g t) 22 ^^^
        spreadW (linW g u)) = 0 := by
  decide +kernel

private theorem linW_lt_5 : ∀ g < 2, ∀ u < 1024, linW g u < 1024 := by
  decide +kernel

private theorem seed_check_6 :
    red 12 pivK rowK 1 ≠ 0 ∧ red 12 pivK rowK 3 ≠ 0 ∧
      (∀ x : Fin 22, red 12 pivK rowK (3 ^^^ 2 ^ (x : ℕ)) ≠ 0) ∧
      red 12 pivK rowK 7 ≠ 0 ∧ (∀ x : Fin 22, red 12 pivK rowK (7 ^^^ 2 ^ (x : ℕ)) ≠ 0) ∧
      ∀ x y : Fin 22, red 12 pivK rowK (7 ^^^ (2 ^ (x : ℕ) ^^^ 2 ^ (y : ℕ))) ≠ 0 := by
  decide +kernel

private theorem cosetWt_seed_hs1_7 : spreadW 1 = 1 := by
  decide +kernel

private theorem cosetWt_seed_hs3_8 : spreadW 3 = 3 := by
  decide +kernel

private theorem cosetWt_seed_hs7_9 : spreadW 7 = 7 := by
  decide +kernel

private theorem cosetWt_seed_popc_10 :
    ∀ x y : Fin 22, popc 22 (2 ^ (x : ℕ) ^^^ 2 ^ (y : ℕ)) = 0 ∨
      popc 22 (2 ^ (x : ℕ) ^^^ 2 ^ (y : ℕ)) = 2 := by
  decide +kernel

end CertificateChecks.Batch16010

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Fischer CFSG.Monster.Code
  CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu in
theorem certificate16010 : (
    IsEchelon 12 pivK rowK
  ) ∧ (
    ∀ l < 12, rowK l = xorSel (coefK l).testBit genQ 12
  ) ∧ (
    ∀ j < 12, red 12 pivK rowK (genQ j) = 0
  ) ∧ (
    ∀ u < 1024, red 12 pivK rowK (spreadW u) = 0 → u = 0
  ) ∧ (
    ∀ g < 2, ∀ u < 1024,
      red 12 pivK rowK (xorSel (spreadW u).testBit (fun t => 2 ^ genAB' g t) 22 ^^^
        spreadW (linW g u)) = 0
  ) ∧ (
    ∀ g < 2, ∀ u < 1024, linW g u < 1024
  ) ∧ (
    red 12 pivK rowK 1 ≠ 0 ∧ red 12 pivK rowK 3 ≠ 0 ∧
      (∀ x : Fin 22, red 12 pivK rowK (3 ^^^ 2 ^ (x : ℕ)) ≠ 0) ∧
      red 12 pivK rowK 7 ≠ 0 ∧ (∀ x : Fin 22, red 12 pivK rowK (7 ^^^ 2 ^ (x : ℕ)) ≠ 0) ∧
      ∀ x y : Fin 22, red 12 pivK rowK (7 ^^^ (2 ^ (x : ℕ) ^^^ 2 ^ (y : ℕ))) ≠ 0
  ) ∧ (
    spreadW 1 = 1
  ) ∧ (
    spreadW 3 = 3
  ) ∧ (
    spreadW 7 = 7
  ) ∧ (
    ∀ x y : Fin 22, popc 22 (2 ^ (x : ℕ) ^^^ 2 ^ (y : ℕ)) = 0 ∨
      popc 22 (2 ^ (x : ℕ) ^^^ 2 ^ (y : ℕ)) = 2
  ) := by
  exact ⟨CertificateChecks.Batch16010.isEchelon_K_0, CertificateChecks.Batch16010.rowK_eq_1, CertificateChecks.Batch16010.red_genK_2,
    CertificateChecks.Batch16010.red_spreadW_3, CertificateChecks.Batch16010.matW_check_4, CertificateChecks.Batch16010.linW_lt_5,
    CertificateChecks.Batch16010.seed_check_6, CertificateChecks.Batch16010.cosetWt_seed_hs1_7, CertificateChecks.Batch16010.cosetWt_seed_hs3_8,
    CertificateChecks.Batch16010.cosetWt_seed_hs7_9, CertificateChecks.Batch16010.cosetWt_seed_popc_10⟩

end Certificates
