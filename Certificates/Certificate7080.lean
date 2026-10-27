module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoCertInputs

public section

set_option maxRecDepth 400000

open CFSG CFSG.Quasithin CFSG.Quasithin.L34Amalgam MulAction CFSG.ComponentClassification.WittDesign
open CFSG.Quasithin.Asc94 CFSG.CosetTable

namespace CertificateChecks.Batch7080

open CFSG CFSG.Quasithin CFSG.Quasithin.L34Amalgam MulAction CFSG.ComponentClassification.WittDesign
open CFSG.Quasithin.Asc94 CFSG.CosetTable

theorem crd_presF_0 :
    ∀ x : Fin 16, presF (tab (crd x)) = true := by
  decide +kernel

theorem fix_A1_1 :
    ∀ y : Fin 22, y ≠ 0 → y ≠ 1 → ∃ x : Fin 16, (tab (crd x)).getD y.val 0 ≠ y := by
  decide +kernel

theorem fix_A2_2 :
    ∀ y : Fin 22, y ∉ m22HexadL →
      ∃ s ∈ a2W, (wtab genTL genTiL s).getD y.val 0 ≠ y := by
  decide +kernel

theorem count_A1_A2_3 :
    (Finset.univ.filter fun x : Fin 16 => fixesF (tab (crd x)) = true).card = 4 := by
  decide +kernel

end CertificateChecks.Batch7080

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.L34Amalgam MulAction CFSG.ComponentClassification.WittDesign in
open CFSG.Quasithin.Asc94 CFSG.CosetTable in
theorem certificate7080 :
    (∀ x : Fin 16, presF (tab (crd x)) = true)
    ∧ (∀ y : Fin 22, y ≠ 0 → y ≠ 1 → ∃ x : Fin 16, (tab (crd x)).getD y.val 0 ≠ y)
    ∧ (∀ y : Fin 22, y ∉ m22HexadL →
        ∃ s ∈ a2W, (wtab genTL genTiL s).getD y.val 0 ≠ y)
    ∧ ((Finset.univ.filter fun x : Fin 16 => fixesF (tab (crd x)) = true).card = 4) :=
  ⟨CertificateChecks.Batch7080.crd_presF_0, CertificateChecks.Batch7080.fix_A1_1, CertificateChecks.Batch7080.fix_A2_2, CertificateChecks.Batch7080.count_A1_A2_3⟩

end Certificates
