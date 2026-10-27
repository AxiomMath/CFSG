module

public import CFSG.Timmesfeld.Exceptional.DeepQInputs
import Certificates.Kernel.Misc.Coset.C8054
public import CFSG.Certificates.WordPresentation

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Timmesfeld CFSG.Timmesfeld.Moufang CFSG.Timmesfeld.Moufang.Deep CFSG.Certificates
  CFSG.CosetTable in
theorem certificate8054 : 
    (Finite (PG (subsetOf 3 [0, 1]).length relsAB) ∧
        Nat.card (PG (subsetOf 3 [0, 1]).length relsAB) ≤ 360) ∧
      (Finite (PG 3 (relsQ ++ [wQC3])) ∧ Nat.card (PG 3 (relsQ ++ [wQC3])) ≤ 1) ∧
      (∀ r ∈ relsQ, signedProd psi r = 1) ∧ signedProd psi wQC6 = 1 ∧
      ∀ i j : Fin 360, signedProd psi (w3 i) = signedProd psi (w3 j) → i = j :=
  ⟨KernelMiscCoset.C8054.card_AB, KernelMiscCoset.C8054.card_QC3,
    KernelMiscCoset.C8054.perm_facts⟩

end Certificates
