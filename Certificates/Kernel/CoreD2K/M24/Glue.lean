
module

public import Certificates.Kernel.CoreD2K.M24.Checks
public import CFSG.Certificates.Kernel.CoreD2K.PairsZ

public section

namespace CertificateChecks.KernelCoreD2K.M24

open CFSG.KS.Raw CFSG.KS.CoreD2K CFSG.KD.CoreD2K CFSG.ComponentClassification.PSL3Four
  CFSG.AGLEmbedding.CoreD2 Certificates.CoreD2Perm

theorem gp0_eq : unpack 24 5 (GP 0) = m24CoreData.aT := by decide +kernel

theorem gp1_eq : unpack 24 5 (GP 1) = m24CoreData.bT := by decide +kernel

theorem tab0 : TabRep (unpack 24 5 (GP 0))
    (List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 16] * List.formPerm [4, 12] *
      List.formPerm [5, 8] * List.formPerm [7, 14] * List.formPerm [9, 18] *
      List.formPerm [10, 17] * List.formPerm [11, 20] * List.formPerm [13, 15] *
      List.formPerm [19, 23] * List.formPerm [21, 22] : Equiv.Perm (Fin 24)) := by
  rw [gp0_eq]
  exact ⟨rfl, by decide⟩

theorem tab1 : TabRep (unpack 24 5 (GP 1))
    (List.formPerm [0, 3, 5] * List.formPerm [1, 20, 13] * List.formPerm [2, 8, 14] *
      List.formPerm [4, 17, 9] * List.formPerm [12, 16, 15] * List.formPerm [18, 23, 22] :
      Equiv.Perm (Fin 24)) := by
  rw [gp1_eq]
  exact ⟨rfl, by decide⟩

theorem coreGenerationZOf_M24_three :
    CoreGenerationZOf ↥CFSG.Blueprint.NativeSporadic.M24 3 :=
  coreGenerationZOf_of_zchecks (V := m24V) k_sz k_gens k_nab k_cen k_pairs k_norm Nat.prime_three
    tab0 tab1

end CertificateChecks.KernelCoreD2K.M24

end
