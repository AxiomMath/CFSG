
module

public import Certificates.Kernel.CoreD2K.M12.Checks
public import CFSG.Certificates.Kernel.CoreD2K.Pairs

public section

namespace CertificateChecks.KernelCoreD2K.M12

open CFSG.KS.Raw CFSG.KS.CoreD2K CFSG.KD.CoreD2K CFSG.ComponentClassification.PSL3Four
  CFSG.AGLEmbedding.CoreD2 Certificates.CoreD2Perm

theorem gp0_eq : unpack 12 4 (GP 0) = m12CoreData.aT := by decide +kernel

theorem gp1_eq : unpack 12 4 (GP 1) = m12CoreData.bT := by decide +kernel

theorem tab0 : TabRep (unpack 12 4 (GP 0))
    (List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] *
      List.formPerm [5, 11] : Equiv.Perm (Fin 12)) := by
  rw [gp0_eq]
  exact ⟨rfl, by decide⟩

theorem tab1 : TabRep (unpack 12 4 (GP 1))
    (List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
      List.formPerm [5, 9, 6] : Equiv.Perm (Fin 12)) := by
  rw [gp1_eq]
  exact ⟨rfl, by decide⟩

theorem coreGenerationOf_M12_three :
    CoreGenerationOf ↥CFSG.Blueprint.NativeSporadic.M12 3 :=
  coreGenerationOf_of_pchecks (V := m12V) k_sz k_gens k_pairs k_norm Nat.prime_three tab0 tab1

end CertificateChecks.KernelCoreD2K.M12

end
