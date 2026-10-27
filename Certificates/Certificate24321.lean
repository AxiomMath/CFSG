module

public import CFSG.Sporadic.Recognition.HNMultiplierExact
import Certificates.Kernel.HNDce2.Assembly
import Certificates.Kernel.HNDce2.ChainGlue
public import CFSG.Sporadic.Recognition.HNMultiplierTables

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Recognition.HNMultiplier in
theorem certificate24321 : (∃ g : Fin 7 → HNJ, HNGens g) ∧ Finite PC ∧ Nat.card PC ≤ 273030912000000 := by
  obtain ⟨hf, hQ⟩ := CFSG.KD.HNDce2.card_hnPR_le_tf
  exact ⟨⟨_, KernelHNMult.hnGens_gf⟩,
    CFSG.KD.HNDce2.card_PC_le_of_card hQ KernelHNMult.hnPsi_injective_gf_tf⟩

end Certificates
