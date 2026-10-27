module

public import Certificates.Kernel.CoreD2K.Tits.Checks
public import Certificates.Kernel.Sporadic.Tits.Words2264
public import CFSG.Certificates.Kernel.CoreD2K.Pairs
public import CFSG.LocalAnalysis.StandardType.TitsGeneratorsBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCoreD2K.Tits

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.CoreD2K CFSG.KD.CoreD2K
  CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.CoreD2 CFSG.Sporadic.Schreier.Tits
  CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264

theorem gp0_eq : Nat.beq (GP 0) (TitsD.S 0) = true := by decide +kernel

theorem gp1_eq : Nat.beq (GP 1) (TitsD.S 1) = true := by decide +kernel

theorem tab_gp {j : Nat} (hj : j < 2) (hb : Nat.beq (GP j) (TitsD.S j) = true) :
    TabRep (unpack 1755 11 (GP j)) (titsDGen j) := by
  have hd : Nat.beq (Dp j) (TitsD.S j) = true := PK.allN_iff.1 dOK j hj
  rw [Nat.eq_of_beq_eq_true hb, ← Nat.eq_of_beq_eq_true hd, ← titsDArr_eq hj]
  exact CFSG.StandardType.TitsGenerators.tab_titsDGen hj

theorem tab0 : TabRep (unpack 1755 11 (GP 0)) (titsDGen 0) := tab_gp (by norm_num) gp0_eq

theorem tab1 : TabRep (unpack 1755 11 (GP 1)) (titsDGen 1) := tab_gp (by norm_num) gp1_eq

theorem titsD_eq_pair :
    titsD = Subgroup.closure ({titsDGen 0, titsDGen 1} : Set (Equiv.Perm (Fin 1755))) := by
  unfold titsD
  congr 1
  ext x
  simp [Fin.exists_fin_two, eq_comm]

theorem coreGenerationOf_titsD_three : CoreGenerationOf ↥titsD 3 := by
  rw [titsD_eq_pair]
  exact coreGenerationOf_of_pchecks (V := titsV) k_sz k_gens k_pairs k_norm Nat.prime_three tab0
    tab1

end CertificateChecks.KernelCoreD2K.Tits

end
