module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM22Model
import Certificates.Kernel.Q16M22.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate320302 : ∃ Q : Subgroup (Equiv.Perm (Fin 24)),
    Q ≤ CFSG.ComponentClassification.RankTwoSporadic.M22.iota.range ∧
    Nat.card ↥Q = 2 ^ 8 ∧ CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.NoQ16Q16 ↥Q :=
  ⟨KernelQ16M22.m22S, KernelQ16M22.q16M22_le_range, KernelQ16M22.q16M22_card_noQ16Q16⟩

end Certificates
