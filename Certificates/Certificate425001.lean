module

import Certificates.Kernel.MonsterPcFive.W425001
public import CFSG.Adapters.ProjectiveSpecialLinear
public import Certificates.Certificate13680

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveCensus (prodAsc) in
open Timmesfeld.PcFive (pw cw repIdx) in
open Timmesfeld.PcReg (digitsOf) in
theorem certificate425001 : ∀ {G : Type} [Group G] [Finite G] (g : Fin 9 → G),
    (∀ i : Fin 9, g i ^ 5 = prodAsc g pw[i.val]!) →
    (∀ i j : Fin 9, i < j → g i * g j * (g i)⁻¹ = prodAsc g cw[i.val * 9 + j.val]!) →
    g 8 ≠ 1 → ∀ k < repIdx.size, ∃ E : Subgroup G, CFSG.Open.IsElemAbelian 5 E ∧
      Nat.card E = 5 ^ 3 ∧ prodAsc g (digitsOf 5 9 repIdx[k]!) ∈ E :=
  fun g hpow hcomm hz => KernelMonPcFive.fiveE3Witness g hpow hcomm hz

end Certificates
