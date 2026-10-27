module

public import CFSG.Certificates.Kernel.MonsterPcFive.ProdAsc
public import Certificates.Data.CFSGNative.Timmesfeld.PcFive
import Certificates.Kernel.MonsterPcFive.W13680
import Certificates.Kernel.MonsterPcFive.Tab
import CFSG.Certificates.Kernel.MonsterPcFive.Center

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.MonPcFive CFSG.KC.MonPcFiveD

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveCensus (prodAsc) in
open Timmesfeld.PcFive (pw cw auts repIdx) in
open Timmesfeld.PcReg (digitsOf) in
theorem certificate13680 : ∀ {G : Type} [Group G] [Finite G] (g : Fin 9 → G),
    (∀ i : Fin 9, g i ^ 5 = prodAsc g pw[i.val]!) →
    (∀ i j : Fin 9, i < j → g i * g j * (g i)⁻¹ = prodAsc g cw[i.val * 9 + j.val]!) →
    g 8 ≠ 1 →
    (Nat.card (Subgroup.closure (Set.range g)) = 5 ^ 9 ∧
      ∀ c ∈ Subgroup.closure (Set.range g),
        (∀ y ∈ Subgroup.closure (Set.range g), c * y = y * c) → c ∈ Subgroup.zpowers (g 8)) ∧
    ∀ {m : ℕ}, Nat.card G = 5 ^ 9 * m → ¬ 5 ∣ m →
    (∀ j < auts.size, ∃ c : G, ∀ (i : ℕ) (hi : i < 9),
      c * g ⟨i, hi⟩ * c⁻¹ = prodAsc g (digitsOf 5 9 (auts[j]!)[i]!)) →
    ∀ s : G, orderOf s = 5 → ∃ k < repIdx.size, prodAsc g (digitsOf 5 9 repIdx[k]!) ^ 5 = 1 ∧
      ∃ e : ℕ, 0 < e ∧ e < 5 ∧ ∃ c : G, c * s * c⁻¹ = prodAsc g (digitsOf 5 9 repIdx[k]!) ^ e := by
  refine fun g hpow hcomm hz => ⟨?_, fun hcard hm hN =>
    KernelMonPcFive.fiveCensusConj hcard hm g hpow hcomm hz hN⟩
  have H := pcHyp_of_rel hpow hcomm
  have C : TabChecks := ⟨tabT, tauT⟩
  rw [closure_range_eq H]
  exact ⟨card_P H C sigT hz, fun c hc hcen => H.mem_zpowers_of_central C sigT hz hc hcen⟩

end Certificates
