module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSARk1
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSAGen
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSAPair

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalInvolution.Phan

theorem ggSecFiveRk1PhanInput_of_N
    (hN : GGSecFiveRk1PhanNInput) (hNS : GGSecFiveNSKGPosAInput) (hL1 : GGSecFiveL1PhanInput) :
    GGSecFiveRk1PhanInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hL ι M e hpres hle3
  by_cases hAb : (∃ (m : ℕ) (σ : Fin m ≃ ι), 5 ≤ m ∧ M = (CoxeterMatrix.A m).reindex σ) ∧
      (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
  · exact ggSecFiveRk1PhanAInput_of_nsKGPos hNS hL1 G p B Bs x L D J 𝒦 hcfg hL ι M e hpres hAb.1 hAb.2
  · exact hN G p B Bs x L D J 𝒦 hcfg hL ι M e hpres hle3 hAb

theorem ggSecFiveGenPhanInput_of_N
    (hN : GGSecFiveGenPhanNInput) (hNS : GGSecFiveNSKGPosAInput) (hL1 : GGSecFiveL1PhanInput) :
    GGSecFiveGenPhanInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hL ι M e hpres hle3 hbig
  by_cases hA : ∃ (m : ℕ) (σ : Fin m ≃ ι), 5 ≤ m ∧ M = (CoxeterMatrix.A m).reindex σ
  · exact ggSecFiveGenPhanAInput_of_nsKGPos hNS hL1 G p B Bs x L D J 𝒦 hcfg hL ι M e hpres hA hbig
  · exact hN G p B Bs x L D J 𝒦 hcfg hL ι M e hpres hle3 (fun h => hA h.1) hbig

theorem ggSecFivePhanPairInput_of_N
    (hN : GGSecFivePhanPairNInput) (hNS : GGSecFiveNSKGPosAInput) :
    GGSecFivePhanPairInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hL ι M e hpres hle3 hbig
  by_cases hA : ∃ (m : ℕ) (σ : Fin m ≃ ι), 5 ≤ m ∧ M = (CoxeterMatrix.A m).reindex σ
  · exact ggSecFivePhanPairAInput_of_nsKGPos hNS G p B Bs x L D J 𝒦 hcfg hL ι M e hpres hA hbig
  · exact hN G p B Bs x L D J 𝒦 hcfg hL ι M e hpres hle3 (fun h => hA h.1) hbig

end CFSG.StandardType

end
