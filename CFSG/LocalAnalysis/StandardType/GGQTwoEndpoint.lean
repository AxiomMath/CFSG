module

public import CFSG.LocalAnalysis.StandardType.GGQTwoJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanADefs

public section

namespace CFSG.StandardType

open CFSG.StandardType.QTwo CFSG.ClassicalInvolution.Phan

section Endpoint

theorem ggSecFiveDataResPhanAQTwoInput_of_inputs
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    (hBS : BSCompletion) (hRMGen : QTwoRMGenProducer) (hBlock : QTwoBlockProducer K) :
    GGSecFiveDataResPhanAQTwoInput := by
  intro G instG finG p B Bs x L D J 𝒦 hcfg hTier1 hSplit ι M e hpres hA horder
  obtain ⟨n, e', hn, hM⟩ := hA
  have hGuard : QTwoJoinGuard p B Bs x L D J 𝒦 :=
    ⟨hcfg, hTier1, hSplit, ι, M, e, hpres, ⟨n, e', hn, hM⟩, horder⟩
  have hjoin : ggG0 p B x L D J = L ⊔ ⨆ k ∈ 𝒦, k :=
    ggG0_eq_join_of_qTwoProducer (qTwoJoinProducer_of_rmGen hRMGen) hGuard hcfg.2.2.2.1
  obtain ⟨U, W, hSys⟩ :=
    hBlock hK G p B Bs x L D J 𝒦 hcfg hTier1 hSplit ι M e hpres n e' hn hM horder
  exact ggSecFiveData_of_qTwoWeakPhanSystem (K := K) (n := n) hn
    (L ⊔ ⨆ k ∈ 𝒦, k) U W hSys hjoin.symm hBS

end Endpoint

end CFSG.StandardType

end
