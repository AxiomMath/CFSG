module

public import CFSG.RankThree.PartOne.KE.CTConclusion
public import CFSG.RankThree.PartOne.KE.NativeCyclicTwisted
public import CFSG.RankThree.PartOne.KE.CTTwistedEight
public import CFSG.RankThree.PartOne.KE.CTTwistedEighteen
public import CFSG.RankThree.PartOne.KE.CTTwistedTwelve

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.Blueprint.Chevalley

theorem oddEndpoint_twistedE6_phi8 :
    OddEndpoint .twistedE6 fun p ℓ f => (p : ℤ) ∣ cycloVal 8 ℓ f :=
  oddEndpoint_twistedE6_of_cyclic fun K _ _ σ p ℓ f hp hp3 hℓ _ hf hK hσ hc => by
    obtain ⟨-, -, _k, h⟩ := twisted_E6_eight_cyclic_sylow hℓ hf K hK σ hσ hp hp3 hc
    exact ⟨CyclicSylowConclusion'.pgroups_cyclic h, CyclicSylowConclusion'.centralizer_cyclic h⟩

theorem oddEndpoint_twistedE6_phi12 :
    OddEndpoint .twistedE6 fun p ℓ f => (p : ℤ) ∣ cycloVal 12 ℓ f :=
  oddEndpoint_twistedE6_of_cyclic fun K _ _ σ p ℓ f hp hp3 hℓ _ hf hK hσ hc => by
    obtain ⟨-, -, _k, h⟩ := twisted_E6_twelve_cyclic_sylow hℓ hf K hK σ hσ hp hp3 hc
    exact ⟨CyclicSylowConclusion'.pgroups_cyclic h, CyclicSylowConclusion'.centralizer_cyclic h⟩

theorem oddEndpoint_twistedE6_phi18 :
    OddEndpoint .twistedE6 fun p ℓ f => (p : ℤ) ∣ cycloVal 18 ℓ f :=
  oddEndpoint_twistedE6_of_cyclic fun K _ _ σ p ℓ f hp hp3 hℓ _ hf hK hσ hc => by
    obtain ⟨-, -, _k, h⟩ := twisted_E6_eighteen_cyclic_sylow hℓ hf K hK σ hσ hp hp3 hc
    exact ⟨CyclicSylowConclusion'.pgroups_cyclic h, CyclicSylowConclusion'.centralizer_cyclic h⟩

end CFSG.RankThree.PartOne.KE
