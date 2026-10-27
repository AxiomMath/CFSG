module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalGlue

import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalVertexTwo
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalVertexOne

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

theorem G2qLocalData.isAmalgamOfGroup_g2_of_indec (hf : 3 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) (hIndec : ⁅pCoreOf 2 L2, L2⁆ = pCoreOf 2 L2) :
    IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsG2Over f) := by
  obtain ⟨K, _, _, _, hK, ψ₂, hψ₂S, hψ₂Q⟩ := hD.exists_mulEquiv_vertexTwo hf hH h1 h2 hIndec
  obtain ⟨ψ₁, hψ₁Q, hψ₁S⟩ := hD.exists_mulEquiv_vertexOne hf hH h1 h2 hK ψ₂ hψ₂Q hψ₂S
  exact isAmalgamOfGroup_g2_of_mulEquiv hf hH hD h1 h2 hK ψ₁ hψ₁Q hψ₁S ψ₂ hψ₂Q hψ₂S

end CFSG.Quasithin.F112R.St84

end
