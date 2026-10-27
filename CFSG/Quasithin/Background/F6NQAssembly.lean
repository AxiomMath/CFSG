module

public import CFSG.Quasithin.Background.F6NQShapes

public section

namespace CFSG.Quasithin

namespace F6

theorem f617NonquasisimpleCaseCat_of
    (hF : F613Two.{0}) (hQ : NativeSQTSection)
    (hW : WalterModelsStatement) : F617NonquasisimpleCaseCat := by
  intro D _ _ G₁ G₂ h hX _ K hK hKn h₁ h₂ _
  have hS := f617Setting_of hF hQ h hX hK hKn h₁ h₂
  obtain ⟨p, F, _, _, hp, hp5, hp8, hFc, hL2, ⟨eK⟩⟩ := hS.exists_psl2 hW
  exact hS.isF618CaseThree hp hp5 hp8 hFc hL2 eK

end F6

end CFSG.Quasithin
