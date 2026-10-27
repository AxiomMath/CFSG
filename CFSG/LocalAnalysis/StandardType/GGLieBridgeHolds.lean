module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreBridge
public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive
public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
public import CFSG.LocalAnalysis.StandardType.GGFinModelInput
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeHom
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeComp
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeTheta
public import CFSG.LocalAnalysis.StandardType.GGLieBridgePartner

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel
open CFSG.Open (StatedLieTag)

theorem ggLieBridge_holds
    : GGLieBridge := by
  intro p G _ _ t n f ψ G₀ D J hp hp2 ht hf hHyp
  have hpres := ggPresentsG0_of_bridgeHyp ht hHyp
  obtain ⟨θ, hθc, hθker, hθrange, hθcent⟩ := ggLieBridge_theta ht hf hpres
  have hΓ : θ.range ≤ ggFixGp t f := by
    rw [hθrange]
    refine Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂)
      (Subgroup.inv_mem _ h₁)) (Subgroup.inv_mem _ h₂)
  obtain ⟨-, -, -, hDN, hDinn, hel, hDC⟩ := hHyp
  obtain ⟨A, hAΦ, hAel, hAcard, hA₁, hA₂⟩ := ggLieBridge_partner_hom G₀ D (ggFixGp t f) θ
    hpres.2.2.1 hθker hDN hel hDC hθcent
    (fun d hd => ggLiePartner_exists ht hf hpres hΓ hθc (hDN hd) (hDinn d hd))
  exact ⟨θ, A, hθker, hθrange, hAΦ, hAel, hAcard, hA₁, hA₂,
    ggLieBridge_component G₀ D J _ A θ hθker hθrange hDN hA₁ hA₂⟩

end CFSG.StandardType.LieCore
