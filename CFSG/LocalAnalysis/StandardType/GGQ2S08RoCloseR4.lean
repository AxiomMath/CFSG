module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoCloseDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoAbsorbPrime
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoCloseAux
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoCloseAux5

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08_roClose_of_components (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs))
    (M : GGQ2LDatum 3 Bs L x)
    {N : ℕ} (h2 : 2 ≤ N) (f : Fin N → M.V) (hf : GGQ2S08ROFrame M f)
    (hQ : GGQ2S08ROComponents M f)
    (hD : ∀ g : M.V ≃ₗ[ZMod 3] M.V, GGQ2S08MonoEven f g →
      ∃ (k : G) (φ : MulAut ↥Bs), GGQ2Ind Bs k φ ∧
        k ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) ∧ ggLin (p := 3) M.model φ = g) :
    ∀ (g : G) (φ : MulAut ↥Bs), GGQ2Ind Bs g φ → GGQ2S08Mono f (ggLin (p := 3) M.model φ) →
      g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  classical
  obtain ⟨Q, hQle, hQcomp, hQnorm, hQa, hQgen⟩ := hQ
  refine ggQ2s08r4_reduce hS M h2 f hf hD ?_
  intro g φ hInd hcase
  rcases hcase with h1 | ⟨k, hk⟩
  · exact ggQ2s08r4_identity hLB hP hS hCav M f hf hInd h1
  · exact ggQ2s08r4_sign hLB hP hS hCav M h2 f hf Q hQle hQcomp hQnorm hQa hQgen hD
      hInd ⟨k, hk⟩

end CFSG.StandardType

end
