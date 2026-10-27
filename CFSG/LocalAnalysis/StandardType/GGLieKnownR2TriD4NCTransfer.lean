module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4NCC0
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ExcNCRoots

public section

namespace CFSG.StandardType.LieKnownR2.TriD4.NC

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedD4 CFSG.SeitzReduction
open scoped commutatorElement

theorem ggRootNoCentral_triD4_highRoot
    {K : Type} [Field K] [Finite K] (σ : K →+* K) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    GGRootNoCentralAt (⊤ : Subgroup (twistedGroup σ))
      ((twistedDatum σ).rootGroup (highRoot .G2)) := by
  have hC0 := triD4_noCentral_C0 σ hf hK hσ
  have h := ggRootNoCentralAt_top_map_mulEquiv
    (Bridge.triD4BridgeEquiv σ hf hK hσ).symm hC0
  have hEq := Bridge.triD4BridgeEquiv_twistedRootGroup_highRoot σ hf hK hσ
  rw [← hEq, GGRootNorm.map_symm_map] at h
  exact h

end CFSG.StandardType.LieKnownR2.TriD4.NC
