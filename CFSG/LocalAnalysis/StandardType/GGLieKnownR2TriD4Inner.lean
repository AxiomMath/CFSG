module

public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4BridgeLongRoot
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4InnerLevi

public section

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg.TwistedD4
open CFSG.StandardType.S2MathFi1035Pos (TriField triD4Universal)
open scoped commutatorElement

namespace CFSG.StandardType.LieKnownR2.TriD4

theorem ggRootNormInner_triD4
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hF : TriField F σ g)
    {β : Fin (triD4Universal F σ).D.rank → ℤ} (hl : GGLongRoot (triD4Universal F σ).D β)
    (u : (triD4Universal F σ).K) :
    GGRootNormInner (((triD4Universal F σ).D.rootGroup β).map (MulAut.conj u).toMonoidHom) := by
  have hσ3 : ∀ c, σ (σ (σ c)) = c := by
    intro c
    haveI : Fintype F := Fintype.ofFinite F
    have hexp : ((c ^ 2 ^ g) ^ 2 ^ g) ^ 2 ^ g = c ^ ((2 ^ g) ^ 3) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [hF.2.2, hF.2.2, hF.2.2, hexp, ← hF.2.1, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  change GGRootNormInner
    (((twistedDatum σ).rootGroup β).map (MulAut.conj u).toMonoidHom)
  obtain ⟨m, hm⟩ := Bridge.triD4_longRoot_conj σ hσ3 hl
  rw [hm]
  exact ggRootNormInner_map_mulEquiv (MulAut.conj u)
    (ggRootNormInner_map_mulEquiv (MulAut.conj m)
      (Inner.ggRootNormInner_triD4_highRoot σ hF.1 hF.2.1 hF.2.2))

end CFSG.StandardType.LieKnownR2.TriD4
