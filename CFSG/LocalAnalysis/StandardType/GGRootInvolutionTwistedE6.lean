module

public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionCore
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6PosLift
public import CFSG.LieType.HighestRoot.GenModels

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.CentralExt
  CFSG.LieType.Steinberg.Minuscule

theorem twistedRootGroup_mul_comm {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β) :
    ∀ x ∈ twistedRootGroup k θ β, ∀ y ∈ twistedRootGroup k θ β, x * y = y * x := by
  intro x hx y hy
  obtain ⟨hα, hp⟩ := liftRoot_spec hβ
  by_cases hfix : rho (liftRoot β) = liftRoot β
  · obtain ⟨s, rfl⟩ := TwistedE6Closed.exists_xF_eq θ hα hp hfix hx
    obtain ⟨u, rfl⟩ := TwistedE6Closed.exists_xF_eq θ hα hp hfix hy
    rw [← TwistedE6Closed.xF_add, ← TwistedE6Closed.xF_add, add_comm]
  · obtain ⟨s, rfl⟩ := TwistedE6Closed.exists_xPair_eq θ hθ hα hp hfix hx
    obtain ⟨u, rfl⟩ := TwistedE6Closed.exists_xPair_eq θ hθ hα hp hfix hy
    rw [← TwistedE6Closed.xPair_add, ← TwistedE6Closed.xPair_add, add_comm]

theorem ggRootSylowCentral_twistedE6 {k : Type} [Field k] [Finite k] [CharP k 2] (θ : k →+* k)
    (hθ : ∀ c, θ (θ c) = c) : GGRootSylowCentral (twistedDatum k θ) .twistedE6 := by
  have : Finite (Module.End k (Fin e6Data.d →₀ k)) := Module.finite_of_finite k
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ggRootSylowCentral_of_longRoot_reduced
    (twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ))
    (twistedDatum_steinbergExtras θ hθ) (twistedDatum_bruhatExtras θ) rfl
    (fun β hβ => CFSG.LieType.HighestRoot.isPGroup_twistedE6_rootGroup θ
      (isRoot_of_mem_twistedDatum_roots θ hβ))
    (TwistedE6Closed.coprime_card_torus θ hθ)
    (fun β hβ _ => twistedRootGroup_mul_comm θ hθ (isRoot_of_mem_twistedDatum_roots θ hβ))
    fun γ hγ => hγ.longRoot_of_twisted (Or.inr (Or.inr rfl))

end CFSG.StandardType
