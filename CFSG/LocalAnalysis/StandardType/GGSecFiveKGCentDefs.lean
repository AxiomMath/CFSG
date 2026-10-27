module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

@[expose] def ggKGCentRoots {U : Type*} [Group U] (Δ : UniversalRootDatum U) {G : Type*}
    [Group G] (ψ : U →* G) (S : Subgroup G) : Set (Fin Δ.rank → ℤ) :=
  {β | β ∈ Δ.roots ∧ Δ.rootGroup β ≤ (Subgroup.centralizer (S : Set G)).comap ψ}

@[expose] def ggKGCentRootSpan {U : Type*} [Group U] (Δ : UniversalRootDatum U) {G : Type*}
    [Group G] (ψ : U →* G) (S : Subgroup G) : Subgroup U :=
  ⨆ β ∈ ggKGCentRoots Δ ψ S, Δ.rootGroup β

@[expose] def GGKGCentTagStmt
    (tg : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      (∃ r ∈ ggAutomizer J Bs, GGIsReflection p r) →
      ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ∀ (n f : ℕ) (ψ : (ggU tg n f).K →* G),
        GGKGPosLocalHyp p Bs X tg n f ψ → GGKGPosStdPos (ggU tg n f).D ψ Bs →
          ∀ t : G, (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∈ Subgroup.normalizer (X : Set G) →
            t ∈ Subgroup.centralizer (D : Set G) → t ∈ Subgroup.centralizer (J : Set G) →
              ∀ g ∈ X, ∀ h ∈ X, Commute (t * g * t⁻¹ * g⁻¹) h

end CFSG.StandardType

end
