module

public import CFSG.LocalAnalysis.StandardType.GGLatRootBridge
public import CFSG.LocalAnalysis.StandardType.GGInterfaceSix

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section StdForm

variable {G : Type} [Group G] {U' : Type} [Group U']

structure GGStdForm (p : ℕ) (Bs G₀ : Subgroup G) (Δ : UniversalRootDatum U')
    (S : Matrix (Fin Δ.rank) (Fin Δ.rank) ℤ) (π : Equiv.Perm (Fin Δ.rank)) (f : ℕ) where
  coord : Bs →* Multiplicative (Fin Δ.rank → ZMod p)
  coord_inj : Function.Injective coord
  coord_fixed : ∀ b i, Multiplicative.toAdd (coord b) (π i) = Multiplicative.toAdd (coord b) i
  coord_surj : ∀ g ∈ LatCorootSpan Δ p, (∀ i, g (π i) = g i) →
    ∃ b, Multiplicative.toAdd (coord b) = g
  comp_ex : ∀ b : Bs, b ≠ 1 → ∀ O,
    IsCompOrbit S π (latPhi Δ.roots p (Multiplicative.toAdd (coord b))) O →
    ¬ LatSolv (f = 1) π O → ∃ L : Subgroup G,
      IsComponentOf L (G₀ ⊓ Subgroup.centralizer {(b : G)}) ∧
      ∀ b' : Bs, (b' : G) ∈ Subgroup.centralizer (L : Set G) ↔
        ∀ α ∈ O, latChar p (Multiplicative.toAdd (coord b')) α = 0
  comp_all : ∀ b : Bs, b ≠ 1 → ∀ L : Subgroup G,
    IsComponentOf L (G₀ ⊓ Subgroup.centralizer {(b : G)}) →
      ∃ O, IsCompOrbit S π (latPhi Δ.roots p (Multiplicative.toAdd (coord b))) O ∧
        ¬ LatSolv (f = 1) π O ∧
        (∀ b' : Bs, (b' : G) ∈ Subgroup.centralizer (L : Set G) ↔
          ∀ α ∈ O, latChar p (Multiplicative.toAdd (coord b')) α = 0) ∧
        Bs ≤ Subgroup.normalizer (L : Set G) ∧
        (∀ α ∈ O, latPerm π α = α → ∀ b' : Bs,
          Multiplicative.toAdd (coord b') = corootCoord p S α → (b' : G) ∈ L) ∧
        (IsSingleComp S (latPhi Δ.roots p (Multiplicative.toAdd (coord b))) O ∨
          ∃ k : ℕ, LieModel (↥L ⧸ Subgroup.center ↥L) .PSL k 2 (2 * f))

end StdForm

section Regime

@[expose] def GGExcRegime (p f : ℕ) : Prop := p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1

@[expose] def GGExcRegimeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), GGExcFive t →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    GGExcRegime p f

@[expose] def ggRankOneSub {U'' : Type} [Group U''] {G : Type} [Group G]
    (Δ : UniversalRootDatum U'') (ψ : U'' →* G) (α : Fin Δ.rank → ℤ) : Subgroup G :=
  (Δ.rootGroup α ⊔ Δ.rootGroup (-α)).map ψ

@[expose] def GGSixExcStandardFormInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), GGExcFive t →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    GGExcRegime p f →
      ∃ (S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ)
        (π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank))
        (F : GGStdForm p Bs (ggG0 p B x L D J) (ggU (absTag t) 6 f).D S π f),
        IsRootGram (ggU (absTag t) 6 f).D S ∧ IsDiagAut (ggU (absTag t) 6 f).D π ∧
        (t = .F4 ∨ t = .E7 ∨ t = .E8 → π = 1) ∧
        (t = .E6 → (π = 1 ↔ p ∣ 2 ^ f - 1)) ∧
        (t = .twistedE6 → (π = 1 ↔ p ∣ 2 ^ f + 1)) ∧
        (∀ α ∈ (ggU (absTag t) 6 f).D.roots, latPerm π α = α →
          ∃ (γ : Fin (ggU t n f).D.rank → ℤ) (u : (ggU t n f).K),
            GGRootClass (ggU t n f).D t γ ∧
            (∀ b : Bs, latChar p (Multiplicative.toAdd (F.coord b)) α = 0 →
              (b : G) ∈ Subgroup.centralizer (ggRootSub (ggU t n f).D ψ γ u : Set G)) ∧
            ∃ r ∈ ggRootSub (ggU t n f).D ψ γ u, orderOf r = 2) ∧
        (∀ α ∈ (ggU t n f).D.roots, GGRootClass (ggU t n f).D t α →
          (∃ x' ∈ ggRankOneSub (ggU t n f).D ψ α, orderOf x' = p) ∧
          ∀ x' ∈ ggRankOneSub (ggU t n f).D ψ α, orderOf x' = p →
            ∃ h ∈ ggG0 p B x L D J, ∃ αB ∈ (ggU (absTag t) 6 f).D.roots, latPerm π αB = αB ∧
              ∃ k : ZMod p, k ≠ 0 ∧ ∃ b : Bs, (b : G) = h * x' * h⁻¹ ∧
                Multiplicative.toAdd (F.coord b) = k • corootCoord p S αB)

end Regime

end CFSG.StandardType
