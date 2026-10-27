module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT

section KGPos

@[expose] def ggRootLevi {K : Type} [Group K] (D : UniversalRootDatum K)
    (γ : Fin D.rank → ℤ) : Subgroup K :=
  D.rootGroup γ ⊔ D.rootGroup (-γ)

@[expose] def GGTableBPos (p : ℕ) {G : Type} [Group G] (Bs X : Subgroup G) (t : StatedLieTag)
    (n f : ℕ) (ψ : (ggU t n f).K →* G) : Prop :=
  ∃ ε : (coxeterMatrix (ggU t n f).D.isFiniteType).Group ≃* ↥(ggAutomizer X Bs),
    (∀ i, GGIsReflection p
      ((ε ((coxeterMatrix (ggU t n f).D.isFiniteType).simple i) : ↥(ggAutomizer X Bs)) :
        MulAut ↥Bs)) ∧
    (∀ (w : (coxeterMatrix (ggU t n f).D.isFiniteType).Group) (i : Fin (ggU t n f).D.rank),
      ggRankOneIn X Bs
        ((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹) :
          ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
        (ggRootLevi (ggU t n f).D
          (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1))).map ψ) ∧
    Nat.card ↥Bs ≤ p ^ (ggU t n f).D.rank *
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G))

@[expose] def GGSecFiveKGPosInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → GGSplitLie p X →
          ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
            StatedLieAdmissible t n 2 f ∧ 3 ≤ bnRank t n ∧
              ψ.ker ≤ Subgroup.center (ggU t n f).K ∧ ψ.range = X ∧
              (t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) ∧ p ∣ 2 ^ f - 1 ∧
              GGTableBPos p Bs X t n f ψ

end KGPos

end CFSG.StandardType
