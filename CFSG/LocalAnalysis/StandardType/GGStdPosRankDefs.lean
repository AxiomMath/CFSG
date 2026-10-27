module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

@[expose] def GGKGPosBaseHyp
    (p : ℕ) {G : Type} [Group G] (Bs X : Subgroup G) (t : StatedLieTag) (n f : ℕ)
    (ψ : (ggU t n f).K →* G) : Prop :=
  (p.Prime ∧ p ≠ 2 ∧ StatedLieAdmissible t n 2 f ∧ 3 ≤ bnRank t n) ∧
    (ψ.ker ≤ Subgroup.center (ggU t n f).K ∧ ψ.range = X ∧
      (t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) ∧ p ∣ 2 ^ f - 1) ∧
    (IsElemAbelian p Bs ∧ Bs ≤ Subgroup.normalizer (X : Set G) ∧
      ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) ∧
    (∀ b ∈ Bs, GGPsiInnerDiag (ggU t n f).D ψ b)

@[expose] def GGKGPosBoundsHyp (p : ℕ) {G : Type} [Group G] (Bs X : Subgroup G)
    (t : StatedLieTag) (n : ℕ) : Prop :=
  (¬ GGKGPosTorsion p t n →
      p ^ bnRank t n * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ Nat.card ↥Bs) ∧
    p ^ (bnRank t n - 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ Nat.card ↥Bs

theorem ggKGPosLocalHyp_iff
    {p : ℕ} {G : Type} [Group G] {Bs X : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} :
    GGKGPosLocalHyp p Bs X t n f ψ ↔
      GGKGPosBaseHyp p Bs X t n f ψ ∧ GGKGPosBoundsHyp p Bs X t n :=
  ⟨fun ⟨hA, hB, hC, hD, hE⟩ => ⟨⟨hA, hB, hC, hD⟩, hE⟩,
    fun ⟨⟨hA, hB, hC, hD⟩, hE⟩ => ⟨hA, hB, hC, hD, hE⟩⟩

@[expose] def GGKGPosRankStmt :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → GGSplitLie p X →
        ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
          GGKGPosLocalHyp p Bs X t n f ψ

end CFSG.StandardType

end
