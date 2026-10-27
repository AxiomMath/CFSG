module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.ClassicalInvolution.Phan

section Chart

variable {G : Type} [Group G] [Finite G]

@[expose] def QTwoDL1Chart4 (p : ℕ) (B Bs X : Subgroup G) : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (n : ℕ) (ψ : Su K 2 1 n →* G),
      Nat.card K = 4 ∧ GGNSLocalHyp p B Bs K 1 n ψ ∧ ψ.range = X ∧
        GGActsDiagonally (p := 2) (f := 1) ψ Bs ∧
        Nat.card ↥Bs = 3 ^ (n - 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ∨
    ∃ Φ : OrthTorus.OrthFrameCore p Bs X, Nat.card Φ.F = 2 ∧ 4 ≤ Φ.r ∧ (Φ.r = 4 → B < Bs) ∧
      Subgroup.center ↥X = ⊥

theorem QTwoDL1Chart.toChart4 {p : ℕ} {B Bs X : Subgroup G} (h : QTwoDL1Chart p B Bs X) :
    QTwoDL1Chart4 p B Bs X := by
  rcases h with h | ⟨Φ, hF, h5, hZ⟩
  · exact Or.inl h
  · exact Or.inr ⟨Φ, hF, by omega, fun h4 => absurd h4 (by omega), hZ⟩

end Chart

section Inputs

@[expose] def GGQTwoDSixTwE6InputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → m = 6 → M = (ggCoxeterMatrixD m).reindex e' →
        ∀ (y : G) (X : Subgroup G), GGNbr p B x D J y X →
          GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ p = 3) p Bs X →
            ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G),
              3 ^ 5 ≤ Nat.card (ggGamma X hN).range

@[expose] def GGQTwoDL1Chart4NbrInputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        ∀ (y : G) (X : Subgroup G), GGNbr p B x D J y X → QTwoDL1Chart4 p B Bs X

end Inputs

end CFSG.StandardType.QTwo

end
