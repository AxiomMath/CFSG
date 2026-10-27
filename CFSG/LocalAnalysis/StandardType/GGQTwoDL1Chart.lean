module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan

section Defs

variable {G : Type} [Group G]

@[expose] def QTwoDL1Chart [Finite G] (p : ℕ) (B Bs X : Subgroup G) : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (n : ℕ) (ψ : Su K 2 1 n →* G),
      Nat.card K = 4 ∧ GGNSLocalHyp p B Bs K 1 n ψ ∧ ψ.range = X ∧
        GGActsDiagonally (p := 2) (f := 1) ψ Bs ∧
        Nat.card ↥Bs = 3 ^ (n - 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ∨
    ∃ Φ : OrthTorus.OrthFrameCore p Bs X, Nat.card Φ.F = 2 ∧ 5 ≤ Φ.r ∧
      Subgroup.center ↥X = ⊥

end Defs

section Inputs


@[expose] def GGQTwoDL1ChartLInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), 7 ≤ m → M = (ggCoxeterMatrixD m).reindex e' →
        QTwoDL1Chart p B Bs L

@[expose] def GGQTwoDL1ChartNbrInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), 7 ≤ m → M = (ggCoxeterMatrixD m).reindex e' →
        ∀ (y : G) (X : Subgroup G), GGNbr p B x D J y X → QTwoDL1Chart p B Bs X

@[expose] def GGQTwoDL1ChartInputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        ∀ X : Subgroup G, (X = L ∨ ∃ y : G, GGNbr p B x D J y X) → QTwoDL1Chart p B Bs X

@[expose] def GGQTwoDL1ChartInput : Prop :=
  GGQTwoDL1ChartInputOn fun m => 7 ≤ m

theorem ggQTwoDL1ChartInput_of_L_nbr (hL : GGQTwoDL1ChartLInput)
    (hN : GGQTwoDL1ChartNbrInput) : GGQTwoDL1ChartInput := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM X hX
  rcases hX with rfl | ⟨y, hy⟩
  · exact hL G p B Bs x X D J 𝒦 ι M e hcfg m e' hm hM
  · exact hN G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM y X hy

end Inputs

end CFSG.StandardType.QTwo

end
