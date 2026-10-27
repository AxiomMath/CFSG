module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpFourDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Basic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Models.SymplecticPairs

section Inputs


@[expose] def GGSecFiveBCoordBSpFourCommonChartInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 4 ≤ n →
      ∀ (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab) p Bs L →
        B = Bs →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
      ∀ (f : ℕ) (K : Subgroup G), GGSecFiveBCoordBSpFourCell p Bs L 𝒦 n eta f K i0 →
      ∀ j : Fin n, j ≠ i0 →
        (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j →
      ∀ u v : Fin n, j ≠ u → j ≠ v → u ≠ v → u ≠ i0 → v ≠ i0 →
      ∃ ψ : StatedSp 2 (GaloisField 2 f) →* G, Function.Injective ψ ∧
        ψ.range = ggBlockComm Bs eta {u, v} ∧
        (ψ.comp (longBlock (GaloisField 2 f) 2 0)).range =
          ⁅Subgroup.centralizer (ggBsCoordZero Bs eta u : Set G), Bs⁆ ∧
        (ψ.comp (longBlock (GaloisField 2 f) 2 1)).range =
          ⁅Subgroup.centralizer (ggBsCoordZero Bs eta v : Set G), Bs⁆

@[expose] def GGSecFiveBCoordBSpFourCommonCompInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 4 ≤ n →
      ∀ (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab) p Bs L →
        B = Bs →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
      ∀ (f : ℕ) (K : Subgroup G), GGSecFiveBCoordBSpFourCell p Bs L 𝒦 n eta f K i0 →
      ∀ j : Fin n, j ≠ i0 →
        (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j →
      ∀ u v : Fin n, j ≠ u → j ≠ v → u ≠ v → u ≠ i0 → v ≠ i0 →
      ∃ d ∈ ggBsCoordEq Bs eta j i0,
        CFSG.Assembly.IsComponentOf (ggBlockComm Bs eta {u, v})
          (Subgroup.centralizer ({d} : Set G))

end Inputs

end CFSG.StandardType

end
