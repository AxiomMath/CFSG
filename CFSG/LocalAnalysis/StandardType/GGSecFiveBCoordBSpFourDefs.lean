module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSpDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrameDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

@[expose] def GGSecFiveBCoordBSpFourCell {G : Type} [Group G] (p : ℕ) (Bs L : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (n : ℕ) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (f : ℕ)
    (K : Subgroup G) (i0 : Fin n) : Prop :=
  2 ≤ f ∧ n = 4 ∧ K ∈ 𝒦 ∧
    Nonempty (↥L ≃* StatedSp (n - 1) (GaloisField 2 f)) ∧
    Nonempty (↥K ≃* StatedSp (n - 1) (GaloisField 2 f)) ∧
    ∃ j : Fin n, j ≠ i0 ∧
      (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j

section Inputs


@[expose] def GGSecFiveBCoordBSpFourCrossInput : Prop :=
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
      ∀ a ∈ ⁅Subgroup.centralizer (ggBsCoordEq Bs eta j u : Set G), Bs⁆,
      ∀ b ∈ ⁅Subgroup.centralizer (ggBsCoordEq Bs eta v i0 : Set G), Bs⁆, a * b = b * a

@[expose] def GGSecFiveBCoordBSpFourInput : Prop :=
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
        GGSecFiveData p B x L D J

end Inputs

end CFSG.StandardType

end
