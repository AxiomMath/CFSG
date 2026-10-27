module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Inputs


@[expose] def GGSecFiveBCoordBSparseSpLargeInput : Prop :=
  GGSecFiveBCoordBSparseOn fun _ _ lab => lab.n ≠ 1 ∧ (lab.tag = .B ∨ lab.tag = .C)

@[expose] def GGSecFiveBCoordBSparseTwDLargeInput : Prop :=
  GGSecFiveBCoordBSparseOn fun _ _ lab => lab.n ≠ 1 ∧ lab.tag = .twD

end Inputs

@[expose] def GGSecFiveBCoordBSparseEndpointFourOn (S : ℕ → ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → n = 4 →
      ∀ (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧ S n p lab) p Bs L →
        B = Bs →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
      ∀ (y : G) (hy : y ∈ Bs) (K : Subgroup G) (j : Fin n), K ∈ 𝒦 → GGNbr p B x D J y K →
        j ≠ i0 → (∀ k, k ≠ j → eta ⟨y, hy⟩ k = 1) →
        ((ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j ∨
          (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p j) →
        (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j ∧
          Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* (↥K ⧸ Subgroup.center ↥K))

end CFSG.StandardType

end
