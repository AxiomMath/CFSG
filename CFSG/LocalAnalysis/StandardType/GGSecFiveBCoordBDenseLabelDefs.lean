module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank

section Inputs


@[expose] def GGSecFiveBCoordBDenseNbrLabelInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 4 ≤ n →
      ∀ (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 →
      ∀ f : ℕ, 2 ≤ f →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧ lab.n = f) p Bs L →
        B = Bs →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
      ∀ K : Subgroup G, GGSecFiveBCoordBDenseNbr p Bs 𝒦 n eta K →
        (p ∣ 2 ^ f - 1 → GGHasLabel ⟨.A, n - 1, f⟩ (↥K ⧸ Subgroup.center ↥K)) ∧
          (p ∣ 2 ^ f + 1 → GGHasLabel ⟨.twA, n - 1, f⟩ (↥K ⧸ Subgroup.center ↥K))

end Inputs

end CFSG.StandardType

end
