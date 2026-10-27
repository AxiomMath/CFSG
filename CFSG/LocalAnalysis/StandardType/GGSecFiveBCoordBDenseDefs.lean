module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBOmDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open scoped MatrixGroups

@[expose] def GGSecFiveBCoordBDenseNbr {G : Type} [Group G] (p : ℕ) (Bs : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (n : ℕ) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (K : Subgroup G) : Prop :=
  K ∈ 𝒦 ∧ ∃ δ ∈ bSignedFull n p, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
    (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom

@[expose] def GGSecFiveBCoordBUniCell {G : Type} [Group G] (p : ℕ) (Bs L : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (n f : ℕ) (K : Subgroup G) (i0 : Fin n) : Prop :=
  2 ≤ f ∧ Even n ∧ p ∣ 2 ^ f + 1 ∧ K ∈ 𝒦 ∧
    (∃ ψ : ↥(Unitary.SU (BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n) →* G,
      ψ.ker ≤ Subgroup.center
        ↥(Unitary.SU (BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n) ∧
      ψ.range = K) ∧
    Nonempty (↥L ≃*
      spinGroup (quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) ∧
    ∃ eta' : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
      (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta').toMonoidHom = bSignedFull n p ∧
      (ggAutomizer L Bs).map (MulAut.congr eta').toMonoidHom = bCoordinateBlock n p i0 ∧
      (ggAutomizer K Bs).map (MulAut.congr eta').toMonoidHom = aPermutationFull n p

section Inputs


@[expose] def GGSecFiveBCoordBDenseNbrOn (S : ℕ → ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 4 ≤ n →
      ∀ (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧ S n p lab) p Bs L →
        B = Bs →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
      ∀ K : Subgroup G, GGSecFiveBCoordBDenseNbr p Bs 𝒦 n eta K →
        ∃ f : ℕ, GGSecFiveBCoordBSpCell p Bs L 𝒦 n f K i0 ∨
          GGSecFiveBCoordBOmCell p Bs L 𝒦 n f K i0 ∨ GGSecFiveBCoordBUniCell p Bs L 𝒦 n f K i0

@[expose] def GGSecFiveBCoordBDenseNbrLargeInput : Prop :=
  GGSecFiveBCoordBDenseNbrOn fun _ _ lab => lab.n ≠ 1

@[expose] def GGSecFiveBCoordBUniInput : Prop :=
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
      ∀ (f : ℕ) (K : Subgroup G), GGSecFiveBCoordBUniCell p Bs L 𝒦 n f K i0 →
        ∃ ψ : (ggU .POmegaPlus (n + 1) f).K →* G,
          ψ.ker ≤ Subgroup.center (ggU .POmegaPlus (n + 1) f).K ∧ ψ.range = L ⊔ K

@[expose] def GGSecFiveBCoordBSparseOn (S : ℕ → ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 4 ≤ n →
      ∀ (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧ S n p lab) p Bs L →
        B = Bs →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
        (¬ ∃ (f : ℕ) (K : Subgroup G), GGSecFiveBCoordBSpCell p Bs L 𝒦 n f K i0) →
        (¬ ∃ (f : ℕ) (K : Subgroup G), GGSecFiveBCoordBSpSpCell p Bs L 𝒦 n eta f K i0) →
        (¬ ∃ (f : ℕ) (K : Subgroup G), GGSecFiveBCoordBOmCell p Bs L 𝒦 n f K i0) →
        (¬ ∃ K : Subgroup G, GGSecFiveBCoordBDenseNbr p Bs 𝒦 n eta K) →
          GGSecFiveData p B x L D J

@[expose] def GGSecFiveBCoordBSparseLargeInput : Prop :=
  GGSecFiveBCoordBSparseOn fun _ _ lab => lab.n ≠ 1

end Inputs

end CFSG.StandardType

end
