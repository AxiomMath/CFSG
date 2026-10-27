module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBOffSpSpQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalInvolution.WeakCT (blockSL2)
open scoped MatrixGroups

@[expose] def GGSecFiveBCoordBOmCell {G : Type} [Group G] (p : ℕ) (Bs L : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (n f : ℕ) (K : Subgroup G) (i0 : Fin n) : Prop :=
  2 ≤ f ∧ K ∈ 𝒦 ∧
    (∃ ψ : SL(n, GaloisField 2 f) →* G,
      ψ.ker ≤ Subgroup.center SL(n, GaloisField 2 f) ∧ ψ.range = K) ∧
    Nonempty (↥L ≃*
      spinGroup (quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) ∧
    ∃ eta' : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
      (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta').toMonoidHom = bSignedFull n p ∧
      (ggAutomizer L Bs).map (MulAut.congr eta').toMonoidHom = bCoordinateBlock n p i0 ∧
      (ggAutomizer K Bs).map (MulAut.congr eta').toMonoidHom = aPermutationFull n p

section Inputs

@[expose] def GGSecFiveBCoordBOmChartInput : Prop :=
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
      ∀ (f : ℕ) (K : Subgroup G), GGSecFiveBCoordBOmCell p Bs L 𝒦 n f K i0 →
        ∃ r : ℕ, n = r + 2 ∧ ∃ (σ : SL(r + 2, GaloisField 2 f) →* G)
          (κ : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
            (minusCoeffs 2 f).2) →* G),
          σ.ker ≤ Subgroup.center SL(r + 2, GaloisField 2 f) ∧ σ.range = K ∧
          Function.Injective κ ∧ κ.range = L ∧
          (∀ k : Fin r, (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) k.succ)).range =
            (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
              k.castSucc).map κ) ∧
          ∀ a ∈ (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) 0)).range,
            ∀ b ∈ (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
              (Fin.last r)).map κ, a * b = b * a

@[expose] def GGSecFiveBCoordBOffSpSpOmOn (S : ℕ → ℕ → LargeEvenLabel → Prop) : Prop :=
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
          GGSecFiveData p B x L D J

@[expose] def GGSecFiveBCoordBOffSpSpOmLargeInput : Prop :=
  GGSecFiveBCoordBOffSpSpOmOn fun _ _ lab => lab.n ≠ 1

end Inputs

end CFSG.StandardType

end
