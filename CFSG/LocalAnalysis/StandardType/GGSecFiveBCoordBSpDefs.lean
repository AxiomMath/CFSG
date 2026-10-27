module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (blockSL2)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock shortBlock)
open scoped MatrixGroups

@[expose] def GGSecFiveBCoordBBstarInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ∀ (n : ℕ), 4 ≤ n → ∀ (_ : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))),
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab) p Bs L →
          B = Bs ∨ GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧ 5 ≤ n ∧
            (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ p = 3) p Bs L

@[expose] def GGSecFiveBCoordBSpCell {G : Type} [Group G] (p : ℕ) (Bs L : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (n f : ℕ) (K : Subgroup G) (i0 : Fin n) : Prop :=
  2 ≤ f ∧ K ∈ 𝒦 ∧
    (∃ ψ : SL(n, GaloisField 2 f) →* G,
      ψ.ker ≤ Subgroup.center SL(n, GaloisField 2 f) ∧ ψ.range = K) ∧
    Nonempty (↥L ≃* StatedSp (n - 1) (GaloisField 2 f)) ∧
    ∃ eta' : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
      (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta').toMonoidHom = bSignedFull n p ∧
      (ggAutomizer L Bs).map (MulAut.congr eta').toMonoidHom = bCoordinateBlock n p i0 ∧
      (ggAutomizer K Bs).map (MulAut.congr eta').toMonoidHom = aPermutationFull n p

section Inputs


@[expose] def GGSecFiveBCoordBProperInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 4 ≤ n →
      ∀ (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧ 5 ≤ n ∧
          (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ p = 3) p Bs L →
        B ≠ Bs →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
          GGSecFiveData p B x L D J

@[expose] def GGSecFiveBCoordBSpChartInput : Prop :=
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
      ∀ (f : ℕ) (K : Subgroup G), GGSecFiveBCoordBSpCell p Bs L 𝒦 n f K i0 →
        ∃ r : ℕ, n = r + 2 ∧ ∃ (σ : SL(r + 2, GaloisField 2 f) →* G)
          (κ : StatedSp (r + 1) (GaloisField 2 f) →* G),
          σ.ker ≤ Subgroup.center SL(r + 2, GaloisField 2 f) ∧ σ.range = K ∧
          Function.Injective κ ∧ κ.range = L ∧
          (∀ k : Fin r, (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) k.succ)).range =
            (κ.comp (shortBlock (GaloisField 2 f) (Fin.castSucc_lt_succ (i := k)).ne)).range) ∧
          ∀ a ∈ (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) 0)).range,
            ∀ b ∈ (κ.comp (longBlock (GaloisField 2 f) (r + 1) (Fin.last r))).range,
              a * b = b * a

@[expose] def GGSecFiveBCoordBOffSpInput : Prop :=
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
        (¬ ∃ (f : ℕ) (K : Subgroup G), GGSecFiveBCoordBSpCell p Bs L 𝒦 n f K i0) →
          GGSecFiveData p B x L D J

end Inputs

end CFSG.StandardType

end
