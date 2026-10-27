module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock shortBlock)
open scoped MatrixGroups

@[expose] def GGSecFiveBCoordBSpSpCell {G : Type} [Group G] (p : ℕ) (Bs L : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (n : ℕ) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (f : ℕ)
    (K : Subgroup G) (i0 : Fin n) : Prop :=
  2 ≤ f ∧ 5 ≤ n ∧ K ∈ 𝒦 ∧
    Nonempty (↥L ≃* StatedSp (n - 1) (GaloisField 2 f)) ∧
    Nonempty (↥K ≃* StatedSp (n - 1) (GaloisField 2 f)) ∧
    ∃ j : Fin n, j ≠ i0 ∧
      (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j

section Inputs


@[expose] def GGSecFiveBCoordBSpSpChartInput : Prop :=
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
      ∀ (f : ℕ) (K : Subgroup G), GGSecFiveBCoordBSpSpCell p Bs L 𝒦 n eta f K i0 →
        ∃ s : ℕ, n = s + 3 ∧ ∃ κ₁ κ₂ : StatedSp (s + 2) (GaloisField 2 f) →* G,
          Function.Injective κ₁ ∧ κ₁.range = L ∧ Function.Injective κ₂ ∧ κ₂.range = K ∧
          (∀ k : Fin s,
            (κ₁.comp (shortBlock (GaloisField 2 f) (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
              (κ₂.comp (shortBlock (GaloisField 2 f)
                (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range) ∧
          (κ₁.comp (longBlock (GaloisField 2 f) (s + 2) (Fin.last (s + 1)))).range =
            (κ₂.comp (longBlock (GaloisField 2 f) (s + 2) (Fin.last s).castSucc)).range ∧
          (∀ a ∈ (κ₁.comp (shortBlock (GaloisField 2 f)
              (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
            ∀ b ∈ (κ₂.comp (shortBlock (GaloisField 2 f)
              (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range, a * b = b * a) ∧
          ∀ a ∈ (κ₁.comp (shortBlock (GaloisField 2 f)
              (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
            ∀ b ∈ (κ₂.comp (longBlock (GaloisField 2 f) (s + 2) (Fin.last (s + 1)))).range,
              a * b = b * a

@[expose] def GGSecFiveBCoordBOffSpSpInput : Prop :=
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
        (¬ ∃ (f : ℕ) (K : Subgroup G), GGSecFiveBCoordBSpSpCell p Bs L 𝒦 n eta f K i0) →
          GGSecFiveData p B x L D J

end Inputs

end CFSG.StandardType

end
