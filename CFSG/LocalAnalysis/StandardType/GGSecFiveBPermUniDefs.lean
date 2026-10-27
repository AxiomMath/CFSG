module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOffSpCaseDefs
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofRed
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Remainder
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverOdd

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock shortBlock)
open scoped MatrixGroups

@[expose] def GGSecFiveBPermUniSpCell {G : Type} [Group G] (p : ℕ) (Bs L : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (n : ℕ) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (f : ℕ)
    (K : Subgroup G) (i0 : Fin n) : Prop :=
  GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ lab.n = f) p Bs L ∧ K ∈ 𝒦 ∧
    Nonempty (↥K ≃* StatedSp (n - 1) (GaloisField 2 f)) ∧
    (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0

@[expose] def GGSecFiveBPermUniOmCell {G : Type} [Group G] (p : ℕ) (Bs L : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (n : ℕ) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (f : ℕ)
    (K : Subgroup G) (i0 : Fin n) : Prop :=
  GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ lab.n = f) p Bs L ∧ K ∈ 𝒦 ∧
    ((Even n ∧ ∃ b c : GaloisField 2 f, (∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (↥K ≃* StatedOmega (StatedQuadMinus n (GaloisField 2 f) b c))) ∨
      (Odd n ∧ Nonempty (↥K ≃* StatedOmega (StatedQuadPlus n (GaloisField 2 f))))) ∧
    (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0

section Inputs


@[expose] def GGSecFiveBPermUniQGeFourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 4 ≤ n →
      ∀ eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
        (¬ ∃ (f : ℕ) (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermSpCell p Bs L 𝒦 n eta f K i0) →
        B = Bs →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ 2 ≤ lab.n) p Bs L →
          GGSecFiveData p B x L D J

@[expose] def GGSecFiveBPermUniQTwoInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 4 ≤ n →
      ∀ eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
        (¬ ∃ (f : ℕ) (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermSpCell p Bs L 𝒦 n eta f K i0) →
        B = Bs →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ lab.n ≤ 1) p Bs L →
          GGSecFiveData p B x L D J

@[expose] def GGSecFiveBPermUniNbrInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 4 ≤ n →
      ∀ eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
        (¬ ∃ (f : ℕ) (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermSpCell p Bs L 𝒦 n eta f K i0) →
        B = Bs →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ 2 ≤ lab.n) p Bs L →
          ∃ (f : ℕ) (K : Subgroup G) (i0 : Fin n), 2 ≤ f ∧
            (GGSecFiveBPermUniSpCell p Bs L 𝒦 n eta f K i0 ∨
              GGSecFiveBPermUniOmCell p Bs L 𝒦 n eta f K i0)

@[expose] def GGSecFiveBPermUniSpChartInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 5 ≤ n →
      ∀ eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
        (¬ ∃ (f : ℕ) (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermSpCell p Bs L 𝒦 n eta f K i0) →
      ∀ (f : ℕ) (K : Subgroup G) (i0 : Fin n), 2 ≤ f →
        GGSecFiveBPermUniSpCell p Bs L 𝒦 n eta f K i0 →
          ∃ s : ℕ, n = s + 3 ∧ ∃ κ₁ κ₂ : StatedSp (s + 2) (GaloisField 2 f) →* G,
            Function.Injective κ₁ ∧ Function.Injective κ₂ ∧ κ₁.range ⊔ κ₂.range = L ⊔ K ∧
            (∀ k : Fin s,
              (κ₁.comp (shortBlock (GaloisField 2 f)
                (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
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

@[expose] def GGSecFiveBPermUniOmInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 5 ≤ n →
      ∀ eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
        (¬ ∃ (f : ℕ) (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermSpCell p Bs L 𝒦 n eta f K i0) →
      ∀ (f : ℕ) (K : Subgroup G) (i0 : Fin n), 2 ≤ f →
        GGSecFiveBPermUniOmCell p Bs L 𝒦 n eta f K i0 →
          (∃ ψ : (ggU .POmegaPlus (n + 1) f).K →* G,
              ψ.ker ≤ Subgroup.center (ggU .POmegaPlus (n + 1) f).K ∧ ψ.range = L ⊔ K) ∨
            ∃ ψ : (ggU .POmegaMinus (n + 1) f).K →* G,
              ψ.ker ≤ Subgroup.center (ggU .POmegaMinus (n + 1) f).K ∧ ψ.range = L ⊔ K

@[expose] def GGSecFiveBPermUniFourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → n = 4 →
      ∀ eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
        (¬ ∃ (f : ℕ) (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermSpCell p Bs L 𝒦 n eta f K i0) →
        B = Bs →
      ∀ (f : ℕ) (K : Subgroup G) (i0 : Fin n), 2 ≤ f →
        (GGSecFiveBPermUniSpCell p Bs L 𝒦 n eta f K i0 ∨
          GGSecFiveBPermUniOmCell p Bs L 𝒦 n eta f K i0) →
        ggG0 p B x L D J = L ⊔ K →
          GGSecFiveData p B x L D J

@[expose] def GGSecFiveBPermUniQTwoNbrInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 5 ≤ n →
      ∀ eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
        (¬ ∃ (f : ℕ) (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermSpCell p Bs L 𝒦 n eta f K i0) →
        B = Bs →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ lab.n ≤ 1) p Bs L →
        Line63.H5.twoCenter L = ⊥ →
          ∃ (K : Subgroup G) (i0 : Fin n),
            GGSecFiveBPermUniSpCell p Bs L 𝒦 n eta 1 K i0 ∨
              GGSecFiveBPermUniOmCell p Bs L 𝒦 n eta 1 K i0

@[expose] def GGSecFiveBPermUniQTwoSpInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 5 ≤ n →
      ∀ eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
        (¬ ∃ (f : ℕ) (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermSpCell p Bs L 𝒦 n eta f K i0) →
        Line63.H5.twoCenter L = ⊥ →
      ∀ (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermUniSpCell p Bs L 𝒦 n eta 1 K i0 →
        ggG0 p B x L D J = L ⊔ K →
          GGSecFiveData p B x L D J

@[expose] def GGSecFiveBPermUniQTwoOmInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 5 ≤ n →
      ∀ eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
        (¬ ∃ (f : ℕ) (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermSpCell p Bs L 𝒦 n eta f K i0) →
        Line63.H5.twoCenter L = ⊥ →
      ∀ (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermUniOmCell p Bs L 𝒦 n eta 1 K i0 →
          (∃ ψ : (ggU .POmegaPlus (n + 1) 1).K →* G,
              ψ.ker ≤ Subgroup.center (ggU .POmegaPlus (n + 1) 1).K ∧ ψ.range = L ⊔ K) ∨
            ∃ ψ : (ggU .POmegaMinus (n + 1) 1).K →* G,
              ψ.ker ≤ Subgroup.center (ggU .POmegaMinus (n + 1) 1).K ∧ ψ.range = L ⊔ K

@[expose] def GGSecFiveBPermUniQTwoExcInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 5 ≤ n →
      ∀ eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
        (¬ ∃ (f : ℕ) (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermSpCell p Bs L 𝒦 n eta f K i0) →
        B = Bs →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ lab.n ≤ 1) p Bs L →
        Line63.H5.twoCenter L ≠ ⊥ →
          GGSecFiveData p B x L D J

end Inputs

end CFSG.StandardType

end
