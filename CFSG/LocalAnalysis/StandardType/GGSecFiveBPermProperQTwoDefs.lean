module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

@[expose] def GGSecFiveBPermProperQTwoSpPairCell {G : Type} [Group G] (p : ℕ)
    (Bs L : Subgroup G) (𝒦 : Finset (Subgroup G)) (n : ℕ)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (K : Subgroup G) (a a' : Fin n) : Prop :=
  GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ lab.n = 1) p Bs L ∧ K ∈ 𝒦 ∧
    Nonempty (↥K ≃* StatedSp (n - 2) (GaloisField 2 1)) ∧
    (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
      bBlockOn n p ({a, a'} : Finset (Fin n))ᶜ

section Inputs


@[expose] def GGSecFiveBPermProperQTwoNbrInput : Prop :=
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
        B ≠ Bs →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ lab.n ≤ 1) p Bs L →
          (∃ (K : Subgroup G) (i0 : Fin n),
            GGSecFiveBPermUniSpCell p Bs L 𝒦 n eta 1 K i0 ∨
              GGSecFiveBPermUniOmCell p Bs L 𝒦 n eta 1 K i0) ∨
          (7 ≤ n ∧ ∃ (K : Subgroup G) (a a' : Fin n), a ≠ a' ∧
            (∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b a = eta b a')) ∧
            GGSecFiveBPermProperQTwoSpPairCell p Bs L 𝒦 n eta K a a')

@[expose] def GGSecFiveBPermProperQTwoSpPairInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 7 ≤ n →
      ∀ eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
        (¬ ∃ (f : ℕ) (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermSpCell p Bs L 𝒦 n eta f K i0) →
      ∀ (K : Subgroup G) (a a' : Fin n), a ≠ a' →
        (∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b a = eta b a')) →
        GGSecFiveBPermProperQTwoSpPairCell p Bs L 𝒦 n eta K a a' →
        ggG0 p B x L D J = L ⊔ K →
          ∃ ψ : StatedSp n (GaloisField 2 1) →* G,
            ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField 2 1)) ∧ ψ.range = L ⊔ K

end Inputs

end CFSG.StandardType

end
