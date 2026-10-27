module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal

@[expose] def GGSecFiveBPermLinNbrLabel (p n f : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab = ⟨.C, n - 1, f⟩ ∨ lab = ⟨.B, n - 1, f⟩ ∨ lab = ⟨.twD, n, f⟩ ∨
    (p = 3 ∧ f = 2 ∧ (lab = ⟨.A, 2 * n - 3, 1⟩ ∨ lab = ⟨.A, 2 * n - 2, 1⟩)) ∨
    (n = 4 ∧ ∃ a : ℕ, f = 2 * a ∧ 2 ≤ a ∧ p ∣ 2 ^ a - 1 ∧ lab = ⟨.twA, 5, a⟩)

section Inputs


@[expose] def GGSecFiveBPermLinNbrLabelInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 4 ≤ n →
      ∀ eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K → B = Bs →
      ∀ f : ℕ, 2 ≤ f →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermLinLabel n p lab ∧ lab.n = f) p Bs L →
      ∀ K ∈ 𝒦, ∀ i0 : Fin n,
        (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 →
          ∃ lab : LargeEvenLabel, GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) ∧
            GGSecFiveBPermLinNbrLabel p n f lab

@[expose] def GGSecFiveBPermLinSU6Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ e : (CoxeterMatrix.B 4).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B 4) e →
      ∀ eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p)),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 4 p →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K → B = Bs →
      ∀ a : ℕ, 2 ≤ a → p ∣ 2 ^ a - 1 →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermLinLabel 4 p lab ∧ lab.n = 2 * a) p Bs L →
      ∀ K ∈ 𝒦, ∀ i0 : Fin 4,
        (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p i0 →
        GGHasLabel ⟨.twA, 5, a⟩ (↥K ⧸ Subgroup.center ↥K) →
          Nonempty (↥K ≃*
            ↥(Unitary.SU (BorelTits.unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6))

end Inputs

end CFSG.StandardType

end
