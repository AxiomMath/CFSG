module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinusTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

variable {G : Type} [Group G]

@[expose] def GGSecFiveBPermLinOmKFrame {p n r f : ℕ} (Bs K : Subgroup G)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (π : Fin (r + 2) ≃ Fin n)
    (κ : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) →* G)
    (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ) : Prop :=
  Function.Injective κ ∧ κ.range = K ∧ Function.Injective χ ∧
    ∀ b : ↥Bs, ∃ t : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2),
      PsiDiag.SpinM.DiagAct t (fun m : Fin (r + 1) => χ (eta b (π m.succ))) ∧
        ∀ s, (b : G) * κ s * (b : G)⁻¹ = κ (t * s * t⁻¹)

section Inputs


@[expose] def GGSecFiveBPermOmKFrameInput : Prop :=
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
        B = Bs → GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermLinLabel n p lab) p Bs L →
      ∀ (f : ℕ) (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermOmCell p Bs L 𝒦 n eta f K i0 →
        ∃ (r : ℕ) (π : Fin (r + 2) ≃ Fin n), π 0 = i0 ∧
          ∃ (κ : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
              (minusCoeffs 2 f).2) →* G)
            (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ),
            GGSecFiveBPermLinOmKFrame Bs K eta π κ χ

end Inputs

end CFSG.StandardType

end
