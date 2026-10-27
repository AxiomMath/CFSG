module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniDefs
public import CFSG.LocalAnalysis.StandardType.GGNsq2Cited

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Inputs


@[expose] def GGSecFiveBPermUniQTwoExcSixInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (e : (CoxeterMatrix.B 6).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B 6) e →
      ∀ eta : ↥Bs ≃* (Fin 6 → Multiplicative (ZMod p)),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 6 p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 6 p →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
        (¬ ∃ (f : ℕ) (K : Subgroup G) (i0 : Fin 6), GGSecFiveBPermSpCell p Bs L 𝒦 6 eta f K i0) →
        B = Bs →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel 6 p lab ∧ lab.n ≤ 1) p Bs L →
        Line63.H5.twoCenter L ≠ ⊥ →
          GGSecFiveData p B x L D J

@[expose] def GGSecFiveBPermUniQTwoExcSixU62Input : Prop :=
  GGU62OuterDiagInput → GGSecFiveBPermUniQTwoExcSixInput

end Inputs

end CFSG.StandardType

end
