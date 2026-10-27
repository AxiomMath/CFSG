module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRegionDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

@[expose] def GGIsWeylMatrixA {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  ∃ (n : ℕ) (e : Fin n ≃ ι), 1 ≤ n ∧ M = (CoxeterMatrix.A n).reindex e

@[expose] def GGIsWeylMatrixB {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  ∃ (n : ℕ) (e : Fin n ≃ ι), 2 ≤ n ∧ M = (CoxeterMatrix.B n).reindex e

@[expose] def GGIsWeylMatrixD {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  ∃ (n : ℕ) (e : Fin n ≃ ι), 4 ≤ n ∧ M = (ggCoxeterMatrixD n).reindex e

@[expose] def GGIsWeylMatrixF4 {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  ∃ e : Fin 4 ≃ ι, M = CoxeterMatrix.F₄.reindex e

@[expose] def GGIsWeylMatrixG2 {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  ∃ e : Fin 2 ≃ ι, M = CoxeterMatrix.G₂.reindex e

@[expose] def GGSecFiveDataResAt
    (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → T M → GGSecFiveData p B x L D J

end CFSG.StandardType

end
