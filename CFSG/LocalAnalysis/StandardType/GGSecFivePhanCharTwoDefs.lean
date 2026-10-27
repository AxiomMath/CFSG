module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
public import CFSG.LocalAnalysis.StandardType.GGPhanCentralQuotient
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.LieType.Universal

@[expose] def PhanDInput2 :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2],
    Nat.card K = (2 ^ f) ^ 2 → 4 ≤ 2 ^ f → ∀ n : ℕ, 4 ≤ n →
    ∀ {X : Type} [Group X] (U : Fin n → Subgroup X) (W : Fin n → Fin n → Subgroup X),
      WeakPhanSL K 2 f (CFSG.StandardType.ggCoxeterMatrixD n) U W →
      (Even n → IsCentralQuotientOf (lieUniversal .POmegaPlus n 2 f Nat.prime_two) X) ∧
      (Odd n → IsCentralQuotientOf (lieUniversal .POmegaMinus n 2 f Nat.prime_two) X)

@[expose] def PhanEInput2 :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2],
    Nat.card K = (2 ^ f) ^ 2 → 4 ≤ 2 ^ f →
    (∀ {X : Type} [Group X] (U : Fin 6 → Subgroup X) (W : Fin 6 → Fin 6 → Subgroup X),
      WeakPhanSL K 2 f CoxeterMatrix.E₆ U W →
        IsCentralQuotientOf (lieUniversal .twistedE6 0 2 f Nat.prime_two) X) ∧
    (∀ {X : Type} [Group X] (U : Fin 7 → Subgroup X) (W : Fin 7 → Fin 7 → Subgroup X),
      WeakPhanSL K 2 f CoxeterMatrix.E₇ U W →
        IsCentralQuotientOf (lieUniversal .E7 0 2 f Nat.prime_two) X) ∧
    (∀ {X : Type} [Group X] (U : Fin 8 → Subgroup X) (W : Fin 8 → Fin 8 → Subgroup X),
      WeakPhanSL K 2 f CoxeterMatrix.E₈ U W →
        IsCentralQuotientOf (lieUniversal .E8 0 2 f Nat.prime_two) X)

end CFSG.ClassicalInvolution.Phan

end
