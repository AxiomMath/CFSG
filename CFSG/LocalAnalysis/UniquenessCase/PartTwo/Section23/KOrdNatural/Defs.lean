module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def NatOrderClass {W : Type} [CommGroup W] (H : Subgroup (MulAut W)) (n : ℕ) : Prop :=
  Nontrivial ↥H ∧
    ((BinaryNaturalSL H ⊤ ⊥ 2 n ∧ Nat.card ↥H = 2 ^ n * ((2 ^ n) ^ 2 - 1)) ∨
      (NatOmegaMinus H ⊤ ⊥ 4 n ∧ Nat.card ↥H = (2 ^ n) ^ 2 * ((2 ^ n) ^ 4 - 1)) ∨
      (Nat.card ↥H ∣ 2 * (2 ^ n) ^ 2 * ((2 ^ n) ^ 2 - 1) ^ 2 ∧
        (2 ≤ n → (2 ^ n) ^ 2 ∣ Nat.card ↥H)) ∨
      (2 ^ n) ^ 3 ∣ Nat.card ↥H)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

end
