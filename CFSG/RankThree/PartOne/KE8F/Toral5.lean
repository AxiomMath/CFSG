module

public import CFSG.RankThree.PartOne.KE8F.E8Frame

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE


@[expose] def E8FiveToral {K L : Type} [Field K] [Field L] [Algebra K L] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] (F : E8P4Frame0 K L ℓ f) : Prop :=
  ∀ x : adjointGroup .E8 K, orderOf x = 5 → ∃ c : adjointGroup .E8 K,
    F.g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))

@[expose] def Phi4FiveToral : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ), 1 ≤ f → Nat.card K = 2 ^ f →
    5 ∣ Nat.card K * Nat.card K + 1 →
    ∀ (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2],
      ∃ F : E8P4Frame0 K L 2 f, E8FiveToral F

end CFSG.RankThree.PartOne.KE8F
