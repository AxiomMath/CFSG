module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModG2
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldChevalleyOdd

import CFSG.Quasithin.Recognition.GoldschmidtF112RY9

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.QuasithinUnique.Setup.X6


noncomputable abbrev g2ParA (K : Type) [Field K] : Subgroup ↥(adjointGroup Tag.G2 K) :=
  (parabolicSubgroup Tag.G2 K {g2Index 1}).subgroupOf (adjointGroup Tag.G2 K)

noncomputable abbrev g2ParB (K : Type) [Field K] : Subgroup ↥(adjointGroup Tag.G2 K) :=
  (parabolicSubgroup Tag.G2 K {g2Index 0}).subgroupOf (adjointGroup Tag.G2 K)


variable {K : Type} [Field K] [Finite K]

theorem isLieOverTwo_g2 {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    IsLieOverTwo .G2 0 f ↥(adjointGroup Tag.G2 K) := by
  refine Or.inr (Or.inl ⟨rfl, by decide, ?_⟩)
  refine ⟨⟨Nat.prime_two, by omega, rfl, ?_⟩,
    CFSG.SignalizerFunctorTheorem.CatalogBridge.untwistedChevalleyModel_adjointGroup
      (τ := .G2) (K := K) hK⟩
  calc 3 ≤ 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

variable
  [CharP K 2]

theorem isYAmalgamPair_g2 {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    IsYAmalgamPair (posUnipotentSub Tag.G2 K) (g2ParA K) (g2ParB K) :=
  isYAmalgamPair_swap (H13.Sec53F.G2.g2_yamStd hK hf).isYAmalgamPair

end CFSG.Quasithin.F112R.St84

end
