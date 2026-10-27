module

public import CFSG.RankThree.PartOne.SEITZ7.SzPair

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZ12

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG.RankThree.PartOne.SEITZ7

set_option linter.unusedSectionVars false

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

variable (K) in
@[expose] def phi4Plane (a₀ : ModGL F4.tag K) : Subgroup (ModGL F4.tag K) :=
  Subgroup.zpowers a₀ ⊔ Subgroup.zpowers (szNw K * a₀ * (szNw K)⁻¹)

variable (m) (K) in
@[expose] def phi4D (a₀ : ModGL F4.tag K) : Subgroup (ModGL F4.tag K) :=
  Subgroup.closure {k | k ∈ F4.reeGamma K m ∧
    ∃ x ∈ phi4Plane K a₀, x ≠ 1 ∧ k * x = x * k}

variable (m) (K) in
@[expose] def Phi4Ambient : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ (2 ^ (2 * m + 1)) ^ 2 + 1 →
    ∀ a₀ ∈ rankOneGroupTwo K m, orderOf a₀ = p → phi4D m K a₀ = F4.reeGamma K m

end CFSG.RankThree.PartOne.SEITZ12
