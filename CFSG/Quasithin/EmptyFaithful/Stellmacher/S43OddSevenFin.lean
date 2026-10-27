module

public import CFSG.Quasithin.EmptyFaithful.SzF53MTab

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.F53Mod Equiv

namespace F53.Stellmacher.S43

namespace Odd

namespace Seven

theorem that_eq_of_ne : ∀ a ∈ S5ThatF, ∀ σ ∈ S5ThatF, ∀ b ∈ S5ThatF, a ≠ 1 → σ ≠ 1 →
    σ ≠ a → b = 1 ∨ b = a ∨ b = σ ∨ b = a * σ := by
  decide +kernel

theorem that_swap_or_swap : ∀ a ∈ S5ThatF, ∀ b ∈ S5ThatF, a ≠ 1 → b ≠ 1 → b ≠ a →
    (b ≠ 1 ∧ b ^ 2 = 1 ∧ Perm.sign b ≠ 1 ∧ b ≠ a) ∨
      (b * a ≠ 1 ∧ (b * a) ^ 2 = 1 ∧ Perm.sign (b * a) ≠ 1 ∧ b * a ≠ a) := by
  decide +kernel

theorem that_act_comm : ∀ a ∈ S5ThatF, ∀ ξ ∈ S5ThatF, ∀ σ ∈ S5ThatF,
    (σ = 1 ∨ σ = a ∨ σ = ξ ∨ σ = a * ξ) → ∀ w : orth.W, orth.act ξ w = w →
      orth.act σ w * w⁻¹ = 1 ∨ orth.act σ w * w⁻¹ = orth.act a w * w⁻¹ := by
  decide +kernel

end Seven

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
