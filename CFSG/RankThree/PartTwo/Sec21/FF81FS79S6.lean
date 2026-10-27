module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Std

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open Equiv

namespace J6

theorem normalizes_Efin_of_conj_line : ∀ x ∈ Efin, x ≠ 1 → ∀ n : S6,
    (n * x * n⁻¹ = x ∨ n * x * n⁻¹ = x⁻¹) → ∀ e ∈ Efin, n * e * n⁻¹ ∈ Efin := by
  decide +kernel

theorem mem_Efin_of_cen : ∀ n : S6, n * c₁ = c₁ * n → n * c₂ = c₂ * n → n ∈ Efin := by
  decide +kernel

end J6

end CFSG.RankThree.PartTwo.Sec21.FF81
