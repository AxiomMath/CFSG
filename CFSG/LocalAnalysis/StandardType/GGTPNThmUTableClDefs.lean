module

public import CFSG.LocalAnalysis.StandardType.GGMultTableCl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTPNPRankOne (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ lab.rank = 1) ∨ (lab.tag = .twD ∧ lab.rank = 2) ∨
    (lab.tag = .A ∧ lab.rank = 2 ∧ p ∣ 2 ^ lab.n + 1) ∨
    (lab.tag = .twA ∧ lab.rank = 2 ∧ p ∣ 2 ^ lab.n - 1)

theorem ggMultOrd_ne_zero_of_mem_ggMultTableCl {T : GGKacTypeCl} {tw : Bool} {p n : ℕ}
    {D : GGKacDatum} (hD : D ∈ ggMultTableCl T tw p n) : ggMultOrd p n ≠ 0 := by
  intro h
  cases T <;> simp [ggMultTableCl, h] at hD

end CFSG.StandardType

end
