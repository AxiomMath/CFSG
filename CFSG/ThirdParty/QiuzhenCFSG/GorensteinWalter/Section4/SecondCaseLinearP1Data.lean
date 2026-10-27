module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearP0LeConjugateCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearP1UpperBound
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearLineCard
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The complete equation-(11) line parameter
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The source's `p₁` package: the number of ambient conjugates of `P` in
`A`, its two elementary bounds, and the exact number of non-`P` lines. -/
public theorem secondCase_linear_p1_data
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseLinearOmegaData c w d)
    (p0 : ℕ)
    (hp0 : p0 = (normalizerIn c.U od.P).relIndex (normalizerIn c.U od.A)) :
    ∃ p1 : ℕ,
      p1 = conjugateCount od.P od.A ∧
      p0 ≤ p1 ∧
      p1 ≤ od.p + 1 ∧
      Nat.card (secondCase_linesIn G od.P od.P0) = p1 - 1 := by
  classical
  let : Fact od.p.Prime := ⟨od.hp_prime⟩
  let p1 : ℕ := conjugateCount od.P od.A
  have hp01 : p0 ≤ p1 := by
    dsimp [p1]
    rw [hp0]
    exact secondCase_linear_p0_le_conjugateCount c w d od
  have hp1p : p1 ≤ od.p + 1 := by
    dsimp [p1]
    exact secondCase_linear_conjugateCount_le_p_add_one
      od.P_card od.A_card od.A_elem_abelian
  have hlines : Nat.card (secondCase_linesIn G od.P od.P0) = p1 - 1 := by
    apply secondCase_linearEquation11_line_card
      (P := od.P) (P0 := od.P0) (A := od.A) (p1 := p1)
    · exact od.A_eq
    · rw [od.A_eq]
      exact le_sup_left
    · rfl
  exact ⟨p1, rfl, hp01, hp1p, hlines⟩

end CFSG.GorensteinWalter
