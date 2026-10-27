module

public import CFSG.RankThree.GF2n.Smith81.LinTLLgen
public import CFSG.RankThree.GF2n.Smith81.LinTLMixedConj

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
  {M Q Z A B : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}

theorem LinSetup.Lgen_eq (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n)
    (hA : Ctx M Q Z A) : Lgen M (LB M Q A) = Lgen M (LB M Q B) := by
  rcases hS.conj_le_V hc hn hA with h | h
  · exact hS.Lgen_eq_of_le_V₁ hc hn hA h
  · exact hS.symm.Lgen_eq_of_le_V₁ hc hn hA h

theorem LinSetup.of_conj (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n)
    (hA : Ctx M Q Z A) : LinSetup M Q Z A n V₁ V₂ :=
  hS.of_conj_of_le hc hn hA (hS.conj_le_V hc hn hA)

theorem LinSetup.transv_of_conj (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n)
    (hA : Ctx M Q Z A) :
    (A ≤ V₁ ∨ A ≤ V₂) ∧ ∀ t ∈ LB M Q A, t ∉ Q →
      HasDimOn V₁ Z 1 t ∧ HasDimOn V₂ Z 1 t ∧ A ≤ ⁅Q, Subgroup.zpowers t⁆ ⊔ Z :=
  linTransvStatement_holds G M Q Z A n V₁ V₂ hA (hS.of_conj hc hn hA) hn

end CFSG.RankThree.GF2n.Smith81
