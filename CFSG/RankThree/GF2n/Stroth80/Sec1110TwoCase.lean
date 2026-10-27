module

import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoFieldEq
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoTau
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec11BStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

theorem false_of_lieModel_psl_two [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x) : False := by
  have hx : 1 ≤ x := (hLm2.admissible).2.1
  have hcenter := hc.center_Xbar_eq_bot_of_lieModel_psl_two hLm2
  have hZ := card_Z_eq_two_pow_of_lieModel hc hw hn hLm2 hcenter
  obtain ⟨K, hKf, hKfin, -, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  exact false_of_xbar_psl_two hc hw hn hx hZ hLm2 hcenter hD

theorem stroth1110_of_lieModel_psl_two [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hLm2 : ∃ x : ℕ, CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x) :
    Xbar M Q Z B = bar M Q (Lgen M (LB M Q B)) ∧
      CaseVICore M Q Z (Lgen M (LB M Q B)) n := by
  obtain ⟨x, hx⟩ := hLm2
  exact (false_of_lieModel_psl_two hc hw hn hx).elim

theorem isLmChar2_cases {Y : Type} [Group Y] (h : IsLmChar2 Y) :
    (∃ x : ℕ, CFSG.Blueprint.LieModel Y .PSL 2 2 x) ∨
      ∃ m x : ℕ, 3 ≤ m ∧ CFSG.Blueprint.LieModel Y .PSL m 2 x := by
  obtain ⟨m, x, hLm⟩ := h
  have hm : 2 ≤ m := (hLm.admissible).2.2.1
  rcases eq_or_lt_of_le hm with h2 | h3
  · subst h2
    exact Or.inl ⟨x, hLm⟩
  · exact Or.inr ⟨m, x, h3, hLm⟩

end CFSG.RankThree.GF2n.Stroth80
