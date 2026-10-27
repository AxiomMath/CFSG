module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110CMLmConsumer

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

theorem caseVICore_of_CMLmChain_three [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {n x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hC : CMLmChain) (h3 : CMLmThree)
    (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 3 2 x) :
    Xbar M Q Z B = bar M Q (Lgen M (LB M Q B)) ∧
      CaseVICore M Q Z (Lgen M (LB M Q B)) n := by
  have hx : 2 ^ x = Nat.card Z := by
    rcases hC G M Q Z B hc n 3 x hw hn ha2 hLm (le_refl 3) with
      ⟨X₁, X₂, X₃, X₄, hX₁, h₁₂, h₂₃, h₃₄, hX₄Q, -, -, -, -,
        K', hK'f, hK'fin, hK'card, nat2, -⟩ | ⟨h34, -⟩
    · letI : Field K' := hK'f
      letI : Finite K' := hK'fin
      have hX₂Q : X₂ ≤ Q := by rw [← hX₄Q]; exact h₂₃.trans h₃₄
      exact two_pow_eq_card_Z_of_naturalRep (K := K') hc (m := 3) (by norm_num)
        hX₁ hX₂Q nat2 hLm hK'card
    · omega
  exact caseVICore_of_CMLmChain (m := 3) hc hw hn ha2 hC hLm (le_refl 3)
    (h3 G M Q Z B hc n x hw hn ha2 hLm hx)

theorem stroth1110_core_of_inputs [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {n m x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hC : CMLmChain) (h3 : CMLmThree)
    (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL m 2 x) (hm : 3 ≤ m)
    (hLgen : Lgen M (LB M Q B) ≤ XbarPre M Q Z B) :
    Xbar M Q Z B = bar M Q (Lgen M (LB M Q B)) ∧
      CaseVICore M Q Z (Lgen M (LB M Q B)) n := by
  rcases eq_or_lt_of_le hm with h3m | hm4
  · subst h3m
    exact caseVICore_of_CMLmChain_three hc hw hn ha2 hC h3 hLm
  · exact caseVICore_of_CMLmChain hc hw hn ha2 hC hLm hm hLgen

theorem stroth1110_of_inputs_m_ge_three [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hC : CMLmChain) (h3 : CMLmThree)
    (hLm3 : ∃ m x : ℕ, 3 ≤ m ∧
      CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL m 2 x)
    (hLgen : ∀ (m x : ℕ), 4 ≤ m →
      CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL m 2 x →
      Lgen M (LB M Q B) ≤ XbarPre M Q Z B) :
    Xbar M Q Z B = bar M Q (Lgen M (LB M Q B)) ∧
      CaseVICore M Q Z (Lgen M (LB M Q B)) n := by
  obtain ⟨m, x, hm, hLm⟩ := hLm3
  rcases eq_or_lt_of_le hm with h3m | hm4
  · subst h3m
    exact caseVICore_of_CMLmChain_three hc hw hn ha2 hC h3 hLm
  · exact stroth1110_core_of_inputs hc hw hn ha2 hC h3 hLm hm
      (hLgen m x (by omega) hLm)

end CFSG.RankThree.GF2n.Stroth80
