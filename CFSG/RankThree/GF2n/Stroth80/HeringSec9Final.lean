module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec9Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem stroth95_of_n5_core (h92 : Stroth92Statement) (h93 : Stroth93Statement)
    (hConjV : Step94ConjVStatement) (hn5 : Sec9NGeFiveStatement) (hN5 : Sec95N5Statement)
    (hcore : Step95CoreStatement) : Stroth95Statement := by
  intro G _ _ M Q Z B hc n t hs
  have hx : ∃ x ∈ LB M Q B, x ∉ hc.CN t ∧
      ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t := by
    by_cases h6 : 6 ≤ n
    · obtain ⟨Z0, hZ0⟩ := exists_isCentrePre (Q := Q) (hc.Q_le_Rt hs.mem)
      by_cases hbad : ∀ s ∈ Z0, ∀ g ∈ M, g * s * g⁻¹ ∈ LB M Q B → g * s * g⁻¹ ∈ hc.CN t
      · have hns : ¬ StronglyClosedMod M Z0 (LB M Q B) := h93 G M Q Z B hc n t hs Z0 hZ0
        unfold StronglyClosedMod at hns
        push Not at hns
        obtain ⟨s, hs0, g, hg, hL, hZ⟩ := hns
        exact hcore G M Q Z B hc n t hs h6 Z0 hZ0 hbad ⟨s, hs0, g, hg, hL, hZ⟩
      · push Not at hbad
        obtain ⟨s, hs0, g, hg, hL, hN⟩ := hbad
        have hxM : g * s * g⁻¹ ∈ M := hc.LB_le_M hL
        have hconj : ConjMod M Q s (g * s * g⁻¹) := ⟨hxM, g, hg, by simp [Q.one_mem]⟩
        exact ⟨g * s * g⁻¹, hL, hN,
          hConjV G M Q Z B hc n t hs _ _ rfl rfl Z0 hZ0 s hs0 _ hL hN hconj⟩
    · have h5 : 5 ≤ n := hn5 G M Q Z B hc n t hs
      exact hN5 G M Q Z B hc n t hs (by omega)
  obtain ⟨x, hxL, hxN, hxW⟩ := hx
  obtain ⟨hY, hcomm⟩ := h92 G M Q Z B hc n t hs _ _ rfl rfl x hxL hxN hxW
  obtain ⟨Y, hdp, hq⟩ := hY
  exact ⟨Sec9R0 hc t x, Y, hdp, hq, hcomm⟩

end CFSG.RankThree.GF2n.Stroth80
