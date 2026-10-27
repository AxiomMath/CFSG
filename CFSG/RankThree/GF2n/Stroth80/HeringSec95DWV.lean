module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DEnd
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

@[expose] def Step95WVMinStatementFrom (n0 : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G)
    (Z0 : Subgroup G), HS9.Cfg95 hc n t Z0 → n0 ≤ n → HS9.One95 hc t Z0 →
      ∀ z : G, HS9.ZPair95 hc t Z0 z → HS9.Three95 hc t z → HS9.Five95 hc t z →
        ∃ x ∈ conjSubgroup z (HS9.N1 hc t), x ∉ hc.CN t ∧
          ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t

theorem step95Core_of_wvMin (h34 : Stroth34Statement) (h91b : Stroth91bStatement)
    (hA : Sec9AExistsStatement) (hN6 : Sec95N6Statement) (hCentre : Step95CentreStatementFrom 7)
    (h0 : Step95ChoiceStatementFrom 7) (h1 : Step95OneStatementFrom 7)
    (hwv : Step95WVMinStatementFrom 7) : Step95CoreStatement := by
  intro G _ _ M Q Z B hc n t hs hn Z0 hZ0 hbad hnsc
  by_cases h7 : 7 ≤ n
  · have cfg : HS9.Cfg95 hc n t Z0 :=
      ⟨hs, hn, hZ0, hbad, hnsc, hCentre G M Q Z B hc n t hs h7 Z0 hZ0⟩
    obtain ⟨z, hz⟩ := h0 G M Q Z B hc n t Z0 cfg h7
    have c1 := h1 G M Q Z B hc n t Z0 cfg h7
    have c3 := three95_noTwo h34 h91b hA G M Q Z B hc n t Z0 cfg h7 c1 z hz
    have c5 := five95_noTwo h34 h91b hA G M Q Z B hc n t Z0 cfg h7 z hz c3
    obtain ⟨x, hxz, hxN, hxW⟩ := hwv G M Q Z B hc n t Z0 cfg h7 c1 z hz c3 c5
    have hx : x ∈ conjSubgroup z (LB M Q B) := by
      rw [mem_conjSubgroup] at hxz ⊢
      exact (Subgroup.mem_inf.mp hxz).1
    rw [hz.normL] at hx
    exact ⟨x, hx, hxN, hxW⟩
  · by_cases h6' : n = 6
    · exact hN6 G M Q Z B hc n t hs h6'
    · exact (sec95Excluded_seven G M Q Z B hc n t hs (by omega) (by omega)).elim

end CFSG.RankThree.GF2n.Stroth80
