module

public import CFSG.RankThree.GF2n.Stroth80.Sec11BCent
public import CFSG.RankThree.GF2n.Stroth80.Sec11Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

theorem stroth117_of_115 (h115 : Stroth115Statement) (hex : Stroth117ExclStatement) :
    Stroth117Statement := by
  intro G _ _ M Q Z B _ hc n hw hn ha
  obtain ⟨t, m, x, htF, htT, hadm, hLie⟩ := h115 G M Q Z B hc n hw hn ha
  by_cases hexc : ExcludedByElevenSeven (XbarMod M Q Z B)
  · exact absurd hexc (hex G M Q Z B hc n hw hn ha)
  · cases t with
    | PSL => exact Or.inl ⟨m, x, hLie⟩
    | PSp => exact Or.inr (Or.inl ⟨m, x, hLie⟩)
    | POmegaPlus => exact Or.inr (Or.inr ⟨m, x, Or.inl hLie⟩)
    | POmegaMinus => exact Or.inr (Or.inr ⟨m, x, Or.inr (Or.inl hLie)⟩)
    | PSU =>
      have h3 : 3 ≤ m := hadm.2.2.1
      have hm4 : m = 4 := by
        by_contra h4
        refine hexc ⟨.PSU, m, x, ?_, hLie⟩
        iterate 8 right
        exact ⟨rfl, by omega⟩
      subst hm4
      exact Or.inr (Or.inr ⟨4, x, Or.inr (Or.inr (Or.inr hLie))⟩)
    | POmegaOdd => exact absurd rfl hadm.2.2.2
    | G2 => exact absurd ⟨.G2, m, x, by simp, hLie⟩ hexc
    | F4 => exact absurd ⟨.F4, m, x, by simp, hLie⟩ hexc
    | E6 => exact absurd ⟨.E6, m, x, by simp, hLie⟩ hexc
    | E7 => exact absurd ⟨.E7, m, x, by simp, hLie⟩ hexc
    | E8 => exact absurd ⟨.E8, m, x, by simp, hLie⟩ hexc
    | twistedE6 => exact absurd ⟨.twistedE6, m, x, by simp, hLie⟩ hexc
    | trialityD4 => exact absurd ⟨.trialityD4, m, x, by simp, hLie⟩ hexc
    | twistedB2 => exact absurd ⟨.twistedB2, m, x, by simp, hLie⟩ hexc
    | twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
    | twistedF4 => exact absurd rfl htF
    | Tits => exact absurd rfl htT

theorem stroth1111_of_117_1110
    (h117 : Stroth117Statement) (h118 : Stroth118Statement) (h119 : Stroth119Statement)
    (h1110 : Stroth1110Statement) : Stroth1111Statement := by
  intro G _ _ M Q Z B hc n hw hn ha
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have hL : IsLmChar2 (XbarMod M Q Z B) := by
    rcases h117 G M Q Z B hc n hw hn ha with hl | hsp | hom
    · exact hl
    · exact absurd hsp (h118 G M Q Z B hc n hw hn ha)
    · obtain ⟨y, -, hy⟩ := h119 G M Q Z B hc n hw hn ha hom
      exact ⟨4, y, hy⟩
  obtain ⟨-, hcore⟩ := h1110 G M Q Z B hc n hw hn ha hL
  exact caseVI_of_core hc hw hn hcore

theorem stroth1111_of_115 (h115 : Stroth115Statement)
    (hex : Stroth117ExclStatement) (h118 : Stroth118Statement) (h119 : Stroth119Statement)
    (h1110 : Stroth1110Statement) : Stroth1111Statement :=
  stroth1111_of_117_1110 (stroth117_of_115 h115 hex) h118 h119 h1110

end CFSG.RankThree.GF2n.Stroth80
