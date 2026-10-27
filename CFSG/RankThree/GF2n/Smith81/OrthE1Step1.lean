module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps

public section

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80


theorem step1_of (h34 : Stroth34Statement) (hN : E1NaturalStatement)
    (hKF1 : ParabolicStatement) : Step1Statement := by
  intro G _ _ M Q Z B t hH AM
  have hc : Ctx M Q Z B := hH.ctx
  have hsec : Sec5Hyp hc 4 t := hH.sec
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hKZ : Nat.card AM.K = Nat.card Z := AM.glob.card
  have hK1 : 1 < Nat.card AM.K := by omega
  have hq2 : 2 ≤ Nat.card Z := by omega
  have hZpos : 0 < Nat.card Z := by omega
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hE8 : Module.finrank AM.K AM.M₀.E = 8 := by
    have h := AM.glob.finrank_E hsec.width hK1
    omega
  have hhyp : AM.S.IsHyp := AM.glob.hyperbolic
  have h35 := (stroth_3_5 h34 hc hsec.width hsec.n_gt hsec.noA2 hsec.gen).2.1
  have hel := hc.Vt_isElemAbelian h35 hsec.mem hsec.notQ
  have hTS : AM.S.IsTS (AM.Vsp hc t) := fun e he =>
    (AM.M₀.isElemAbelian_iff AM.glob.reg hVQ).mp hel e (mem_imgSub.mp he)
  have hNat : Nat.card (Vt M (LB M Q B) B Z t) = Nat.card Z * Nat.card Z ^ 4 := by
    obtain ⟨hP, hMi⟩ := hN G M Q Z B t hH
    obtain ⟨h9, hNt, hPM⟩ := hH.case
    rcases hPM with hPM | hPM
    · obtain ⟨_, _, _, hK', hnat⟩ :=
        hP (by unfold CaseE1Plus; exact ⟨h9, hNt, hPM⟩)
      have h := card_of_naturalRep hnat sec39_Z_le_Vt hK'
      simpa using h
    · obtain ⟨_, _, _, hK', _, _, _, hnat⟩ :=
        hMi (by unfold CaseE1Minus; exact ⟨h9, hNt, hPM⟩)
      have h := card_of_naturalRep hnat sec39_Z_le_Vt hK'
      simpa using h
  have himg : Nat.card (AM.M₀.img (Vt M (LB M Q B) B Z t)) = Nat.card Z ^ 4 := by
    have h1 := AM.M₀.card_eq hVQ hZV
    rw [hNat] at h1
    exact (Nat.eq_of_mul_eq_mul_left hZpos h1).symm
  have hVsp : Nat.card (AM.Vsp hc t) = Nat.card Z ^ 4 := by
    rw [← himg]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_imgSub)
  have hfin : Module.finrank AM.K (AM.Vsp hc t) = 4 := by
    have h : Nat.card (AM.Vsp hc t) =
        Nat.card AM.K ^ Module.finrank AM.K (AM.Vsp hc t) := Module.natCard_eq_pow_finrank
    rw [hVsp, hKZ] at h
    exact Nat.pow_right_injective hq2 h.symm
  exact ⟨hE8, hhyp, hTS, hfin⟩

end CFSG.RankThree.GF2n.Smith81.Smith23E1
