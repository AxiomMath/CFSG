
module

public import Certificates.Data.CFSGNative.ExcCensus.InLCommon
public import CFSG.LocalAnalysis.StandardType.GGQ2CensusFrameAut
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusMain
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtExcLine
public import CFSG.LocalAnalysis.StandardType.GGQ2InLLeafExcVacuous

@[expose] public section

namespace CFSG.StandardType.GGQ2Frame

namespace ExcRaw

variable {m : Fin 6} {T : Chk.Tabs}

theorem inLCommonCasesVx_of_scanLineN (hT : Chk.tabsOK m T = true) {X : Chk.ICSearch} {vx : V m}
    (h : Chk.scanLineN T m false true X.S (Chk.bodyIC T m X) (code m vx) = true) :
    InLCommonCasesVx (excRaw m) vx := by
  intro hvx ℓ hℓ hq hocc hcent hin U hU hxU j hj hjocc hjcent _ _
  have hL : LineHyp m false true vx ℓ :=
    ⟨hvx, hℓ, fun _ => hq, hocc, hcent, iff_of_true hin rfl⟩
  have hP : PlaneHyp m U j := ⟨hj, hjocc, hjcent⟩
  obtain ⟨cv, cy, hcv, -, rfl, hy, rfl, rfl, rfl, hbody⟩ := scanLineN_sound hT h hL hU hxU hP
  simp only [Chk.bodyIC] at hbody
  cases hX : X.common cv cy with
  | none => simp [hX] at hbody
  | some t =>
    obtain ⟨a, b, rows, B, W⟩ := t
    simp only [hX, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hbody
    obtain ⟨⟨⟨-, hb⟩, hc⟩, hW⟩ := hbody
    refine ⟨_, vec_combN_mem cv cy a b, ?_, _,
      candidate_of_candOK hT hcv hc hP (vec_combN_mem cv cy a b),
      commonWitness_of_commonOK hT hW⟩
    rw [vec_combN]
    exact comb_not_mem_span hy hb

end ExcRaw

theorem inLCommonCases_excRaw (m : Fin 6) (hm : m ≠ 4) : InLCommonCases (excRaw m) := by
  intro vx hvx ℓ _ _ hocc hcent hin
  exact (ExcRaw.noInternalAt_excRaw m hm hvx ℓ hocc hcent hin).elim

end CFSG.StandardType.GGQ2Frame

end
