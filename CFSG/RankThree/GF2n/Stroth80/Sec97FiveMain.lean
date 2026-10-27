module

public import CFSG.RankThree.GF2n.Stroth80.Sec97FivePoint
import CFSG.RankThree.GF2n.Stroth80.Sec97FiveTrans
import CFSG.RankThree.GF2n.Stroth80.Sec97FiveK13
import CFSG.RankThree.GF2n.Stroth80.Sec97FiveK5
import CFSG.RankThree.GF2n.Stroth80.Sec97FiveCore
import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreX
public import CFSG.RankThree.GF2n.Stroth80.Sec9NComm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem sec97Five_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (hm : Sec9CentreMprStatement) : Sec97FiveStatement := by
  intro G _ _ M Q Z B hc n t hs X Y hsplit h4 h1 r hr Z0 hZ0 s hs0 nn hsn hnn hnZ
  have hcen : HS9.Centre95 hc t Z0 :=
    step95Centre_of h34 h311a h311bComm h311bCard G M Q Z B hc n t hs Z0 hZ0
  have hVn : Sec97VnStatement := sec97Vn_of_centreMpr h34 hm
  obtain ⟨g₀, hg₀, hq, -, hVg₀, -⟩ :=
    HS9.five_transport h34 h311a hc hs hsplit h1 hr hZ0 hcen hs0 hsn hnn hnZ
  set q : G := nn * (g₀ * s * g₀⁻¹)⁻¹ with hqdef
  have hsQ : s ∉ Q := by
    intro hsQ
    have hgsQ : g₀ * s * g₀⁻¹ ∈ Q := by
      have hmem : g₀ * s * g₀⁻¹ ∈ conjSubgroup g₀ Q := by
        rw [mem_conjSubgroup]
        have e : g₀⁻¹ * (g₀ * s * g₀⁻¹) * g₀ = s := by group
        rwa [e]
      rwa [hc.conj_Q_eq hg₀] at hmem
    have hnnQ : nn ∈ Q := by
      have e : nn = q * (g₀ * s * g₀⁻¹) := by rw [hqdef]; group
      rw [e]
      exact Q.mul_mem hq hgsQ
    exact hnZ (hc.Q_le_centre hs.toSec5.mem hZ0 hnnQ)
  have hvanish : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅g₀ * s * g₀⁻¹, v⁆ ∈ Z := by
    intro v hv
    have hvQ : v ∈ Q := hc.Vt_le_Q t hv
    have hnvZ : ⁅nn, v⁆ ∈ Z := (Ctx.mem_CN.mp hnn.2).2 v hv
    have hqM : q ∈ M := hc.Rt_le_M t (hc.Q_le_Rt hs.toSec5.mem hq)
    have hmid : q⁻¹ * ⁅nn, v⁆ * q ∈ Z := by
      have h := (Subgroup.mem_normalizer_iff.mp
        (hc.hyp.Z_normal.2 (M.inv_mem hqM)) ⁅nn, v⁆).mp hnvZ
      simpa only [inv_inv] using h
    have hqinvZ : ⁅q⁻¹, v⁆ ∈ Z :=
      Smith81.comm_mem_Z hc.hyp (Q.inv_mem hq) hvQ
    have he : g₀ * s * g₀⁻¹ = q⁻¹ * nn := by rw [hqdef]; group
    rw [he, commutatorElement_mul_left_eq_conj_mul, inv_inv]
    exact Z.mul_mem hmid hqinvZ
  have hV : Vt M (LB M Q B) B Z nn ≤ Wt Q (Vt M (LB M Q B) B Z t) := by
    rw [← hVg₀]
    exact HS9.conj_Vt_le_Wt_of_vanish hc hcen hs0 hsQ hg₀ hvanish
  have h91b : Stroth91bStatement :=
    stroth91b_of_steps h34 h311a (sec9NComm_of_311b h34 h311bComm)
      (step91OrderQB_of h34) (step91OrderVQB_of h34) (step91Inter_of h34)
      (step91MixedComm_of h34)
  obtain ⟨g, h13, hYg, hpt⟩ :=
    HS9.sec97K13_of h34 h311a hc hs hsplit h4 h1 hr hZ0 hcen hVn hs0 hsn hnn hnZ
  have hK5 := HS9.sec97K5_of_K13 h34 h91b hc hs hsplit h4 hr h13 hV
  exact HS9.fiveConcl_of_core hc
    (HS9.fiveCore_of_line h34 h311a hc hs hsplit h4 hK5 inf_le_right h13.g_mem hYg hpt)

end CFSG.RankThree.GF2n.Stroth80
