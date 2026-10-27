module

public import CFSG.RankThree.GF2n.Stroth80.Sec108RhoLB
public import CFSG.RankThree.GF2n.Stroth80.Sec108Mu
public import CFSG.RankThree.GF2n.Stroth80.Sec108TKer

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement
open Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

theorem Sec108Data.exists_levi108 [(Q.subgroupOf M).Normal] (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    ∃ (ρ : ↥(bar M Q (Rt M (LB M Q B) t)) →* GL (Fin 3) AM.K)
      (μ : ↥(bar M Q (hc.CN t)) →* Multiplicative (Fin 3 → AM.K))
      (T : ↥(Sec108.NLY (bar M Q (LB M Q B)) (bar M Q Y)) →* AddMonoid.End (Fin 3 → AM.K)),
      Sec108.Levi108 AM.K (bar M Q (LB M Q B)) (bar M Q (Rt M (LB M Q B) t))
        (bar M Q (hc.CN t)) (bar M Q Y) ρ μ T := by
  have ht : t ∈ LB M Q B := D.good.1.mem_LB
  have hLR : bar M Q (LB M Q B) ≤ bar M Q (Rt M (LB M Q B) t) := hc.bar_LB_le_bar_Rt ht
  have hNR : bar M Q (hc.CN t) ≤ bar M Q (Rt M (LB M Q B) t) := hc.bar_CN_le_bar_Rt t
  refine ⟨D.rho AM, D.mu AM, D.semiT AM, ?_⟩
  exact
    { four_le_card := Ctx.four_le_card_K hc AM
      elemAb_L := hc.isElemAbelian_bar_LB
      elemAb_N := D.isElemAbelian_bar_CN
      L_le_R := hLR
      N_le_R := hNR
      Y_le_N := Subgroup.map_mono (Subgroup.subgroupOf_mono M D.root_le_CN)
      Y_le_centralizer := D.bar_root_le_centralizer
      range_rho := D.range_rho AM
      ker_rho := D.ker_rho AM
      rho_L := D.rho_LB AM
      exists_L := D.exists_LB_rho AM
      mem_normalizer_iff := D.mem_normalizer_bar_LB_iff AM
      surjective_mu := D.surjective_mu AM
      ker_mu := D.ker_mu AM
      mu_conj := D.mu_conj AM
      mem_L_iff_mu := D.mem_bar_LB_iff_mu AM
      normalizer_Y_le := D.normalizer_bar_root_le
      normalizer_inf_le := D.normalizer_bar_inf_le
      T_semilinear := D.semiT_semilinear AM
      T_line := D.semiT_line AM
      T_rho := D.semiT_rho AM
      T_ker_comm := D.semiT_ker_comm AM
      T_ker_two := D.semiT_ker_two AM }

end CFSG.RankThree.GF2n.Stroth80
