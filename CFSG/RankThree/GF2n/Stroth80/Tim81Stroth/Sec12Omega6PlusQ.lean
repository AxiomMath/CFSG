module

public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Sec12Omega6PlusStepBRed
import CFSG.RankThree.GF2n.Stroth80.Sec7TailRecogGroup
import CFSG.RankThree.GF2n.Smith81.Sec217Perfect
public import CFSG.RankThree.GF2n.Stroth80.Sec12Omega6PlusCaseE6

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem sec12Omega6PlusQStatement_of_zcard
    (hZcard : Sec7ZCardStatement) : Sec12Omega6PlusQStatement := by
  intro G _ _ M Q Z B _ _ hc n h12 t ht htQ hp hsub
  obtain ⟨⟨hN', H₂⟩, hN'', hall⟩ := hsub
  haveI := hN'
  have h5 : Sec5Hyp hc n t := h12.toSec5 ht htQ
  have hlarge := h12.large t ht htQ
  have hnot : ¬ OmegaPlusNat hc t 2 := not_omegaPlusNat_two_of (m := 3) le_rfl (Or.inl hp)
  have hs : Sec7Hyp hc n t := ⟨h5, hnot, ⟨3, by norm_num, Or.inl hp⟩, hlarge⟩
  obtain ⟨Z0, hZ0⟩ := hc.exists_centre ht
  have hZN := sec7ctr_Z0_le_CN hc hs hZ0
  have hZc := hZcard G M Q Z B hc n t hs Z0 hZ0
  have hQN : Q ≤ hc.CN t := sec8_Q_le_CN hc ht
  have hCNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hRH0 : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hZ0H0 : Z0 ≤ H0 M Z := hZ0.le.trans hRH0
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hbarZ := bar_card_mul_card_of_le (M := H0 M Z) hQZ0 hZ0H0
  have hbarZq : Nat.card (bar (H0 M Z) Q Z0) = Nat.card Z := by
    rw [hZc] at hbarZ
    exact Nat.eq_of_mul_eq_mul_right hQpos (by rw [hbarZ]; ring)
  have hNR : bar (H0 M Z) Q (hc.CN t) ≤ bar (H0 M Z) Q (Rt M (LB M Q B) t) :=
    Subgroup.map_mono (fun a ha => hCNR ha)
  have hRM : bar (H0 M Z) Q (Rt M (LB M Q B) t) ≤
      Subgroup.normalizer ((cen (bar (H0 M Z) Q (hc.CN t)) : Subgroup _) : Set _) := by
    rintro _ ⟨r, hr, rfl⟩
    have hrR : (r : G) ∈ Rt M (LB M Q B) t := Subgroup.mem_subgroupOf.mp hr
    have hrN : (r : G) ∈ Subgroup.normalizer ((hc.CN t : Subgroup G) : Set G) :=
      Subgroup.mem_normalizer_fintype fun x hx => hc.CN_conj_mem ht hrR hx
    exact mem_normalizer_cen_of_mem_normalizer _
      (mk_mem_normalizer_bar_of_normalizer (M := H0 M Z) hQN r hrN)
  obtain ⟨hnR, hRq⟩ : QuotSat (bar (H0 M Z) Q (Rt M (LB M Q B) t))
      (bar (H0 M Z) Q (hc.CN t)) (IsOmegaPlus 3 (Nat.card Z)) :=
    quotSat_bar_of (fun X Y _ _ e h => IsOmegaPlus.congr e h) hQN hCNR hRH0 hp.quotSat
  haveI := hnR
  obtain ⟨r0, -, hr0, -⟩ := hc.hyp.cp
  have hqa : ∃ a : ℕ, 2 ≤ a ∧ Nat.card Z = 2 ^ a := by
    refine ⟨r0, ?_, hr0⟩
    by_contra hlt
    have h4 := hc.hyp.q4
    rw [hr0] at h4
    interval_cases r0 <;> simp at h4
  obtain ⟨hRs, hRn, -⟩ := isOmegaPlus_three_facts hqa hRq
  haveI := hRs
  have hnc : ¬ IsMulCommutative (↥(bar (H0 M Z) Q (Rt M (LB M Q B) t)) ⧸
      (bar (H0 M Z) Q (hc.CN t)).subgroupOf (bar (H0 M Z) Q (Rt M (LB M Q B) t))) := fun h => by
    obtain ⟨x, y, hxy⟩ := hRn
    exact hxy (h.is_comm.comm x y)
  have hperfRN := (TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnc).commutator_eq_top
  obtain ⟨E, hER, hEperf, hEN, -⟩ := exists_perfect_sup_eq hNR hperfRN
  have hEc := Smith81.perfect_centralizes_of_semilinAct (Smith81.semilinAct_Z H₂)
    (P := E) (hER.trans hRM) (Group.isPerfect_def.mpr hEperf)
  have hRC : bar (H0 M Z) Q (Rt M (LB M Q B) t) ≤
      Subgroup.centralizer ((cen (bar (H0 M Z) Q (hc.CN t)) : Subgroup _) : Set _) := by
    rw [← hEN]
    refine sup_le (fun p hp => Subgroup.mem_centralizer_iff.mpr fun y hy => (hEc p hp y hy).symm)
      (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    have hy' : y ∈ cen (bar (H0 M Z) Q (hc.CN t)) := hy
    rw [cen_eq] at hy'
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy').2 x hx).symm
  have hcen : cen (bar (H0 M Z) Q (hc.CN t)) = bar (H0 M Z) Q Z0 := by
    refine le_antisymm (fun y hy => ?_) (bar_centre_le_cen hc hZ0 hZN)
    have hyN : y ∈ bar (H0 M Z) Q (hc.CN t) := by
      have hy' : y ∈ cen (bar (H0 M Z) Q (hc.CN t)) := hy
      rw [cen_eq] at hy'
      exact (Subgroup.mem_inf.mp hy').1
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hyN
    have hxC : (x : G) ∈ hc.CN t := Subgroup.mem_subgroupOf.mp hx
    refine Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ((hZ0 x).mpr
      ⟨hCNR hxC, fun r hr => ?_⟩))
    have hrH : r ∈ H0 M Z := hRH0 hr
    have hrb : QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨r, hrH⟩ ∈
        bar (H0 M Z) Q (Rt M (LB M Q B) t) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hr)
    have h1 := Subgroup.mem_centralizer_iff.mp (hRC hrb) _ hy
    exact (mk_comm_iff (M := H0 M Z) x ⟨r, hrH⟩).mp h1
  rw [hcen]
  exact hbarZq

end CFSG.RankThree.GF2n.Stroth80
