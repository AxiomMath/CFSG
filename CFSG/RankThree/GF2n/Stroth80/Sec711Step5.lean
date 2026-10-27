module

public import CFSG.RankThree.GF2n.Stroth80.Sec711Setup
public import CFSG.RankThree.GF2n.Stroth80.Sec78QB
public import CFSG.RankThree.GF2n.Stroth80.Sec78HypFrame
public import CFSG.RankThree.GF2n.Stroth80.Sec8RtConj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem n12Lemma5_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement) :
    N12Lemma5Statement := by
  intro G _ _ M Q Z B hc n t r hs hr
  have hrM : r ∈ M := hc.Rt_le_M t hr.mem
  have hs5 : t ∈ LB M Q B := hs.toSec5.mem
  have hRt : Rt M (LB M Q B) (r * t * r⁻¹) = Rt M (LB M Q B) t := by
    rw [← conjSubgroup_Rt_eq hrM t]
    exact conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hr.mem)
  have hVt : Vt M (LB M Q B) B Z (r * t * r⁻¹) = Vt M (LB M Q B) B Z t := by
    rw [← conjSubgroup_Vt_eq hrM (hc.conj_Z_eq hrM) t]
    exact conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt hs5 hr.mem)
  have hsL : r * t * r⁻¹ ∈ LB M Q (conjSubgroup r B) := by
    rw [hc.LB_conj hrM, mem_conjSubgroup, show r⁻¹ * (r * t * r⁻¹) * r = t by group]
    exact hs5
  have hsQ : r * t * r⁻¹ ∉ Q := fun hsQ =>
    hs.toSec5.notQ ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hrM) t).mpr hsQ)
  have hs' : Sec7Hyp (hc.conj_of_mem hrM) n (r * t * r⁻¹) :=
    sec7ctr_hyp_frame hc hs hrM hsL hsQ hRt hVt
  have hCN : (hc.conj_of_mem hrM).CN (r * t * r⁻¹) = hc.CN t :=
    (sec7ctr_CN_conj_frame hc hrM (r * t * r⁻¹)).trans (hc.CN_congr hRt hVt)
  refine ⟨fun a ha hx => ?_, fun a ha hy => ?_⟩
  · obtain ⟨haB, haW⟩ := Subgroup.mem_inf.mp ha
    have haQ : a ∈ Q := (Subgroup.mem_inf.mp haW).1
    have hcond : ∀ l ∈ (QB B ⊓ M) ⊓ hc.CN t, ⁅l, a⁆ ∈ Z := by
      intro l hl
      obtain ⟨hl1, hl2⟩ := Subgroup.mem_inf.mp hl
      exact hx l ⟨hl1, hl2⟩
    exact sec7ctr_QB h34 hRoot hc hs a (Subgroup.mem_inf.mpr ⟨haQ, haB⟩) hcond
  · obtain ⟨haB, haW⟩ := Subgroup.mem_inf.mp ha
    have haQ : a ∈ Q := (Subgroup.mem_inf.mp haW).1
    have hcond : ∀ l ∈ (QB (conjSubgroup r B) ⊓ M) ⊓ (hc.conj_of_mem hrM).CN (r * t * r⁻¹),
        ⁅l, a⁆ ∈ Z := by
      intro l hl
      obtain ⟨hl1, hl2⟩ := Subgroup.mem_inf.mp hl
      rw [hCN] at hl2
      exact hy l ⟨hl1, hl2⟩
    have key := sec7ctr_QB h34 hRoot (hc.conj_of_mem hrM) hs' a
      (Subgroup.mem_inf.mpr ⟨haQ, haB⟩) hcond
    rw [hc.LB_conj hrM, sec7ctr_Vt_conj_frame hrM, hVt] at key
    exact key

end CFSG.RankThree.GF2n.Stroth80
