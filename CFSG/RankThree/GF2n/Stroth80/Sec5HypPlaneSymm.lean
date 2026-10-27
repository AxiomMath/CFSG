module

public import CFSG.RankThree.GF2n.Stroth80.Sec8HPoints
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsConj
public import CFSG.RankThree.GF2n.Stroth80.Sec34Symm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.hypPlane_symm_sp (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hsp : SpNat hc t)
    {r : G} (hr : r ∈ Rt M (LB M Q B) t)
    (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    HypPlane Q Z (conjSubgroup r B) B t := by
  obtain ⟨K, iF, iFin, hK, m, hm, hrep⟩ := hsp
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hRt : Rt M (LB M Q (conjSubgroup r B)) t = Rt M (LB M Q B) t := by
    rw [hc.LB_conj hrM]
    exact Rt_conj_left hrM t
  have hVtC : Vt M (LB M Q (conjSubgroup r B)) (conjSubgroup r B) Z t =
      Vt M (LB M Q B) B Z t := by
    rw [hc.LB_conj hrM]
    exact Vt_conj_left (M := M) (L := LB M Q B) (B := B) (Z := Z) hrM t
  have hCN : hcC.CN t = hc.CN t := Ctx.CN_conj_left hc hrM t
  have hspC : SpMNat hcC t m := by
    refine ⟨K, iF, iFin, hK, ?_⟩
    rwa [hCN, hRt, hVtC]
  have htC : t ∈ conjSubgroup r (LB M Q B) := by
    rw [mem_conjSubgroup]
    have hcomm : ⁅r⁻¹, t⁆ ∈ Q := hc.Rt_comm_mem_Q ((Rt M (LB M Q B) t).inv_mem hr)
    have e : r⁻¹ * t * r = ⁅r⁻¹, t⁆ * t := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (LB M Q B).mul_mem (sec39_Q_le_LB hcomm) hs.mem
  have hsC : Sec5Hyp hcC n t :=
    { width := hs.width
      n_gt := hs.n_gt
      noA2 := hc.noA2_conj hs.noA2 hrM
      gen := hs.gen.conj_of_mem hrM
      mem := by
        rw [hc.LB_conj hrM]
        exact htC
      notQ := hs.notQ }
  have hs8C : Sec8Hyp hcC n t := ⟨hsC, m, hm, hspC⟩
  have hs8 : Sec8Hyp hc n t := ⟨hs, m, hm, ⟨K, iF, iFin, hK, hrep⟩⟩
  have hnot : ¬ conjSubgroup r B ≤ QB B :=
    (sec8_hypPlane_iff h34 hs8 hr).mp hplane
  have hne : B ≠ conjSubgroup r B := by
    intro hBC
    refine hnot ?_
    rw [← hBC]
    exact hc.B_le_QB
  obtain ⟨g, hg⟩ := hc.conj
  have hCconj : ∃ h : G, conjSubgroup r B = conjSubgroup h Z :=
    ⟨r * g, by rw [hg, conjSubgroup_mul]⟩
  have hsymm : B ≤ QB (conjSubgroup r B) ↔ conjSubgroup r B ≤ QB B :=
    hc.hyp.le_QB_iff_le_QB (B := B) (C := conjSubgroup r B) hc.conj hCconj hne
  have hrInv : r⁻¹ ∈ Rt M (LB M Q (conjSubgroup r B)) t := by
    rw [hRt]
    exact (Rt M (LB M Q B) t).inv_mem hr
  have hiffC := sec8_hypPlane_iff h34 hs8C hrInv
  have hsimp : conjSubgroup r⁻¹ (conjSubgroup r B) = B := by
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  rw [hsimp] at hiffC
  exact hiffC.mpr fun hB => hnot (hsymm.mp hB)

end CFSG.RankThree.GF2n.Stroth80
