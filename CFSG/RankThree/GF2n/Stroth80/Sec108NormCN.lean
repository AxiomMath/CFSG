module

public import CFSG.RankThree.GF2n.Stroth80.Sec108PhiL8
public import CFSG.RankThree.GF2n.Stroth80.Sec108Norm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

private theorem mem_normalizer_of_conj_mem {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : conjSubgroup g H ≤ H := by
    intro x hx
    rw [mem_conjSubgroup] at hx
    have h1 := h _ hx
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h1
  exact conjSubgroup_eq_self_iff.mp
    (Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup]))

theorem Sec108Data.mem_Vt_of_comm (D : Sec108Data hc t Y) {v : G} (hv : v ∈ Q)
    (h : ∀ n ∈ LB M Q B ⊓ hc.CN t, ⁅n, v⁆ ∈ Z) : v ∈ Vt M (LB M Q B) B Z t := by
  obtain ⟨AM⟩ := Smith81.Smith23E1.ActionModel.nonempty hc.hyp
  have he : AM.M₀.π v ∈ AM.Vsp hc t := D.mem_Vsp_of_fix AM fun n hn =>
    (comm_mem_iff_fix (M₀ := AM.M₀) (T := AM.φ ⟨n, hc.LB_le_H0 hn.1⟩)
      (hc.conj_mem_Q_of_mem_M (hc.LB_le_M hn.1)).1
      (fun z hz => AM.φ_π ⟨n, hc.LB_le_H0 hn.1⟩ z hz) hv).mp (h n hn)
  obtain ⟨w, hwV, hwQ, hw⟩ := AM.M₀.mem_img.mp (mem_imgSub.mp he)
  have hz : w⁻¹ * v ∈ Z := (AM.M₀.pi_eq_iff hwQ hv).mp hw
  rw [show v = w * (w⁻¹ * v) by group]
  refine Subgroup.mul_mem _ hwV ?_
  unfold Vt
  exact Subgroup.mem_sup_left hz

theorem Sec108Data.conj_Vt_of_mem_normalizer_CN (D : Sec108Data hc t Y) {g : G} (hg : g ∈ M)
    (hgN : g ∈ Subgroup.normalizer ((hc.CN t : Subgroup G) : Set G)) :
    conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t := by
  refine conjSubgroup_eq_self_iff.mpr (mem_normalizer_of_conj_mem fun v hv => ?_)
  have hvQ : v ∈ Q := hc.Vt_le_Q t hv
  refine D.mem_Vt_of_comm (conj_mem_Q hc.hyp hg hvQ) fun n hn => ?_
  have h1 := (Ctx.mem_CN.mp ((Subgroup.mem_normalizer_iff''.mp hgN n).mp hn.2)).2 v hv
  have h2 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hg) _).mp h1
  rwa [show g * ⁅g⁻¹ * n * g, v⁆ * g⁻¹ = ⁅n, g * v * g⁻¹⁆ by
    simp only [commutatorElement_def]; group] at h2

theorem Sec108Data.mem_normalizer_root_iff_CN (D : Sec108Data hc t Y) {g : G} (hg : g ∈ M) :
    g ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) ↔
      g ∈ Subgroup.normalizer ((hc.CN t : Subgroup G) : Set G) :=
  ⟨fun hgY => D.mem_normalizer_CN_of_conj_Vt hg (D.conj_Vt_of_mem_normalizer_root hg hgY),
    fun hgN => D.mem_normalizer_root_of_conj_Rt hg
      (D.conj_Rt_of_conj_Vt hg (D.conj_Vt_of_mem_normalizer_CN hg hgN))⟩

end CFSG.RankThree.GF2n.Stroth80
