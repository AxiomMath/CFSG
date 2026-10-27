module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3TIB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8UAB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_L_sup_le_cent_v1 (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    L ⊔ conjSubgroup L x ≤
      Subgroup.centralizer ((v1Sub D.M ⊥ V h.hyp151.isElemAbelian L : Subgroup G) : Set G) := by
  obtain ⟨hLW, hLxW⟩ := s16h_e3_cross_centralize D h hxM hxn
  rw [s16h_e3_v1Sub_eq_sup_zx D h hs2 hxM hxn]
  refine sup_le ?_ ?_
  ·
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hZl : (wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) ⊔
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) x ≤
        Subgroup.centralizer ({l} : Set G) := by
      refine sup_le ?_ ?_
      · intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.1 hy]
        exact ((Subgroup.mem_centralizer_iff.1 hz.2) l hl)
      · intro z hz
        have hzW : z ∈ conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x :=
          E3.conjSubgroup_mono_left x inf_le_left hz
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.1 hy]
        exact ((Subgroup.mem_centralizer_iff.1 (hLW hl)) z hzW).symm
    exact ((Subgroup.mem_centralizer_iff.1 (hZl hg)) l (Set.mem_singleton l)).symm
  ·
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hZl : (wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) ⊔
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) x ≤
        Subgroup.centralizer ({l} : Set G) := by
      refine sup_le ?_ ?_
      · intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.1 hy]
        exact ((Subgroup.mem_centralizer_iff.1 (hLxW hl)) z hz.1).symm
      · intro z hz
        have hzc : z ∈ conjSubgroup (Subgroup.centralizer (L : Set G)) x :=
          E3.conjSubgroup_mono_left x inf_le_right hz
        rw [E3.conjSubgroup_centralizer] at hzc
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.1 hy]
        exact (Subgroup.mem_centralizer_iff.1 hzc) l hl
    exact ((Subgroup.mem_centralizer_iff.1 (hZl hg)) l (Set.mem_singleton l)).symm

theorem s16h_e3_v1_hw (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    {q : ℕ} (hq : q ∈ D.sig) (hqp : q.Prime)
    (hpr : 2 ≤ CFSG.Open.pRank q (L ⊔ conjSubgroup L x)) :
    ∀ w ∈ v1Sub D.M ⊥ V h.hyp151.isElemAbelian L, w ≠ 1 →
      ∃ p ∈ D.sig, 2 ≤ CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer ({w} : Set G)) := by
  intro w hw _
  refine ⟨q, hq, hpr.trans (CFSG.SectionRank.pRank_mono hqp.one_lt ?_)⟩
  have hLM : L ≤ D.M := h.hyp151.le
  have hLxM : conjSubgroup L x ≤ D.M := by
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have h1 : x⁻¹ * (x * y * x⁻¹) * x ∈ D.M :=
      D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hxM) (hLM hy)) hxM
    convert h1 using 1
    group
  refine le_inf (sup_le hLM hLxM) fun l hl => ?_
  have hc := s16h_e3_L_sup_le_cent_v1 D h hs2 hxM hxn hl
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff.1 hy]
  exact (Subgroup.mem_centralizer_iff.1 hc) w hw

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
