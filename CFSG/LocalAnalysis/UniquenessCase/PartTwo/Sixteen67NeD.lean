module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67NeA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen68Close
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTwentyTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s1667ne_normalizer₀ (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (h0 : V₀ ≠ ⊥) :
    normalizer (V₀ : Set G) = D.M ∧ CFSG.CGT.Timmesfeld75.IsTI V₀ := by
  rcases h.1 with ⟨-, h0'⟩ | ⟨hV0, -, -⟩
  · exact absurd h0' h0
  · exact ⟨normalizer_eq_of_inCalV D hV0.1, hV0.2.2.2.1⟩

theorem s1667ne_uniqueMax (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hs : Sit1665 D V₀ V hV L) {x : G} (hxM : x ∈ D.M) {w : G}
    (hw : w ∈ wSub V₀ V hV L ∨ w ∈ conjSubgroup (wSub V₀ V hV L) x) (hw1 : w ≠ 1) :
    UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  rcases hw with hw | hw
  · exact hs.2.unique₁ w (Subgroup.mem_sup_left hw) hw1
  · have h := uniqueMax_conjSubgroup_of_mem (g := x)
      (fun w hw hw1 => hs.2.unique₁ w (Subgroup.mem_sup_left hw) hw1) hw hw1
    rwa [conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hxM)] at h

theorem s1667ne_centralizer_le (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hs : Sit1665 D V₀ V hV L) {x : G} (hxM : x ∈ D.M) {w : G}
    (hw : w ∈ wSub V₀ V hV L ∨ w ∈ conjSubgroup (wSub V₀ V hV L) x) (hw1 : w ≠ 1) :
    centralizer ({w} : Set G) ≤ D.M := by
  have hWV : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV _
  have hxN : x ∈ normalizer (V : Set G) :=
    (Hyp125.normalizer_eq hS.setting.hyp16.hyp125).ge hxM
  have hconjV : conjSubgroup V x = V := conjSubgroup_eq_iff_mem_normalizer.mpr hxN
  have hwV : w ∈ V := by
    rcases hw with hw | hw
    · exact hWV hw
    · have h := E3.conjSubgroup_mono_left x hWV hw
      rwa [hconjV] at h
  have hw2 : ∃ n : ℕ, w ^ (2 ^ n) = 1 := ⟨1, by simpa using hV.2 w hwV⟩
  exact (centralizer_le_of_uniqueMax D.maxLocal hw1 hw2
    (s1667ne_uniqueMax D hs hxM hw hw1)).1

theorem s1667ne_cfg (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h61 : UC6.R6_1 D) (h1217 : R1217 D) (h129 : R129_1 D) (h159 : R15_9Small D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hs : Sit1665 D V₀ V hV L) (h0 : V₀ ≠ ⊥) {x : G} (hxM : x ∈ D.M)
    (hxn : x ∉ nBar D.M V₀ V hV L) :
    Cfg1667Ne D.M V₀ V (wSub V₀ V hV L) (conjSubgroup (wSub V₀ V hV L) x) := by
  have hW0 : ⁅E3.wClos V 0 D.T, V⁆ = ⊥ :=
    (sixteen_sixtyThree D hSg h129 h61 h159 V₀ V L hV hS ⟨Or.inr hs.1, hs.2⟩).1
  have hWV : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV _
  have hxN : x ∈ normalizer (V : Set G) :=
    (Hyp125.normalizer_eq hS.setting.hyp16.hyp125).ge hxM
  have hconjV : conjSubgroup V x = V := conjSubgroup_eq_iff_mem_normalizer.mpr hxN
  have hWxV : conjSubgroup (wSub V₀ V hV L) x ≤ V := by
    have h := E3.conjSubgroup_mono_left x hWV
    rwa [hconjV] at h
  refine ⟨hV, h0, s1667_sup_conj_eq D h1217 hS hs.1 hxM hxn,
    s1667_inf_conj_eq D hS hs.1 hxM hxn, s1667_card_wSub D hS hs.1, ?_,
    Hyp125.normalizer_eq hS.setting.hyp16.hyp125,
    (s1667ne_normalizer₀ D hS.setting.hyp16.hyp125 h0).1,
    (s1667ne_normalizer₀ D hS.setting.hyp16.hyp125 h0).2,
    fun m hm => s1667_conj_cases D hS hs.1 hxM hxn hm,
    fun w hw hw1 => s1667ne_centralizer_le D hS hs hxM hw hw1, ?_, ?_⟩
  · rw [E3.card_conjSubgroup (wSub V₀ V hV L) x, s1667_card_wSub D hS hs.1]
  · intro y hy
    exact ⟨c23_inf_conjSubgroup_eq_bot D (R1622_of_R1621 D hSg h1219 h21)
        hS.setting.hyp16 hWV
        (fun w hw hw1 => s1667ne_uniqueMax D hs hxM (Or.inl hw) hw1) hy,
      c23_inf_conjSubgroup_eq_bot D (R1622_of_R1621 D hSg h1219 h21)
        hS.setting.hyp16 hWxV
        (fun w hw hw1 => s1667ne_uniqueMax D hs hxM (Or.inr hw) hw1) hy⟩
  · intro y hy
    exact s1668_comm_eq_bot_of_conj_le D hS.setting.hyp16.hyp125 hW0 hy

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
