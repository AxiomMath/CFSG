module

public import CFSG.RankThree.PartOne.DISTX.Row9Comm
public import CFSG.RankThree.PartOne.K1320X.CommRes

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.DISTX

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem false_of_perfect_in_distinct (hp : p.Prime) {e : G} {I₁ I₂ K : Subgroup G}
    (h1 : I₁ ∈ thetaComponentsAt p e) (h2 : I₂ ∈ thetaComponentsAt p e) (hne : I₁ ≠ I₂)
    (hK₁ : K ≤ I₁) (hK₂ : K ≤ I₂) (hperf : Group.IsPerfect ↥K) (hnt : Nontrivial ↥K) : False := by
  set Θ := inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({e} : Set G)) with hΘ
  have hcomm : ⁅K, K⁆ ≤ Θ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact S11d.commutator_mem_theta_of_ne hp h1 h2 hne x (hK₁ hx) y (hK₂ hy)
  have hKΘ : K ≤ Θ := by
    have := Subgroup.isPerfect_iff.mp hperf
    rwa [this] at hcomm
  obtain ⟨hΘs, -⟩ := theta_solvable_and_not_dvd hp (Subgroup.centralizer ({e} : Set G))
  have hsolv : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKΘ)
      (Subgroup.inclusion_injective hKΘ)
  obtain ⟨n, hn⟩ := hsolv.solvable
  rw [derivedSeries_eq_top_of_isPerfect hperf n] at hn
  obtain ⟨a, b, hab⟩ := exists_pair_ne ↥K
  have ha : a ∈ (⊥ : Subgroup ↥K) := hn ▸ Subgroup.mem_top a
  have hb : b ∈ (⊥ : Subgroup ↥K) := hn ▸ Subgroup.mem_top b
  rw [Subgroup.mem_bot] at ha hb
  exact hab (ha.trans hb.symm)

theorem kfCommDistinctXne_of_nodes (hS : SchreierFor InCatalog) (hRe : Sec13Reinst)
    (hLift : KFLiftAll) (h133 : KF133Two) (hSame : KFCommSame) (h136 : Node136)
    (h138I : Node138I) (h124b : Node124b) (h137 : Node137) (h138T : Node138Trans) :
    K1320X.KFCommDistinctXne := by
  intro G _ _ p A c L E h hF hF13 hT hEA s hs t ht hLs hLt hcomm e he he1 I₁ hI₁ I₂ hI₂ hI hK₁ hK₂
  by_cases hst : s = t
  · subst hst
    exfalso
    have hq : IsSimpleGroup (↥(kZero p E s) ⧸ Subgroup.center ↥(kZero p E s)) := hLs.1.2.1
    have hnt : Nontrivial ↥(kZero p E s) :=
      (QuotientGroup.mk'_surjective (Subgroup.center ↥(kZero p E s))).nontrivial
    exact false_of_perfect_in_distinct h.prime hI₁ hI₂ hI hK₁ hK₂ hLs.1.1 hnt
  · obtain ⟨-, r, hr1, hr12, hmodel, hweyl, hr8, hr9⟩ := hF.three
    have hr9' : 9 ≤ r := by
      by_contra hlt
      exact hEA (hr8 (by omega))
    have hnot10 := h136 G p A c L E h hF hF13 hT hEA
    obtain ⟨hnot11, hnot12⟩ := h138I G p A c L E h hF hF13 hT hEA
    have hr : r = 9 := by
      by_contra hne9
      have h10 : r = 10 ∨ r = 11 ∨ r = 12 := by omega
      rcases h10 with rfl | rfl | rfl
      · exact hnot10 hmodel
      · exact hnot11 ⟨hmodel, hweyl⟩
      · exact hnot12 ⟨hmodel, hweyl⟩
    subst hr
    have hD3 := h137 G p A c L E h hF hF13 hT hEA hmodel
    have hTr := h138T G p A c L E h hF hF13 hT hEA hmodel hD3
    exact kf134Comm_of_members hS hRe hLift h133 hSame h136 h138I h124b G p A c L E h hF hF13 hT
      hEA hmodel hD3 hTr s hs t ht hst hcomm

end CFSG.RankThree.PartOne.DISTX
