module

public import CFSG.RankThree.GF2n.Tim79aSec23RootGrp
public import CFSG.RankThree.GF2n.Tim79aSec23Linear
public import CFSG.RankThree.GF2n.Tim79aSec23Alt6
public import CFSG.RankThree.GF2n.Tim79aSec23Inputs
public import CFSG.CGT.T75E.Nondegenerate

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.CGT.T75E CFSG.Open CFSG.Assembly.LowTwoRank CFSG.GroupTheory

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

section Certified


theorem lemma26_psl_or_a6 {K : Type} [Group K] [Finite K] [IsSimpleGroup K] {T : Subgroup K}
    (hyp : Lemma26Hyp K T) (hnd : Lemma26Nondeg T) :
    (∃ n f : ℕ, 3 ≤ n ∧ 1 ≤ f ∧ StatedClassicalModel K .PSL n 2 f) ∨
      Nonempty (K ≃* alternatingGroup (Fin 6)) := by
  rcases arsHyp_or_exc_of_hyp (hyp_of_lemma26Hyp hyp hnd) with hars | hA | hJ
  · obtain ⟨A, hA⟩ := rootGroupsIn_nonempty hyp
    obtain ⟨n, f, hn, hf, hL⟩ := lieModel_psl_of_isTI hars (isTI_rootGroupsIn hyp hars) hA
    exact Or.inl ⟨n, f, hn, hf, statedClassicalModel_of_lieModel_psl hL⟩
  · exact Or.inr hA
  · exact (j2_excl K T hyp hnd hJ).elim

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem wc_structure (hd : Sec23Data V H)
    (hnd : ∃ d ∈ Dy V H, ∃ e ∈ Dy V H, orderOf (d * e) = 4)
    (h4 : 4 ≤ Nat.card (barOf V H V)) (hwc : IsWC (Vtilde V H)) :
    IsSimpleGroup (Xbar V H ⧸ Subgroup.center (Xbar V H)) ∧
    ((∃ n f : ℕ, 3 ≤ n ∧ 1 ≤ f ∧
        StatedClassicalModel (Xbar V H ⧸ Subgroup.center (Xbar V H)) .PSL n 2 f) ∨
      Nonempty (Xbar V H ⧸ Subgroup.center (Xbar V H) ≃* alternatingGroup (Fin 6))) := by
  have hH := hc.tilde_hyp hd hnd
  haveI := hH.finite
  have hsimple : IsSimpleGroup (Xbar V H ⧸ Subgroup.center (Xbar V H)) :=
    (CFSG.Timmesfeld.conclusions _ (Dtilde V H) hH.isClass hH.root.1 hH.gen hH.oddCore hH.twoCore
      hH.root.2.1 hH.root.2.2 hH.nondeg).1.1
  refine ⟨hsimple, ?_⟩
  haveI := hsimple
  have hcl := hc.classD_Vtilde hd hnd
  obtain ⟨a₀, ha₀V, ha₀1, ha₀D⟩ := hc.exists_Vtilde_ne_one hd
  have hyp : Lemma26Hyp (Xbar V H ⧸ Subgroup.center (Xbar V H)) (Vtilde V H) := by
    refine ⟨hwc, ?_, ?_, ?_, ?_⟩
    · rw [hc.card_Vtilde hd]
      omega
    · refine ⟨a₀, ?_⟩
      rw [hcl]
      ext g
      constructor
      · intro hg
        exact hH.isConj ha₀D hg
      · intro hg
        obtain ⟨c, hcg⟩ := isConj_iff.mp hg
        rw [← hcg]
        exact hH.conj_mem c ha₀D
    · rw [hcl]
      exact hH.root
    · rw [hcl]
      exact hH.gen
  have hnd' : Lemma26Nondeg (Vtilde V H) := by
    rw [Lemma26Nondeg, hcl]
    exact hH.nondeg
  exact lemma26_psl_or_a6 hyp hnd'

theorem degenerate_of_inputs (h : Tim75aTINotWCRoot) (hd : Sec23Data V H) :
    ∀ d ∈ Dy V H, ∀ e ∈ Dy V H, orderOf (d * e) ≠ 4 := by
  intro d hdD e heD h4
  have hnd : ∃ d ∈ Dy V H, ∃ e ∈ Dy V H, orderOf (d * e) = 4 := ⟨d, hdD, e, heD, h4⟩
  rcases hc.card_barOf_V_eq_two_or_four_le with h2 | h4'
  · exact hc.degenerate_of_card_two hd h2 d hdD e heD h4
  have hH := hc.tilde_hyp hd hnd
  haveI := hH.finite
  by_cases hwc : IsWC (Vtilde V H)
  · obtain ⟨hsimple, hstr⟩ := hc.wc_structure hd hnd h4' hwc
    rcases hstr with ⟨n, f, hn, hf, hM⟩ | hA6
    · obtain ⟨-, F, hFfield, hFfin, hF, ⟨e'⟩⟩ := hM
      haveI : CharP F 2 := charP_two_of_card hF
      obtain ⟨-, hV, -⟩ := lin_wc hn e' hwc (hc.Vtilde_ne_bot hd)
      exact hc.false_of_linear hd hn e' hV
    · obtain ⟨e'⟩ := hA6
      exact hc.false_of_alt6 hd hnd e'
  · obtain ⟨d', hd', hle⟩ := h _ _ hH (Vtilde V H) (hc.Vtilde_ne_bot hd)
      (fun a ha ha1 => hc.Vtilde_mem_Dtilde ha ha1) hc.isElemAbelian_Vtilde
      (hc.isTI_Vtilde hd) hwc
    exact hc.false_of_le_rootGroup hd hnd hd' hle

end MinCex

end Certified

end CFSG.RankThree.GF2n.Tim79a
