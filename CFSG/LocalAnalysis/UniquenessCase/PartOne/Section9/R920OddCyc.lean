module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddAct
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Cyc
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

variable {G : Type} [Group G] [Finite G]

theorem pRank_map_subtype_eq (X : Subgroup G) (Y : Subgroup ↥X) :
    CFSG.Open.pRank 3 (Y.map X.subtype) = CFSG.Open.pRank 3 Y := by
  rw [← CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_three,
    ← CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_three]
  exact CFSG.RankThree.PartOne.Quotient36.pRank_map_subtype Nat.prime_three.one_lt Y

theorem isSylowOf_subgroupOf_top {H P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P H) :
    CFSG.ABGLocalTools.IsSylowOf 3 (P.subgroupOf H) (⊤ : Subgroup ↥H) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff H, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 hP.le, Subgroup.map_top, Subgroup.range_subtype]
  exact hP

namespace SliceCore

variable {D : Data G} {L D₃ Y H : Subgroup G}

theorem pRank_M_le_three (hSg : UC6S846.SigmaStd D) (S : SliceCore D L D₃ Y H)
    (hnsp : ¬ IsStronglyPEmbedded 3 D.M) : CFSG.Open.pRank 3 D.M ≤ 3 := by
  by_contra h
  exact S.three_not_mem_sig hSg hnsp (hSg.four_mem 3 Nat.prime_three (by norm_num) (by omega))

theorem exists_normal_pRank_eq_one (hK : UCK.K332Cyc) (h82 : F08.R82 D) (hSg : UC6S846.SigmaStd D)
    (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) (hKF7 : KF7Use D) (S : SliceCore D L D₃ Y H)
    (hnsp : ¬ IsStronglyPEmbedded 3 D.M) :
    ∃ E N : Subgroup G, E ≤ Opp 3 Y ∧ Nat.card E = 3 ∧ E ≤ N ∧ N ≤ H ∧
      H ≤ normalizer (N : Set G) ∧ CFSG.Open.pRank 3 N = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEX, hE3, hEU⟩ := S.exists_order_three_le_opp
  have hEp : IsPGroup 3 ↥E := IsPGroup.of_card (n := 1) (by simpa using hE3)
  obtain ⟨P, hP, hEP, hPM⟩ := S.exists_sylow_le_M hEX hEp hEU
  have hPH : P ≤ H := hP.le
  have hEH : E ≤ H := hEP.trans hPH
  have hEL : E ≤ L := hEX.trans S.opp_le_L
  obtain ⟨Q, _, φ, hQc, hφ⟩ := S.exists_cyclic_hom_of_isPGroup h82 hnsp hP.isPGroup hPM
  have hHK : CFSG.Open.IsKGroup ↥H :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper D.standing.kProper S.H_ne_top
  let ψ : ↥(P.subgroupOf H) →* Q := φ.comp (Subgroup.subgroupOfEquivOfLe hPH).toMonoidHom
  have hrank : CFSG.Open.pRank 3 (P.subgroupOf H) ≤ 3 := by
    rw [← pRank_map_subtype_eq H, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPH]
    exact (CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) hPM).trans
      (S.pRank_M_le_three hSg hnsp)
  have hwc : CFSG.ASVolI.ChIJK.IsWeaklyClosedIn (E.subgroupOf H) (P.subgroupOf H) := by
    intro g hg
    unfold CFSG.conjugate at hg ⊢
    have hEh : E.map (MulAut.conj ((g⁻¹ : ↥H) : G)).toMonoidHom ≤ P := by
      intro y hy
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hy
      exact Subgroup.mem_subgroupOf.1 (hg (Subgroup.mem_map.2
        ⟨⟨e, hEH he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩))
    have hEq := S.map_conj_eq_of_le h82 hSg h614 h76 hKF7 hnsp hEX hE3 hEU hP.isPGroup hPM hEP
      (g⁻¹).2 hEh
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
      rw [Subgroup.mem_subgroupOf] at hz ⊢
      have h1 : (((MulAut.conj g⁻¹).toMonoidHom z : ↥H) : G) ∈
          E.map (MulAut.conj ((g⁻¹ : ↥H) : G)).toMonoidHom :=
        Subgroup.mem_map.2 ⟨z, hz, by simp [MulAut.conj_apply]⟩
      rwa [hEq] at h1
    · intro hx
      have hx' : (x : G) ∈ E := Subgroup.mem_subgroupOf.1 hx
      rw [← hEq] at hx'
      obtain ⟨e, he, hex⟩ := Subgroup.mem_map.1 hx'
      refine Subgroup.mem_map.2 ⟨⟨e, hEH he⟩, Subgroup.mem_subgroupOf.2 he, Subtype.ext ?_⟩
      simpa [MulAut.conj_apply] using hex
  have hdisj : Disjoint ((E.subgroupOf H).subgroupOf (P.subgroupOf H)) ψ.ker := by
    rw [Subgroup.disjoint_def]
    intro x hx hψx
    have hxE : ((x : ↥H) : G) ∈ E := hx
    have hy : φ (Subgroup.subgroupOfEquivOfLe hPH x) = 1 := hψx
    have hy1 := hφ (Subgroup.subgroupOfEquivOfLe hPH x) (hEL hxE) hy
    exact (MulEquiv.map_eq_one_iff _).1 hy1
  have hcl := hK ↥H hHK (P.subgroupOf H) (isSylowOf_subgroupOf_top hP) hrank (E.subgroupOf H)
    (fun x hx => Subgroup.mem_subgroupOf.2 (hEP (Subgroup.mem_subgroupOf.1 hx)))
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv]; exact hE3) hwc Q hQc ψ hdisj
  set N' := Subgroup.normalClosure ((E.subgroupOf H : Subgroup ↥H) : Set ↥H) with hN'
  have hN'n : N'.Normal := Subgroup.normalClosure_normal
  have hNH : N'.map H.subtype ≤ H := Subgroup.map_subtype_le N'
  refine ⟨E, N'.map H.subtype, hEX, hE3, ?_, hNH, ?_, ?_⟩
  · intro e he
    exact Subgroup.mem_map.2 ⟨⟨e, hEH he⟩,
      Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.2 he), rfl⟩
  · have hn : ((N'.map H.subtype).subgroupOf H).Normal := by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
      exact hN'n
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).1 hn
  · rw [pRank_map_subtype_eq H N']
    exact hcl

end SliceCore

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
