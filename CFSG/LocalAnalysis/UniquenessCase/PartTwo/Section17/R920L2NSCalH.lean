module

public import CFSG.LocalAnalysis.UniquenessCase.K332MetaDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2NSAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2NSWeak
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2EvenStrong
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddCyc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
open CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

private theorem sylow_three_isCyclic_of_isL2 {L : Subgroup G} {n : ℕ}
    (hL2 : IsL2 (Bar2 L) n) (T : Sylow 3 ↥L) : IsCyclic ↥(T : Subgroup ↥L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htop : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) L]
    exact le_of_eq (pRank_three_eq_one_of_isL2 hL2)
  exact UCK.K31.isCyclic_of_pRank_le_one Nat.prime_three (by norm_num) T.isPGroup'
    ((CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) le_top).trans htop)

private theorem L9_le_of_le_normalizer_of_isL2 {L H N : Subgroup G} (hLN : L ≤ N)
    (hHN : H ≤ normalizer (N : Set G)) : F09.L9 L H ≤ N := by
  refine iSup_le fun h => ?_
  rintro _ ⟨x, hx, rfl⟩
  have hxL : x ∈ L := opp_le 3 L hx
  have := (Subgroup.mem_normalizer_iff.1 (hHN h.2) x).1 (hLN hxL)
  simpa [MulAut.conj_apply] using this

private theorem mem_uniqueSet_of_card_three_of_isL2 {D : Data G} {L D₃ : Subgroup G} {n : ℕ}
    (hL : L ∈ calC D.M) (hL2 : IsL2 (Bar2 L) n) (hD₃L : D₃ ≤ L)
    (hD₃ : Nat.card D₃ = 3) (hD₃U : D₃ ∈ uniqueSet D.M) {A : Subgroup G} (hAL : A ≤ L)
    (hA : Nat.card A = 3) : A ∈ uniqueSet D.M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj⟩ := CFSG.AGLEmbeddingD2.exists_eq_map_conj_of_isCyclic (J := ↥L) (p := 3)
    (sylow_three_isCyclic_of_isL2 hL2) (Y₀ := D₃.subgroupOf L) (Y₁ := A.subgroupOf L)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD₃L).toEquiv, hD₃])
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hA])
  have heq : A = D₃.map (MulAut.conj (j : G)).toMonoidHom := by
    ext y
    constructor
    · intro hy
      have hy' : (⟨y, hAL hy⟩ : ↥L) ∈ A.subgroupOf L := hy
      rw [hj, Subgroup.mem_map] at hy'
      obtain ⟨d, hd, hdy⟩ := hy'
      exact Subgroup.mem_map.2 ⟨d, hd,
        by simpa [MulAut.conj_apply] using congrArg Subtype.val hdy⟩
    · intro hy
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hy
      have hd' : (⟨d, hD₃L hd⟩ : ↥L) ∈ D₃.subgroupOf L := hd
      have := Subgroup.mem_map_of_mem (MulAut.conj j).toMonoidHom hd'
      rw [← hj] at this
      simpa [MulAut.conj_apply] using Subgroup.mem_subgroupOf.1 this
  rw [heq]
  exact PartTwo.conj_mem_uniqueSet hD₃U (hL.1.le j.2)

private theorem exists_normal_pRank_eq_one_of_isL2 {D : Data G} (hK : UCK.K332Cyc) {n : ℕ}
    (hKM : 3 ∣ n → K332Meta) (h82 : F08.R82 D) (hSg : UC6S846.SigmaStd D) (hKF7 : KF7Use D)
    (hnsp : ¬ IsStronglyPEmbedded 3 D.M) {L H D₃ : Subgroup G} (hL : L ∈ calC D.M)
    (hL2 : IsL2 (Bar2 L) n) (hn : 3 ≤ n) (hσ : ∃ p ∈ D.sig, p ∣ Nat.card L)
    (hD₃L : D₃ ≤ L) (hD₃ : Nat.card D₃ = 3) (hD₃U : D₃ ∈ uniqueSet D.M) (hLH : L ≤ H)
    (hHt : H ≠ ⊤) (hHM : ¬ H ≤ D.M) :
    ∃ N : Subgroup G, D₃ ≤ N ∧ N ≤ H ∧ H ≤ normalizer (N : Set G) ∧
      CFSG.Open.pRank 3 N = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLM : L ≤ D.M := CFSG.Open.IsSubnormal.le hL.1
  have hEp : IsPGroup 3 ↥D₃ := IsPGroup.of_card (n := 1) (by simpa using hD₃)
  obtain ⟨P, hP, hEP⟩ := UC6.exists_isSylowOf_ge (hD₃L.trans hLH) hEp
  have hPM : P ≤ D.M :=
    le_of_mem_uniqueSet_of_isPGroup D.maxLocal hD₃U hEP hP.isPGroup
  have hPH : P ≤ H := hP.le
  have hEH : D₃ ≤ H := hEP.trans hPH
  obtain ⟨Q, _, φ, hQmeta, hQcyc, hφker⟩ :=
    exists_metacyclic_hom_of_isL2 h82 hnsp hL hL2 hP.isPGroup hPM
  let ψ : ↥(P.subgroupOf H) →* Q := φ.comp (Subgroup.subgroupOfEquivOfLe hPH).toMonoidHom
  have hrank : CFSG.Open.pRank 3 (P.subgroupOf H) ≤ 3 := by
    rw [← pRank_map_subtype_eq H, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPH]
    have h3sig : 3 ∉ D.sig := fun h =>
      hnsp (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) h)
    have hM3 : CFSG.Open.pRank 3 D.M ≤ 3 := by
      by_contra h
      exact h3sig (hSg.four_mem 3 Nat.prime_three (by norm_num) (by omega))
    exact (CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) hPM).trans hM3
  have hwc : CFSG.ASVolI.ChIJK.IsWeaklyClosedIn (D₃.subgroupOf H) (P.subgroupOf H) := by
    intro g hg
    unfold CFSG.conjugate at hg ⊢
    have hEh : D₃.map (MulAut.conj ((g⁻¹ : ↥H) : G)).toMonoidHom ≤ P := by
      intro y hy
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hy
      exact Subgroup.mem_subgroupOf.1 (hg (Subgroup.mem_map.2
        ⟨⟨e, hEH he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩))
    have hEq := map_conj_eq_of_le_of_isL2 h82 hSg hKF7 hnsp hL hL2 hn hLH hHt hHM hσ
      hD₃L hD₃ hD₃U hP.isPGroup hPM hEP (g⁻¹).2 hEh
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
      rw [Subgroup.mem_subgroupOf] at hz ⊢
      have h1 : (((MulAut.conj (g⁻¹ : ↥H)).toMonoidHom z : ↥H) : G) ∈
          D₃.map (MulAut.conj ((g⁻¹ : ↥H) : G)).toMonoidHom :=
        Subgroup.mem_map.2 ⟨z, hz, by simp [MulAut.conj_apply]⟩
      rwa [hEq] at h1
    · intro hx
      have hx' : (x : G) ∈ D₃ := Subgroup.mem_subgroupOf.1 hx
      rw [← hEq] at hx'
      obtain ⟨e, he, hex⟩ := Subgroup.mem_map.1 hx'
      refine Subgroup.mem_map.2 ⟨⟨e, hEH he⟩, Subgroup.mem_subgroupOf.2 he, Subtype.ext ?_⟩
      simpa [MulAut.conj_apply] using hex
  have hdisj : Disjoint ((D₃.subgroupOf H).subgroupOf (P.subgroupOf H)) ψ.ker := by
    rw [Subgroup.disjoint_def]
    intro x hx hψx
    have hxE : ((x : ↥H) : G) ∈ D₃ := hx
    have hy : φ (Subgroup.subgroupOfEquivOfLe hPH x) = 1 := hψx
    have hy1 := hφker (Subgroup.subgroupOfEquivOfLe hPH x) (hD₃L hxE) hy
    exact (MulEquiv.map_eq_one_iff _).1 hy1
  have hHK : CFSG.Open.IsKGroup ↥H :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper D.standing.kProper hHt
  have hcl : CFSG.Open.pRank 3
      (Subgroup.normalClosure ((D₃.subgroupOf H : Subgroup ↥H) : Set ↥H)) = 1 := by
    by_cases h3 : 3 ∣ n
    · exact hKM h3 ↥H hHK (P.subgroupOf H) (isSylowOf_subgroupOf_top hP) hrank
        (D₃.subgroupOf H)
        (fun x hx => Subgroup.mem_subgroupOf.2 (hEP (Subgroup.mem_subgroupOf.1 hx)))
        (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv]; exact hD₃)
        hwc Q hQmeta ψ hdisj
    · exact hK ↥H hHK (P.subgroupOf H) (isSylowOf_subgroupOf_top hP) hrank
        (D₃.subgroupOf H)
        (fun x hx => Subgroup.mem_subgroupOf.2 (hEP (Subgroup.mem_subgroupOf.1 hx)))
        (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv]; exact hD₃)
        hwc Q (hQcyc h3) ψ hdisj
  set N' : Subgroup ↥H := Subgroup.normalClosure
    ((D₃.subgroupOf H : Subgroup ↥H) : Set ↥H) with hN'
  have hN'n : N'.Normal := Subgroup.normalClosure_normal
  refine ⟨N'.map H.subtype, ?_, Subgroup.map_subtype_le N', ?_, ?_⟩
  · intro e he
    exact Subgroup.mem_map.2 ⟨⟨e, hEH he⟩,
      Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.2 he), rfl⟩
  · have hn : ((N'.map H.subtype).subgroupOf H).Normal := by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
      exact hN'n
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le N')).1 hn
  · rw [pRank_map_subtype_eq H N']
    exact hcl

theorem mem_calH9_of_isL2_not_sp {D : Data G} (hK : UCK.K332Cyc) {n : ℕ}
    (hKM : 3 ∣ n → K332Meta) (h82 : F08.R82 D) (hSg : UC6S846.SigmaStd D) (hKF7 : KF7Use D)
    (hnsp : ¬ IsStronglyPEmbedded 3 D.M) {L D₃ H : Subgroup G} (hL : L ∈ calC D.M)
    (hL2 : IsL2 (Bar2 L) n) (hn : 3 ≤ n) (hσ : ∃ p ∈ D.sig, p ∣ Nat.card L)
    (hD₃L : D₃ ≤ L) (hD₃ : Nat.card D₃ = 3) (hD₃U : D₃ ∈ uniqueSet D.M)
    (hLH : L ≤ H) (hHt : H ≠ ⊤) (hHM : ¬ H ≤ D.M) : H ∈ F09.calH9 D L := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨hLH, hHM, ?_⟩
  obtain ⟨N, hD₃N, hNH, hHN, hNrank⟩ :=
    exists_normal_pRank_eq_one_of_isL2 hK hKM h82 hSg hKF7 hnsp hL hL2 hn hσ
      hD₃L hD₃ hD₃U hLH hHt hHM
  have hLN : L ≤ N := by
    have hNB : L ≤ normalizer (((N ⊓ L : Subgroup G) : Set G)) := by
      intro l hl
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨hxN, hxL⟩
        have h1 : l * x * l⁻¹ ∈ N :=
          (Subgroup.mem_normalizer_iff.1 (hHN (hLH hl)) x).1 hxN
        exact ⟨by simpa [MulAut.conj_apply] using h1,
          L.mul_mem (L.mul_mem hl hxL) (L.inv_mem hl)⟩
      · rintro ⟨hxN, hxL⟩
        have h1 : l⁻¹ * (l * x * l⁻¹) * l ∈ N := by
          simpa using (Subgroup.mem_normalizer_iff.1 (hHN (hLH (L.inv_mem hl)))
            (l * x * l⁻¹)).1 hxN
        have hx : l⁻¹ * (l * x * l⁻¹) * l = x := by group
        rw [hx] at h1
        refine ⟨h1, ?_⟩
        rw [← hx]
        exact L.mul_mem (L.mul_mem (L.inv_mem hl) hxL) hl
    have hBeq : N ⊓ L = L :=
      PartTwo.eq_of_normal_of_isL2 hL.2.1 hL2 inf_le_right hNB
        (le_inf hD₃N hD₃L) hD₃
    calc L = N ⊓ L := hBeq.symm
      _ ≤ N := inf_le_left
  have hL9N : F09.L9 L H ≤ N := L9_le_of_le_normalizer_of_isL2 hLN hHN
  have hle : CFSG.Open.pRank 3 (F09.L9 L H) ≤ 1 :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) hL9N).trans
      (le_of_eq hNrank)
  have hD₃Opp : D₃ ≤ Opp 3 L := by
    rw [opp3_eq_self_of_isL2 hL.2.1 hL2]
    exact hD₃L
  have hD₃L9 : D₃ ≤ F09.L9 L H := fun x hx =>
    le_iSup (fun h : ↥H => (Opp 3 L).map (MulAut.conj (h : G)).toMonoidHom) 1
      (Subgroup.mem_map.2 ⟨x, hD₃Opp hx, by simp [MulAut.conj_apply]⟩)
  have hge : 1 ≤ CFSG.Open.pRank 3 (F09.L9 L H) :=
    UC6S846.le_pRank' Nat.prime_three hD₃L9
      (CFSG.GroupTheory.isElemAbelian_of_card_prime hD₃) (k := 1) (by simpa using hD₃)
  exact le_antisymm hle hge

theorem uniqueMax_or_mem_calY2_of_not_sp {D : Data G} (hK : UCK.K332Cyc) {n : ℕ}
    (hKM : 3 ∣ n → K332Meta) (h82 : F08.R82 D) (hSg : UC6S846.SigmaStd D) (hKF7 : KF7Use D)
    (hnsp : ¬ IsStronglyPEmbedded 3 D.M) {L D₃ : Subgroup G} (hL : L ∈ calC D.M)
    (hL2 : IsL2 (Bar2 L) n) (hn : 3 ≤ n) (hσ : ∃ p ∈ D.sig, p ∣ Nat.card L)
    (hD₃L : D₃ ≤ L) (hD₃ : Nat.card D₃ = 3) (hD₃U : D₃ ∈ uniqueSet D.M) :
    UniqueMax D.M L ∨ L ∈ F09.calY2_9 D := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hU : UniqueMax D.M L
  · exact Or.inl hU
  · right
    have hLM : L ≤ D.M := CFSG.Open.IsSubnormal.le hL.1
    haveI : IsSimpleGroup G := D.standing.simple
    have hY9 : L ∈ F09.calY9 D :=
      ⟨hLM, F09.calNOf_ne_of_calMOf_ne D hLM hU,
        fun A hAL hA3 => mem_uniqueSet_of_card_three_of_isL2 hL hL2 hD₃L hD₃ hD₃U hAL hA3⟩
    refine ⟨hY9, hU, ?_, ?_, ?_⟩
    · intro N hN
      by_cases hNM : N = D.M
      · exact Or.inr hNM
      · exact Or.inl (mem_calH9_of_isL2_not_sp hK hKM h82 hSg hKF7 hnsp hL hL2 hn hσ
          hD₃L hD₃ hD₃U hN.2
          (CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab hN.1.1)
          (F09.not_le_of_mem_calMOf D hN hNM))
    · intro A hA
      rw [opp3_eq_self_of_isL2 hL.2.1 hL2]
      exact commutator_le_pCoreOf_of_mem_inv9'_of_isL2 hL hL2 hA
    · refine ⟨0, ?_⟩
      rw [opp3_eq_self_of_isL2 hL.2.1 hL2, Subgroup.subgroupOf_self, Subgroup.index_top,
        pow_zero]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
