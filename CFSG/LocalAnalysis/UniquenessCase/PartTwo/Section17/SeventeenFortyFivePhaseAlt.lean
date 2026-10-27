module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseSylow
import CFSG.LocalAnalysis.UniquenessCase.UCFront10K101
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rm
import CFSG.GroupTheory.PermutesPullback
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.Open
open scoped Pointwise commutatorElement

theorem phase45_false_of_alternating {X : Type} [Group X] [Finite X] {L A₁ A₂ T : Subgroup X}
    (hLn : L.Normal) (hLs : IsSimpleGroup L) (hLnab : ¬ IsMulCommutative L)
    (hCL : centralizer (L : Set X) = ⊥) {m : ℕ} (e : ↥L ≃* alternatingGroup (Fin m))
    (hA1 : Nat.card A₁ = 31) (hA2 : Nat.card A₂ = 31) (hA12 : A₁ ⊓ A₂ = ⊥)
    (hA12c : A₁ ≤ centralizer (A₂ : Set X)) (hT : IsPGroup 2 T)
    (hAT : ((A₁ ⊔ A₂ : Subgroup X) : Set X) * (T : Set X) =
      (T : Set X) * ((A₁ ⊔ A₂ : Subgroup X) : Set X))
    (hTL : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L) L) : False := by
  obtain ⟨hAcard, hAab⟩ := phase45_card_sup hA1 hA2 hA12 hA12c
  set A : Subgroup X := A₁ ⊔ A₂
  have hAodd : Odd (Nat.card A) := by
    rw [hAcard]
    norm_num
  set G₀ : Subgroup X := L ⊔ (A ⊔ T)
  have hLG₀ : L ≤ G₀ := le_sup_left
  have hAG₀ : A ≤ G₀ := le_sup_left.trans le_sup_right
  have hTG₀ : T ≤ G₀ := le_sup_right.trans le_sup_right
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 T G₀ :=
    phase45_isSylowOf_two_sup hLn hAodd hT hAT hTL
  set B₀ : Subgroup ↥G₀ := A.subgroupOf G₀
  set T₀ : Subgroup ↥G₀ := T.subgroupOf G₀
  set L₀ : Subgroup ↥G₀ := L.subgroupOf G₀
  have hT₀syl : CFSG.ABGLocalTools.IsSylowOf 2 T₀ ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff G₀).1 ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTG₀, Subgroup.map_top,
      Subgroup.range_subtype]
    exact hSyl
  have hB₀card : Nat.card ↥B₀ = 31 ^ 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAG₀).toEquiv).trans hAcard
  have hB₀ab : IsMulCommutative ↥B₀ := by
    haveI : IsMulCommutative ↥A := hAab
    exact Subgroup.subgroupOf_isMulCommutative G₀ A
  have hB₀odd : Odd (Nat.card ↥B₀) := by
    rw [hB₀card]
    norm_num
  have hB₀perm : UC22.Permutes B₀ T₀ := by
    refine CFSG.GroupTheory.permutes_of_map_permutes G₀.subtype (by simp) ?_
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hAG₀, inf_eq_left.mpr hTG₀]
    exact hAT
  have hpRank : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥B₀ → CFSG.Open.pRank p B₀ ≤ 2 := by
    intro p hp hpdvd
    rw [hB₀card] at hpdvd
    have hp31 : p = 31 := by
      have hdvd : p ∣ 31 := hp.dvd_of_dvd_pow hpdvd
      exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hdvd
    subst hp31
    refine CFSG.SectionRank.pRank_le (by norm_num) ?_
    intro E hE _
    exact (Subgroup.card_le_of_le hE).trans_eq hB₀card
  have hHyp : UC22.F10.Hyp10 T₀ B₀ :=
    ⟨hT₀syl, hB₀ab, hB₀odd, hB₀perm, hpRank⟩
  haveI hL₀normal : L₀.Normal := hLn.subgroupOf G₀
  have hLs₀ : IsSimpleGroup ↥L₀ := by
    haveI : IsSimpleGroup ↥L := hLs
    exact (Subgroup.subgroupOfEquivOfLe hLG₀).isSimpleGroup
  have hL₀nab : ∃ a b : ↥L₀, a * b ≠ b * a := by
    by_contra h
    push Not at h
    refine hLnab (isMulCommutative_iff.mpr fun a b => ?_)
    have hcomm := h ((Subgroup.subgroupOfEquivOfLe hLG₀).symm a)
      ((Subgroup.subgroupOfEquivOfLe hLG₀).symm b)
    have hcomm' := congrArg (Subgroup.subgroupOfEquivOfLe hLG₀) hcomm
    simpa using hcomm'
  have hCL₀ : centralizer (L₀ : Set ↥G₀) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    apply Subtype.ext
    have hx' : (x : X) ∈ centralizer (L : Set X) := by
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro y hy
      have hy₀ : (⟨y, hLG₀ hy⟩ : ↥G₀) ∈ L₀ := hy
      simpa using congrArg Subtype.val (hx ⟨y, hLG₀ hy⟩ hy₀)
    rw [hCL] at hx'
    exact hx'
  have hF : genFittingFStar ↥G₀ = L₀ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_fstar_eq hLs₀ hL₀nab hCL₀
  have hAlt : ∃ n : ℕ, UC22.IsAlt ↥(genFittingFStar ↥G₀) n := by
    refine ⟨m, ?_⟩
    rw [hF]
    exact ⟨(Subgroup.subgroupOfEquivOfLe hLG₀).trans e⟩
  have h3 : IsPGroup 3 ↥B₀ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.F10.k101_holds ↥G₀ T₀ B₀ hHyp hAlt
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h3dvd : 3 ∣ Nat.card ↥B₀ := by
    rcases IsPGroup.card_eq_or_dvd h3 with h | h
    · rw [hB₀card] at h
      norm_num at h
    · exact h
  rw [hB₀card] at h3dvd
  norm_num at h3dvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
