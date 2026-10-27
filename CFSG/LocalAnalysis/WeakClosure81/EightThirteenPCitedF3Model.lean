module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedF3Top
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelMain
import CFSG.LocalAnalysis.UniquenessCase.Lie.DiagGraphL3
import CFSG.LocalAnalysis.UniquenessCase.Lie.DiagGraphSp4
import CFSG.Adapters.StatedSLPerfect

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsSp4)
open CFSG.Quasithin (IsSylowIn conjSubgroup)
open CFSG.QuasithinUnique (IsSylowTwoOf IsRankTwoEvenType)
open Subgroup

private theorem wccm_isPerfect_of_lieModel_PSL3 {M : Type} [Group M]
    (h : CFSG.Blueprint.LieModel M .PSL 3 2 2) : Group.IsPerfect M := by
  obtain ⟨-, K, hKfield, hKfin, -, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  letI : Field K := hKfield
  letI : Finite K := hKfin
  haveI : Group.IsPerfect (CFSG.Open.StatedSL 3 K) :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le (by norm_num) K
  haveI : Group.IsPerfect (CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K)) := inferInstance
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

private theorem wccm_isPerfect_of_lieModel_PSp2 {M : Type} [Group M]
    (h : CFSG.Blueprint.LieModel M .PSp 2 2 2) : Group.IsPerfect M := by
  obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  letI : Field K := hKfield
  letI : Finite K := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  have h4 : ∃ s : Finset K, s.card = 4 := by
    refine ⟨Finset.univ, ?_⟩
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hKcard]
    norm_num
  haveI : Group.IsPerfect (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect 2 K (Or.inl h4)
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

private theorem wccm_borelRankTwoTop_of_rankTwo (M : Type) [Group M] [Finite M]
    (hperf : Group.IsPerfect M) (hsimple : IsSimpleGroup M)
    (hrk : IsRankTwoEvenType (⊤ : Subgroup M))
    (htwo : ∀ V : Sylow 2 M,
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pdiag_TwoClasses M (V : Subgroup M)) :
    BorelRankTwoTop M := by
  intro S hS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let V : Sylow 2 M := hS.isPGroup.toSylow (by
    have h := hS.not_dvd_relIndex
    rwa [Subgroup.relIndex_top_right] at h)
  have hV : (V : Subgroup M) = S := IsPGroup.toSylow_coe _ _
  haveI : Group.IsPerfect M := hperf
  haveI : Group.IsPerfect (↥(⊤ : Subgroup M)) := inferInstance
  haveI : IsSimpleGroup M := hsimple
  haveI : IsSimpleGroup (↥(⊤ : Subgroup M)) :=
    (Subgroup.topEquiv : ↥(⊤ : Subgroup M) ≃* M).isSimpleGroup
  have hcenter : Subgroup.center (↥(⊤ : Subgroup M)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (↥(⊤ : Subgroup M))) with h | h
    · exact h
    · exfalso
      exact (Group.IsPerfect.not_isMulCommutative (↥(⊤ : Subgroup M)))
        (Subgroup.center_eq_top_iff.mp h)
  let eQ : (↥(⊤ : Subgroup M) ⧸ Subgroup.center (↥(⊤ : Subgroup M))) ≃* ↥(⊤ : Subgroup M) :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (QuotientGroup.quotientBot (G := ↥(⊤ : Subgroup M)))
  have hncM : ¬ IsMulCommutative M := Group.IsPerfect.not_isMulCommutative M
  have hncTop : ∃ a b : ↥(⊤ : Subgroup M), a * b ≠ b * a := by
    have hncM' : ∃ a b : M, a * b ≠ b * a := by
      by_contra h
      push Not at h
      exact hncM ⟨⟨h⟩⟩
    obtain ⟨a, b, hab⟩ := hncM'
    exact ⟨⟨a, trivial⟩, ⟨b, trivial⟩,
      fun h => hab (by simpa using congrArg Subtype.val h)⟩
  have hq : CFSG.IsQuasisimple (↥(⊤ : Subgroup M)) := by
    refine ⟨inferInstance, eQ.isSimpleGroup, ?_⟩
    obtain ⟨a, b, hab⟩ := hncTop
    exact ⟨eQ.symm a, eQ.symm b, fun h => hab (by simpa using congrArg (⇑eQ) h)⟩
  have hsyl : IsSylowTwoOf S (⊤ : Subgroup M) := hS
  obtain ⟨-, P₁, P₂, hBP₁, hP₁top, hBP₂, hP₂top, hP₁P₂, hsup, huniq, -, -⟩ :=
    CFSG.QuasithinUnique.rankTwoBorelFacts M ⊤ S hq hrk hsyl
  simp only [top_inf_eq] at hBP₁ hBP₂ huniq
  have hcoat₁ : IsCoatom P₁ := by
    refine ⟨ne_of_lt hP₁top, ?_⟩
    intro Q hQ
    by_cases hQtop : Q = ⊤
    · exact hQtop
    · exfalso
      have hQlt : Q < ⊤ := lt_top_iff_ne_top.mpr hQtop
      have hBQ : normalizer (S : Set M) < Q := lt_of_lt_of_le hBP₁ (le_of_lt hQ)
      rcases huniq Q hBQ hQlt with h | h
      · exact absurd h (ne_of_gt hQ)
      · have hle : P₁ ≤ P₂ := h ▸ le_of_lt hQ
        have hsup' : P₁ ⊔ P₂ = P₂ := sup_eq_right.mpr hle
        rw [hsup] at hsup'
        exact absurd hsup'.symm (ne_of_lt hP₂top)
  have hcoat₂ : IsCoatom P₂ := by
    refine ⟨ne_of_lt hP₂top, ?_⟩
    intro Q hQ
    by_cases hQtop : Q = ⊤
    · exact hQtop
    · exfalso
      have hQlt : Q < ⊤ := lt_top_iff_ne_top.mpr hQtop
      have hBQ : normalizer (S : Set M) < Q := lt_of_lt_of_le hBP₂ (le_of_lt hQ)
      rcases huniq Q hBQ hQlt with h | h
      · have hle : P₂ ≤ P₁ := h ▸ le_of_lt hQ
        have hsup' : P₁ ⊔ P₂ = P₁ := sup_eq_left.mpr hle
        rw [hsup] at hsup'
        exact absurd hsup'.symm (ne_of_lt hP₁top)
      · exact absurd h (ne_of_gt hQ)
  obtain ⟨Q₁, Q₂, -, -, -, -, -, hQuniq, hQnc⟩ := htwo V
  rw [hV] at hQuniq
  have hP₁mem : P₁ = Q₁ ∨ P₁ = Q₂ := hQuniq P₁ hcoat₁ (le_of_lt hBP₁)
  have hP₂mem : P₂ = Q₁ ∨ P₂ = Q₂ := hQuniq P₂ hcoat₂ (le_of_lt hBP₂)
  have hcases : (P₁ = Q₁ ∧ P₂ = Q₂) ∨ (P₁ = Q₂ ∧ P₂ = Q₁) := by
    rcases hP₁mem with h1 | h1 <;> rcases hP₂mem with h2 | h2
    · exact absurd (h1.trans h2.symm) hP₁P₂
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) hP₁P₂
  have hnc : ∀ g : M, conjSubgroup P₁ g ≠ P₂ := by
    intro g hg
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at hg
      exact hQnc g⁻¹ (by simpa [CFSG.Quasithin.conjSubgroup] using hg)
    · rw [h1, h2] at hg
      have h2' : conjSubgroup Q₁ g⁻¹ = Q₂ := by
        have hthis := congrArg (fun A => conjSubgroup A g⁻¹) hg
        rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel,
          CFSG.Quasithin.conjSubgroup_one] at hthis
        exact hthis.symm
      exact hQnc g (by simpa [CFSG.Quasithin.conjSubgroup, inv_inv] using h2')
  refine ⟨P₁, P₂, hP₁top, hP₂top, fun Q hQ => hcoat₁.2 Q hQ,
    fun Q hQ => hcoat₂.2 Q hQ, le_of_lt hBP₁, le_of_lt hBP₂, hnc, ?_⟩
  intro P hP
  by_cases hPB : P = normalizer (S : Set M)
  · exact Or.inl hPB
  · by_cases hPtop : P = ⊤
    · exact Or.inr (Or.inr (Or.inr hPtop))
    · have hBP : normalizer (S : Set M) < P := lt_of_le_of_ne hP (Ne.symm hPB)
      have hPtop' : P < ⊤ := lt_top_iff_ne_top.mpr hPtop
      rcases huniq P hBP hPtop' with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))

theorem borelRankTwoTop_of_isL3 {M : Type} [Group M] [Finite M] (h : IsL3 M 2) :
    BorelRankTwoTop M := by
  have hSCM : CFSG.Open.StatedClassicalModel M .PSL 3 2 2 :=
    (h : CFSG.Blueprint.LieModel M .PSL 3 2 2).statedClassicalModel (by decide)
  refine wccm_borelRankTwoTop_of_rankTwo M (wccm_isPerfect_of_lieModel_PSL3 h)
    (CFSG.LieType.Simplicity.fam_PSL_simplicity M 3 2 2 hSCM).2 ?_ ?_
  · exact Or.inl ⟨2, by norm_num,
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
        (Subgroup.topEquiv : ↥(⊤ : Subgroup M) ≃* M).symm hSCM⟩
  · intro V
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pdiag_twoClasses_L3 h V

theorem borelRankTwoTop_of_isSp4 {M : Type} [Group M] [Finite M] (h : IsSp4 M 2) :
    BorelRankTwoTop M := by
  have hSCM : CFSG.Open.StatedClassicalModel M .PSp 2 2 2 :=
    (h : CFSG.Blueprint.LieModel M .PSp 2 2 2).statedClassicalModel (by decide)
  refine wccm_borelRankTwoTop_of_rankTwo M (wccm_isPerfect_of_lieModel_PSp2 h)
    (CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp M 2 2 2 hSCM) ?_ ?_
  · exact Or.inr (Or.inl ⟨2, le_refl 2,
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
        (Subgroup.topEquiv : ↥(⊤ : Subgroup M) ≃* M).symm hSCM⟩)
  · intro V
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pdiag_twoClasses_Sp4 h V

end CFSG.LocalAnalysis.WeakClosure81

end
