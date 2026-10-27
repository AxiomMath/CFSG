module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K318Mit
public import CFSG.LocalAnalysis.UniquenessCase.UC22K318Red
import CFSG.LocalAnalysis.UniquenessCase.UC22K318Cases
import CFSG.LocalAnalysis.UniquenessCase.UC22K318Dich
import CFSG.LocalAnalysis.UniquenessCase.UC22K318Even

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K318

open Subgroup CFSG.Open CFSG.RepresentationTheory
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.SubgroupLists (MitchellPartThree)
open CFSG.LocalAnalysis.UniquenessCase.UC6.K318 (exists_range_quotient_equiv)
open CFSG.LocalAnalysis.ComponentInitial (statedClassicalModel_psl_two_five_of_alternating_five)

variable {L : Type} [Group L] [Finite L]


theorem k318s_of_irreducible_four (hIII : MitchellPartThree) [Group.IsPerfect L]
    {X : Subgroup L} [X.Normal] (hXs : Group.IsSolvable X) (hs : IsSimpleGroup (L ⧸ X))
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hrank : CFSG.Open.pRank q X ≤ 3)
    {φ : L →* GL (Fin 4) (ZMod q)} (hφ : φ.ker ≤ X) (hirr : IsIrreducibleMatrixRep φ)
    (hcs : CriticalSection X q 4 φ) :
    ((∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (LieModel (L ⧸ X) .PSL 2 p 1 ∨ LieModel (L ⧸ X) .PSL 3 p 1)) ∨
        IsAlt (L ⧸ X) 6 ∨ IsAlt (L ⧸ X) 7 ∨
        (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (LieModel (L ⧸ X) .PSp 2 p 1 ∨ LieModel (L ⧸ X) .PSL 2 p 2) ∧
          CFSG.Open.pRank p X = 3 ∧ 3 < CFSG.Open.pRank p (⊤ : Subgroup L))) ∧
      2 ∣ Nat.card X := by
  classical
  have hq : q.Prime := Fact.out
  obtain ⟨τ, c, hτc, hτS, hX3, hD⟩ := exists_sympSection hrank hcs
  obtain ⟨hRn, ⟨e⟩⟩ := exists_range_quotient_equiv φ X hφ
  haveI : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have hRs : Group.IsSolvable (X.map φ.rangeRestrict) := by
    haveI := hXs
    exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective φ.rangeRestrict X)
  have hsP : IsSimpleGroup (φ.range ⧸ X.map φ.rangeRestrict) :=
    (MulEquiv.isSimpleGroup_congr e).2 hs
  have hirrP : IsIrreducibleMatrixRep φ.range.subtype := fun W hW =>
    hirr W fun g w hw => hW ⟨φ g, g, rfl⟩ w hw
  rcases le_center_or_not_twoCore_le hirrP (X.map φ.rangeRestrict) hRs with hZ | h2
  ·
    obtain ⟨hRZ, hqs⟩ := eq_center_of_le_center hRs hsP hZ
    obtain ⟨e', -⟩ := range_comp_equiv τ φ
    have hqs' : CFSG.IsQuasisimple (τ.toMonoidHom.comp φ).range :=
      (CFSG.IsQuasisimple.congr e').1 hqs
    have hPS : (τ.toMonoidHom.comp φ).range ≤ StatedSp 2 (ZMod q) := by
      rintro _ ⟨g, rfl⟩
      exact hτS g
    have eS : (τ.toMonoidHom.comp φ).range ⧸ center (τ.toMonoidHom.comp φ).range ≃* L ⧸ X :=
      (QuotientGroup.congr (center φ.range) (center (τ.toMonoidHom.comp φ).range) e'
        (Subgroup.map_center_eq e')).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hRZ).symm.trans e)
    obtain ⟨h2Z, hlist⟩ := list_of_quasisimple hIII hq2 hPS hqs' eS
    have h2X : 2 ∣ Nat.card X := by
      have h1 : Nat.card (center (τ.toMonoidHom.comp φ).range) = Nat.card (center φ.range) := by
        rw [← Subgroup.map_center_eq e']
        exact Subgroup.card_map_of_injective e'.injective
      rw [h1, ← hRZ] at h2Z
      exact h2Z.trans (Subgroup.card_map_dvd X _)
    refine ⟨?_, h2X⟩
    rcases hlist with (h | h | h) | ⟨hP, hm⟩ | ⟨⟨eSL⟩, hm⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨q, hq, hq2, Or.inl hm, hX3, three_lt_pRank_of_sp4 hq2 hD hP⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨q, hq, hq2, Or.inr hm, hX3,
        three_lt_pRank_of_sl2 hq2 hD hPS (isIrreducibleOn_comp hτc hirr) eSL⟩))
  ·
    have h2X : 2 ∣ Nat.card X := by
      have hne : CFSG.pCore 2 (X.map φ.rangeRestrict) ≠ ⊥ := by
        intro hbot
        apply h2
        rw [hbot, Subgroup.map_bot]
        exact bot_le
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X.map φ.rangeRestrict)).exists_card_eq
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero, Subgroup.card_eq_one] at hk
        exact hne hk
      have h2T : 2 ∣ Nat.card (CFSG.pCore 2 (X.map φ.rangeRestrict)) := by
        rw [hk]
        exact dvd_pow_self 2 hk0
      exact h2T.trans ((Subgroup.card_subgroup_dvd_card _).trans (Subgroup.card_map_dvd X _))
    refine ⟨?_, h2X⟩
    rcases alt_of_not_twoCore_le hq2 hirrP _ hRs hsP h2 with h5 | h6
    · obtain ⟨e5⟩ := h5
      exact Or.inl ⟨5, Nat.prime_five, by norm_num, Or.inl (Or.inl ⟨by decide,
        statedClassicalModel_psl_two_five_of_alternating_five _ ⟨e.symm.trans e5⟩⟩)⟩
    · obtain ⟨e6⟩ := h6
      exact Or.inr (Or.inl ⟨e.symm.trans e6⟩)

end CFSG.LocalAnalysis.UniquenessCase.UC22.K318
