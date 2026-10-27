module

public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsD
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch7Elim

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

section L825C

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem isOver_autI_82 (hV : IsElemAbelian 2 (fsuV T I))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L) :
    Mathieu.IsOver (autI hV (fsuL0 T L)) (autI hV ⊤) :=
  ⟨autI_fsuL0_le hV, autI_top_le_normalizer hV hNM⟩

theorem tab_82 (h741 : Stmt7_4_1) (htab : HTab82) (hyp : Hyp7_0_2 G T L I)
    (h731 : Hyp7_3_1 T L I) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hV : IsElemAbelian 2 (fsuV T I))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L) [IsMulCommutative ↥(fsuV T I)] :
    (∀ n : ℕ, Row711L3Nine T L I n →
      CFSG.Open.pRank 2 (autI hV ⊤) ≤ 4 * n ∧ ((4 * n : ℕ) : ℕ∞) ≤ rParam (fsuV T I) ∧
        (n = 1 → (5 : ℕ∞) ≤ alphaE (autI hV ⊤)) ∧ ((4 * n : ℕ) : ℕ∞) ≤ betaH (autI hV ⊤)) ∧
    (Row711M22Code T L I →
      CFSG.Open.pRank 2 (autI hV ⊤) ≤ 5 ∧ (6 : ℕ∞) ≤ rParam (fsuV T I)) ∧
    (Row711M24Code T L I →
      CFSG.Open.pRank 2 (autI hV ⊤) ≤ 6 ∧ (6 : ℕ∞) ≤ rParam (fsuV T I) ∧
        (7 : ℕ∞) ≤ alphaE (autI hV ⊤) ∧ (6 : ℕ∞) ≤ betaH (autI hV ⊤)) := by
  have hL0 : fsuL0 T L = L := fsuL0_eq_of_le_normalizer hTL
  have hML : fsuM T L ≤ Subgroup.normalizer (L : Set G) := by
    show Subgroup.normalizer (fsuL0 T L : Set G) ≤ _
    rw [hL0]
  have hr := h741 G T L I hyp h731 hML hV
  obtain ⟨hT9, hT22, hT24⟩ := htab (IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (autI hV ⊤)
    (isOver_autI_82 hV hNM)
  refine ⟨fun n hn => ?_, fun hrow => ?_, fun hrow => ?_⟩
  · obtain ⟨hm2, hβ, hα1, hα⟩ := hT9 n hn.1 hn.2
    refine ⟨hm2, le_trans ?_ hr, hα1, hβ⟩
    refine le_min ?_ hβ
    rcases Nat.lt_or_ge 1 n with h1 | h1
    · rw [hα h1]
      exact le_top
    · have hn1 : n = 1 := le_antisymm h1 hn.1
      subst hn1
      exact le_trans (by norm_num) (hα1 rfl)
  · obtain ⟨hm2, hβ, hα⟩ := hT22 hrow
    exact ⟨hm2, le_trans (le_min hα hβ) hr⟩
  · obtain ⟨hm2, hβ, hα⟩ := hT24 hrow
    exact ⟨hm2, le_trans (le_min (le_trans (by norm_num) hα) hβ) hr, hα, hβ⟩

theorem rParam_sub_wParam_le_82 (hyp : Hyp7_0_2 G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L) {A : Subgroup G}
    (hA : IsWOffender T (fsuV T I) A) :
    rParam (fsuV T I) - wParam T (fsuV T I) ≤ ((rk ↥(autI hV A) : ℕ) : ℕ∞) := by
  obtain ⟨g, rfl, hg⟩ := hA
  exact e3_28_three hV (hypE322_of_fsu hyp.fsu hV hN) (hypE324_of_hyp702 hyp hV hNM) hg

theorem card_lt_of_not_ff_82 (hyp : Hyp7_0_2 G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L)
    {B : Subgroup (MulAut (IntMod (fsuV T I) hV))} (hB : B ≤ autI hV ⊤) (hB1 : B ≠ ⊥)
    (hBe : IsElemAbelian2 B) :
    Nat.card B * Nat.card ↥(fixV B) < Nat.card (IntMod (fsuV T I) hV) := by
  by_contra hle
  push Not at hle
  exact not_isFFModule_of_hyp702 hyp hV hNM ⟨B, hB, hB1, hBe, hle⟩

end L825C

end CFSG.Quasithin.H13
