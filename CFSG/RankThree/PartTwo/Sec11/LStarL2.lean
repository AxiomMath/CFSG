module

public import CFSG.RankThree.PartTwo.Sec11.LStar
public import CFSG.RankThree.PartTwo.Sec8.Outer
public import CFSG.RankThree.PartTwo.KFacts.K72LStar
public import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
public import CFSG.RankThree.PartTwo.KFacts.K72List
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec10.HWNormalizes

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.GorensteinWalter

theorem exists_threeElement_moving_of_psl2 (h97 : Sec9.Item97) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R : Subgroup G}
    (h : Sec9.Hyp91 G A c L a R) {K : Type} [Field K] [Finite K] (h3K : (3 : K) ≠ 0)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* PSL2 K) :
    ∃ l ∈ L ⊓ Subgroup.normalizer (A : Set G), (∃ k : ℕ, l ^ 3 ^ k = 1) ∧
      ∃ x ∈ A, l * x * l⁻¹ ≠ x := by
  have hAe := h.mem_partTwoF.1
  obtain ⟨d, hdL, hd3, hA⟩ := Sec10.exists_inf_eq_zpowers h97 h
  have hdAL : d ∈ A ⊓ L := by
    rw [hdL]
    exact Subgroup.mem_zpowers d
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hd3
    exact absurd hd3 (by norm_num)
  have hout : Sec4.InducesOuterTheta a L := h.toHyp81.inducesOuterTheta
  have ha := KFacts.inducesKind_field_of_pow_three L (hAe.2 a h.a_mem) hout e
  have hsc : c ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
    rw [h.sectionCentralizer_eq]
    exact Subgroup.mem_zpowers c
  exact KFacts.exists_threeElement_moving_of_inducesKindPSL2 h3K hAe h.mem_A h.a_mem hdAL.1 hA
    hsc.2 hdAL.2 hd1 e ha

@[expose] def LStarTransvectionL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y →
      (∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi (L ⧸ aschbacherSolvableCore 3 L) 2 (3 * n)) →
      ∃ l ∈ L ⊓ Subgroup.normalizer (A : Set G), (∃ k : ℕ, l ^ 3 ^ k = 1) ∧
        ∃ x ∈ A, l * x * l⁻¹ ≠ x

theorem lStarTransvection_of (h97 : Sec9.Item97) (hL3 : LStarTransvectionL3) :
    LStarTransvection := by
  intro G _ _ A c L a R Y h
  rcases h.isList1016 with ⟨p, e, _, hp, -, ⟨eq⟩⟩ | ⟨n, -, ⟨eq⟩⟩ | hL
  · exact exists_threeElement_moving_of_psl2 h97 h.toHyp91
      (KFacts.three_ne_zero_galoisField (by omega) _) (eq.trans (Sec4.projSLEquivPSL _))
  · exact exists_threeElement_moving_of_psl2 h97 h.toHyp91
      (KFacts.three_ne_zero_galoisField (by norm_num) _) (eq.trans (Sec4.projSLEquivPSL _))
  · exact hL3 G A c L a R Y h hL

theorem item115_of_lStarL3 (h97 : Sec9.Item97) (hL3 : LStarTransvectionL3) : Item115 :=
  item115_of_lStar h97 (Sec10.hwNormalizesL_of h97) (lStarTransvection_of h97 hL3)

end CFSG.RankThree.PartTwo.Sec11
