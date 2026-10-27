module

public import CFSG.GroupTheory.PGroup.ElemAbelianSq
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Sporadic.Schreier.TitsOuterTwo
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Assembly
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Parity
public import CFSG.Sporadic.Schreier.PairJ2Pairs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor)
open CFSG.Blueprint (LieModel)

theorem not_five_dvd_card_outer_of_isSpor_J2
    {X : Type} [Group X] [Finite X] (h : IsSpor X .J2) :
    ¬ 5 ∣ Nat.card (Outer X) := by
  obtain ⟨e⟩ := h
  rw [CFSG.SignalizerFunctorTheorem.CatalogBridge.card_outer_eq_of_mulEquiv e]
  haveI : Finite (Carrier .J2) := Finite.of_equiv X e.toEquiv
  haveI : Finite (MulAut (Carrier .J2)) :=
    Finite.of_injective (fun α : MulAut (Carrier .J2) => (α : Carrier .J2 → Carrier .J2))
      DFunLike.coe_injective
  haveI : Finite (Outer (Carrier .J2)) :=
    Finite.of_surjective (QuotientGroup.mk' (inner (Carrier .J2))) QuotientGroup.mk_surjective
  haveI : Nonempty (Outer (Carrier .J2)) :=
    ⟨QuotientGroup.mk' (inner (Carrier .J2)) 1⟩
  have h2 : Nat.card (Outer (Carrier .J2)) ≤ 2 :=
    CFSG.Sporadic.Schreier.AT_J2_Schreier.1
  intro h5
  have h5le : 5 ≤ Nat.card (Outer (Carrier .J2)) := Nat.le_of_dvd Nat.card_pos h5
  omega

theorem exists_elemAbelian_five_two_of_isSpor_J2
    {X : Type} [Group X] [Finite X] (h : IsSpor X .J2) :
    ∃ E : Subgroup X, CFSG.Open.IsElemAbelian 5 E ∧ Nat.card E = 25 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e⟩ := h
  haveI : Finite (Carrier .J2) := Finite.of_equiv X e.toEquiv
  obtain ⟨x, y, -, hx, hy, hxy, hcard, -⟩ :=
    CFSG.SectionRank.J2_sylow5_square_witness
  let xC : Carrier .J2 := x
  let yC : Carrier .J2 := y
  have hx' : xC ^ 5 = 1 := hx
  have hy' : yC ^ 5 = 1 := hy
  have hxy' : xC * yC = yC * xC := hxy
  have hcard' : Nat.card (Subgroup.closure ({xC, yC} : Set (Carrier .J2))) = 5 ^ 2 := hcard
  have hx1 : xC ≠ 1 := by
    intro h1
    have hle : Subgroup.closure ({xC, yC} : Set (Carrier .J2)) ≤ Subgroup.zpowers yC := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · subst z; simpa [h1] using Subgroup.one_mem (Subgroup.zpowers yC)
      · subst z; exact Subgroup.mem_zpowers yC
    have hdvd : Nat.card (Subgroup.closure ({xC, yC} : Set (Carrier .J2))) ∣
        Nat.card (Subgroup.zpowers yC) := Subgroup.card_dvd_of_le hle
    rw [hcard', Nat.card_zpowers] at hdvd
    exact (by norm_num : ¬ (5 ^ 2 ∣ 5)) (hdvd.trans (orderOf_dvd_of_pow_eq_one hy'))
  have hyX : yC ∉ Subgroup.zpowers xC := by
    intro hymem
    have hle : Subgroup.closure ({xC, yC} : Set (Carrier .J2)) ≤ Subgroup.zpowers xC := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · subst z; exact Subgroup.mem_zpowers xC
      · subst z; exact hymem
    have hdvd : Nat.card (Subgroup.closure ({xC, yC} : Set (Carrier .J2))) ∣
        Nat.card (Subgroup.zpowers xC) := Subgroup.card_dvd_of_le hle
    rw [hcard', Nat.card_zpowers] at hdvd
    exact (by norm_num : ¬ (5 ^ 2 ∣ 5)) (hdvd.trans (orderOf_dvd_of_pow_eq_one hx'))
  have hy1 : yC ≠ 1 := by
    intro h1
    exact hyX (by rw [h1]; exact Subgroup.one_mem _)
  have hxord : orderOf xC = 5 := orderOf_eq_prime hx' hx1
  have hyord : orderOf yC = 5 := orderOf_eq_prime hy' hy1
  have hXcard : Nat.card (Subgroup.zpowers xC) = 5 := by rw [Nat.card_zpowers, hxord]
  have hcomm : ∀ a ∈ Subgroup.zpowers xC, a * yC = yC * a := by
    have hxcent : xC ∈ Subgroup.centralizer ({yC} : Set (Carrier .J2)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      exact hxy'.symm
    have hgen : Subgroup.zpowers xC ≤ Subgroup.centralizer ({yC} : Set (Carrier .J2)) :=
      Subgroup.zpowers_le.mpr hxcent
    intro a ha
    exact ((Subgroup.mem_centralizer_iff.mp (hgen ha)) yC (by simp)).symm
  obtain ⟨hEel, hEcard⟩ :=
    CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute (G := Carrier .J2) (r := 5)
      (X := Subgroup.zpowers xC) hXcard hyord hyX hcomm
  refine ⟨(Subgroup.zpowers xC ⊔ Subgroup.zpowers yC).map e.symm.toMonoidHom, ?_, ?_⟩
  · exact CFSG.SectionRank.isElemAbelian_map hEel e.symm.toMonoidHom
  · rw [Subgroup.card_map_of_injective e.symm.injective, hEcard]; norm_num

section J2PRank


theorem pRank_five_eq_two_of_isSpor_J2
    {X : Type} [Group X] [Finite X] (h : IsSpor X .J2) :
    CFSG.Open.pRank 5 (⊤ : Subgroup X) = 2 := by
  obtain ⟨E, hEel, hEcard⟩ := exists_elemAbelian_five_two_of_isSpor_J2 h
  have hlow : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup X) :=
    CFSG.SectionRank.le_pRank (p := 5) (k := 2) (by norm_num) le_top hEel
      (by rw [hEcard]; norm_num)
  have hcardX : Nat.card X = 604800 := by
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J2.card_J2
  have hhigh : CFSG.Open.pRank 5 (⊤ : Subgroup X) ≤ 2 := by
    refine CFSG.HardMathSupport.Timmesfeld.SporadicRank.pRank_le_of_not_dvd
      Nat.prime_five ?_
    rw [hcardX]
    norm_num
  exact le_antisymm hhigh hlow

end J2PRank

section TitsCommon


theorem exists_elemAbelian_five_two_of_lieModel_tits
    {X : Type} [Group X] [Finite X]
    (h : LieModel X .Tits 0 2 1) :
    ∃ E : Subgroup X, CFSG.Open.IsElemAbelian 5 E ∧ Nat.card E = 25 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hree : CFSG.Blueprint.ReeTitsModel X .Tits 2 1 :=
    (CFSG.Blueprint.LieModel.reeTitsModel h (by decide)).2
  obtain ⟨K, hKfield, hKfin, hKchar, hKcard, ⟨e⟩⟩ :=
    CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model hree
  letI := hKfield
  letI := hKfin
  haveI := hKchar
  obtain ⟨x, y, -, hx, hy, hxy, hcard, -⟩ :=
    CFSG.SectionRank.Tits_sylow5_square_witness (K := K) hKcard
  let D := commutator (CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0)
  have hx1 : x ≠ 1 := by
    intro h1
    have hle : Subgroup.closure ({x, y} : Set D) ≤ Subgroup.zpowers y := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · subst z; simpa [h1] using Subgroup.one_mem (Subgroup.zpowers y)
      · subst z; exact Subgroup.mem_zpowers y
    have hdvd : Nat.card (Subgroup.closure ({x, y} : Set D)) ∣
        Nat.card (Subgroup.zpowers y) := Subgroup.card_dvd_of_le hle
    rw [hcard, Nat.card_zpowers] at hdvd
    exact (by norm_num : ¬ (5 ^ 2 ∣ 5)) (hdvd.trans (orderOf_dvd_of_pow_eq_one hy))
  have hyX : y ∉ Subgroup.zpowers x := by
    intro hymem
    have hle : Subgroup.closure ({x, y} : Set D) ≤ Subgroup.zpowers x := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · subst z; exact Subgroup.mem_zpowers x
      · subst z; exact hymem
    have hdvd : Nat.card (Subgroup.closure ({x, y} : Set D)) ∣
        Nat.card (Subgroup.zpowers x) := Subgroup.card_dvd_of_le hle
    rw [hcard, Nat.card_zpowers] at hdvd
    exact (by norm_num : ¬ (5 ^ 2 ∣ 5)) (hdvd.trans (orderOf_dvd_of_pow_eq_one hx))
  have hy1 : y ≠ 1 := by
    intro h1
    exact hyX (by rw [h1]; exact Subgroup.one_mem _)
  have hxord : orderOf x = 5 := orderOf_eq_prime hx hx1
  have hyord : orderOf y = 5 := orderOf_eq_prime hy hy1
  have hXcard : Nat.card (Subgroup.zpowers x) = 5 := by rw [Nat.card_zpowers, hxord]
  have hcomm : ∀ a ∈ Subgroup.zpowers x, a * y = y * a := by
    have hxcent : x ∈ Subgroup.centralizer ({y} : Set D) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      exact hxy.symm
    have hgen : Subgroup.zpowers x ≤ Subgroup.centralizer ({y} : Set D) :=
      Subgroup.zpowers_le.mpr hxcent
    intro a ha
    exact ((Subgroup.mem_centralizer_iff.mp (hgen ha)) y (by simp)).symm
  obtain ⟨hEel, hEcard⟩ :=
    CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute (G := D) (r := 5)
      (X := Subgroup.zpowers x) hXcard hyord hyX hcomm
  refine ⟨(Subgroup.zpowers x ⊔ Subgroup.zpowers y).map e.symm.toMonoidHom, ?_, ?_⟩
  · exact CFSG.SectionRank.isElemAbelian_map hEel e.symm.toMonoidHom
  · rw [Subgroup.card_map_of_injective e.symm.injective, hEcard]; norm_num

theorem pRank_five_eq_two_of_lieModel_tits
    {X : Type} [Group X] [Finite X]
    (h : LieModel X .Tits 0 2 1) :
    CFSG.Open.pRank 5 (⊤ : Subgroup X) = 2 := by
  obtain ⟨E, hEel, hEcard⟩ := exists_elemAbelian_five_two_of_lieModel_tits h
  have hlow : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup X) :=
    CFSG.SectionRank.le_pRank (p := 5) (k := 2) (by norm_num) le_top hEel
      (by rw [hEcard]; norm_num)
  have hree : CFSG.Blueprint.ReeTitsModel X .Tits 2 1 :=
    (CFSG.Blueprint.LieModel.reeTitsModel h (by decide)).2
  obtain ⟨K, hKfield, hKfin, hKchar, hKcard, ⟨e⟩⟩ :=
    CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model hree
  letI := hKfield
  letI := hKfin
  haveI := hKchar
  have hdvd : Nat.card X ∣ 35942400 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.SectionRank.TitsOrder.Tits_commutator_card_dvd (K := K) hKcard
  have hhigh : CFSG.Open.pRank 5 (⊤ : Subgroup X) ≤ 2 := by
    refine CFSG.HardMathSupport.Timmesfeld.SporadicRank.pRank_le_of_not_dvd
      Nat.prime_five ?_
    intro h125
    exact (by norm_num : ¬ (125 ∣ 35942400)) (h125.trans hdvd)
  exact le_antisymm hhigh hlow

end TitsCommon

section TitsOut


theorem not_five_dvd_card_outer_of_lieModel_tits
    {X : Type} [Group X] [Finite X]
    (h : LieModel X .Tits 0 2 1) :
    ¬ 5 ∣ Nat.card (Outer X) := by
  have hree : CFSG.Blueprint.ReeTitsModel X .Tits 2 1 :=
    (CFSG.Blueprint.LieModel.reeTitsModel h (by decide)).2
  obtain ⟨-, -, hO, -⟩ :=
    CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound X 2 1 hree
  rw [hO]
  norm_num

end TitsOut

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
