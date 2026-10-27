module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComponentPermutesGeneric
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKSchur
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKNotJ2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEight
public import CFSG.Quasithin.EmptyFaithful.R3cBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem list880_of_isAlt_eight {X : Type} [Group X] (h : IsAlt X 8) : F08.List880 X := by
  unfold F08.List880
  tauto

theorem list880_of_isAlt_seven {X : Type} [Group X] (h : IsAlt X 7) : F08.List880 X := by
  unfold F08.List880
  tauto

theorem list880_of_isA7Z3 {X : Type} [Group X] (h : F08.IsA7Z3 X) : F08.List880 X := by
  unfold F08.List880
  tauto

theorem list880_of_isAlt_six {X : Type} [Group X] (h : IsAlt X 6) : F08.List880 X := by
  unfold F08.List880
  tauto

theorem list880_of_isA6Z3 {X : Type} [Group X] (h : F08.IsA6Z3 X) : F08.List880 X := by
  unfold F08.List880
  tauto

theorem not_isSpor_J2_of_isAlt_six_or_isA6Z3 {X : Type} [Group X]
    (h : IsAlt X 6 ∨ F08.IsA6Z3 X) : ¬ IsSpor X .J2 := by
  intro hJ2
  obtain ⟨eJ⟩ := hJ2
  have hJ : Nat.card X = 604800 := by
    rw [Nat.card_congr eJ.toEquiv]
    change Nat.card CFSG.Blueprint.NativeSporadic.J2 = 604800
    exact CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2
  have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 :=
    CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin 4
  rcases h with hAlt | hA6Z3
  · obtain ⟨e⟩ := hAlt
    have hX : Nat.card X = 360 := by
      rw [Nat.card_congr e.toEquiv]
      exact h360
    omega
  · obtain ⟨-, hz, hquot⟩ := hA6Z3
    obtain ⟨e⟩ := hquot
    have hXq : Nat.card (X ⧸ Subgroup.center X) = 360 := by
      rw [Nat.card_congr e.toEquiv]
      exact h360
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
    rw [hXq, hz] at hcard
    omega

theorem k_eq_one_of_alt_six {D : Data G} (h880 : F08.R880 D)
    {L : Subgroup G} (hL : L ∈ calC D.M)
    (hshape : Nonempty (BarO2Z17 L ≃* alternatingGroup (Fin 6))) : D.k = 1 := by
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20p_odd_center_bar2 ↥L
  have hquot : Nonempty ((Bar2 L ⧸ Subgroup.center (Bar2 L)) ≃*
      alternatingGroup (Fin 6)) := centerQuot_of_barO2Z hL hshape
  obtain ⟨eq⟩ := hquot
  rcases s15k_schur_alt_six hq hodd ⟨eq⟩ with hAlt | hA6Z3
  · exact k_eq_one_of_list880 h880 hL (list880_of_isAlt_six hAlt)
      (not_isSpor_J2_of_isAlt_six_or_isA6Z3 (Or.inl hAlt))
  · exact k_eq_one_of_list880 h880 hL (list880_of_isA6Z3 hA6Z3)
      (not_isSpor_J2_of_isAlt_six_or_isA6Z3 (Or.inr hA6Z3))

theorem seventeen_five_n_ge_nine {D : Data G} {V₀ V : Subgroup G} {hV : Hyp125 D V₀ V}
    (h17_1 : R17_1At D V₀ V hV) (h82 : F08.R82 D) {L : Subgroup G}
    (hL : L ∈ calC D.M) {n : ℕ} (hn : 9 ≤ n)
    (e : BarO2Z17 L ≃* alternatingGroup (Fin n)) : False := by
  have hshape : Nonempty ((Bar2 L ⧸ Subgroup.center (Bar2 L)) ≃*
      alternatingGroup (Fin n)) := centerQuot_of_barO2Z hL ⟨e⟩
  obtain ⟨es⟩ := hshape
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20p_odd_center_bar2 ↥L
  obtain ⟨eA⟩ := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1415.alt_of_center_odd
    hL.2.2 (by omega) es hodd
  have hbar : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eA]
    exact CFSG.SectionRank.three_le_pRank_alternating hn
  have hm3L : 2 < CFSG.Open.pRank 3 L := by
    rw [CFSG.Quasithin.R3c.pRank_three_eq_pCore_quotient L]
    omega
  have hHyp : F08.Hyp81 D.M L :=
    ⟨hL.1, hL.2.1, hm3L, Or.inl (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hL.2.2)⟩
  have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := h82 L hHyp
  have hk : D.k = 1 :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Data.k_eq_one_of_isStronglyPEmbedded D hstr
  exact false_of_k_eq_one_of_permutes h17_1 hk
    (exists_permutes_three_of_alt_ge_eight hL (by omega) ⟨es⟩)

theorem seventeen_five_n_eq_eight {D : Data G} {V₀ V : Subgroup G} {hV : Hyp125 D V₀ V}
    (h17_1 : R17_1At D V₀ V hV) (h880 : F08.R880 D) {L : Subgroup G}
    (hL : L ∈ calC D.M) (e : BarO2Z17 L ≃* alternatingGroup (Fin 8)) : False := by
  have hshape : Nonempty ((Bar2 L ⧸ Subgroup.center (Bar2 L)) ≃*
      alternatingGroup (Fin 8)) := centerQuot_of_barO2Z hL ⟨e⟩
  obtain ⟨es⟩ := hshape
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20p_odd_center_bar2 ↥L
  obtain ⟨eA⟩ := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1415.alt_of_center_odd
    hL.2.2 (by norm_num) es hodd
  have hlist : F08.List880 (Bar2 L) := list880_of_isAlt_eight ⟨eA⟩
  have hJ : ¬ IsSpor (Bar2 L) .J2 := by
    intro hJ2
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.rNotJ2_holds (Bar2 L) hJ2
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨eA⟩)))))
  have hk : D.k = 1 := k_eq_one_of_list880 h880 hL hlist hJ
  exact false_of_k_eq_one_of_permutes h17_1 hk
    (exists_permutes_three_of_alt_ge_eight hL (by norm_num) ⟨es⟩)

theorem seventeen_five_n_eq_seven
    (hKA1 : Inputs1719.K_A7Permuting) {D : Data G} {V₀ V : Subgroup G} {hV : Hyp125 D V₀ V}
    (h17_1 : R17_1At D V₀ V hV) (h880 : F08.R880 D) {L : Subgroup G}
    (hL : L ∈ calC D.M) (e : BarO2Z17 L ≃* alternatingGroup (Fin 7)) : False := by
  have hshape : Nonempty ((Bar2 L ⧸ Subgroup.center (Bar2 L)) ≃*
      alternatingGroup (Fin 7)) := centerQuot_of_barO2Z hL ⟨e⟩
  obtain ⟨es⟩ := hshape
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20p_odd_center_bar2 ↥L
  have hcover := s15k_schur_alt_seven hL.2.2 hodd ⟨es⟩
  have hk : D.k = 1 := by
    rcases hcover with hA7 | hA7Z3
    · exact k_eq_one_of_list880 h880 hL (list880_of_isAlt_seven hA7) (by
        intro hJ2
        exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.rNotJ2_holds (Bar2 L) hJ2
          (Or.inr (Or.inr (Or.inl hA7))))
    · exact k_eq_one_of_list880 h880 hL (list880_of_isA7Z3 hA7Z3) (by
        intro hJ2
        exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.rNotJ2_holds (Bar2 L) hJ2
          (Or.inr (Or.inr (Or.inr (Or.inl hA7Z3)))))
  exact false_of_k_eq_one_of_permutes h17_1 hk
    (exists_permutes_three_of_alt_seven hKA1 hL ⟨es⟩)

theorem seventeen_five_of_no_A6 {D : Data G} {V₀ V : Subgroup G}
    {hV : Hyp125 D V₀ V} (h17_1 : R17_1At D V₀ V hV)
    (h82 : F08.R82 D) (h880 : F08.R880 D)
    (hKA1 : Inputs1719.K_A7Permuting)
    (h6 : ∀ L ∈ calC D.M,
      ¬ Nonempty (BarO2Z17 L ≃* alternatingGroup (Fin 6))) :
    R17_5At D V₀ V := by
  intro L hL n hn hA
  obtain ⟨e⟩ := hA
  by_cases hn6 : n = 6
  · exact h6 L hL ⟨hn6 ▸ e⟩
  by_cases hn7 : n = 7
  · exact seventeen_five_n_eq_seven hKA1 h17_1 h880 hL (hn7 ▸ e)
  by_cases hn8 : n = 8
  · exact seventeen_five_n_eq_eight h17_1 h880 hL (hn8 ▸ e)
  · exact seventeen_five_n_ge_nine h17_1 h82 hL (by omega) e

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

