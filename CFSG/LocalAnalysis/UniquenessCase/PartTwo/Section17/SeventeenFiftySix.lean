module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ThirteenTwoInner
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F13
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_card_outer_of_isL3 {X : Type} [Group X] {p : ℕ} (hX : IsL3 X 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : ¬ p ∣ Nat.card (Outer X) := fun h => by
  have h12 : p ∣ 2 ^ 2 * 3 :=
    h.trans (((CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound X 3 2 2
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hX)).2.2.2.2
        (by norm_num)).trans (by decide))
  rcases (Nat.Prime.dvd_mul hp).1 h12 with h4 | h3
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3)

theorem isSimple_barImage_of_shape {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hThin : ThinList13)
    (hshape : Thin13 L ∨ (∃ n : ℕ, Even n ∧ IsU3 (Bar2 L) n) ∨ IsL3 (Bar2 L) 2) :
    IsSimpleGroup ↥(barImage D.M L) := by
  obtain ⟨e⟩ := s13_bar_equiv hL
  refine (MulEquiv.isSimpleGroup_congr e).1 ?_
  rcases hshape with hthin | ⟨n, -, hU⟩ | hL3
  · exact (s13_list_bar hThin D hL hthin).1
  · exact s13_isSimple_of_isU3 hU
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL3

theorem mem_sup_centralizer_barImage_of_shape {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) {p k : ℕ}
    (hp : Hyp1754 D p)
    (hshape : Thin13 L ∨ (∃ n : ℕ, Even n ∧ IsU3 (Bar2 L) n) ∨ IsL3 (Bar2 L) 2)
    (hL3inner : IsL3 (Bar2 L) 2 → p ≠ 3) {y : Bar2 D.M}
    (hcomm : y ∈ commutator (Bar2 D.M)) (hypow : y ^ p ^ k = 1) :
    y ∈ barImage D.M L ⊔ Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M)) := by
  haveI : (barImage D.M L).Normal := s13_barImage_normal (hp.2 L hL).1
  obtain ⟨e⟩ := s13_bar_equiv hL
  rcases hshape with hthin | ⟨n, heven, hU⟩ | hL3
  · exact s13_commutator_le_sup_centralizer _ (uc22p22u_outAbelian_thin hThin hCyc D hL hthin)
      hcomm
  · exact s13_commutator_le_sup_centralizer _
      (s13_outAbelian_of_mulEquiv e (s13_outAbelian_of_isU3_even hL.2.2 hU heven)) hcomm
  · have hpp := D.sig_prime p hp.1
    refine CFSG.AGLEmbedding.mem_sup_centralizer_of_not_dvd_card_outer hpp.1
      (not_dvd_card_outer_of_isL3 (CFSG.Blueprint.LieModel.of_mulEquiv e hL3) hpp.1 hpp.2
        (hL3inner hL3)) ?_ hypow
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top _

theorem shape_of_hyp1754 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} (hp : Hyp1754 D p)
    (h33 : R17_33_2At D V₀ V) :
    ∀ L ∈ calC D.M, Thin13 L ∨ (∃ n : ℕ, Even n ∧ IsU3 (Bar2 L) n) ∨ IsL3 (Bar2 L) 2 := by
  intro L hL
  rcases (hp.2 L hL).2 with hthin | ⟨n, hU⟩ | hL3
  · exact Or.inl hthin
  · obtain ⟨k, rfl⟩ := h33 L n hL (uc22p22d_isSU3_of_isU3 hL.2.2 hU)
    refine Or.inr (Or.inl ⟨2 ^ k, Nat.even_pow.2 ⟨even_two, ?_⟩, hU⟩)
    rintro rfl
    have := s13_two_le_of_isU3 hU
    norm_num at this
  · exact Or.inr (Or.inr hL3)

theorem seventeen_fiftysix (D : Data G) (V₀ V : Subgroup G) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    (h638 : UC6.R6_38 D) (h33 : R17_33_2At D V₀ V) :
    R17_56At D V₀ V := by
  intro p hp
  by_cases h2 : p = 3 ∧ ∃ L ∈ calC D.M, IsL3 (Bar2 L) 2
  · exact Or.inr h2
  left
  have hpp : p.Prime := (D.sig_prime p hp.1).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp.1).2
  have hshape := shape_of_hyp1754 D hp h33
  have htop : CFSG.GH74.GLS.oResidual p (Bar2 D.M) = ⊤ :=
    uc22p21c_oResidual_bar_eq_top hpp (h638 p hpp hp2 (Or.inl hp.1))
  have hns : s13_NormalSimple (Bar2 D.M) := by
    intro J hJ
    obtain ⟨L, hL, rfl⟩ := s13_exists_calC_of_component D.M hJ
    exact ⟨s13_barImage_normal (hp.2 L hL).1, isSimple_barImage_of_shape hL hThin (hshape L hL)⟩
  rw [show Lp D p = F13.Lp D.M p from rfl, sp_eq_f13Sp D p]
  refine opp_eq_Lp_sup_Sp_of_inner hpp hp2 hns fun x hxM hx J hJ => ?_
  obtain ⟨k, hk⟩ := hx
  obtain ⟨L, hL, rfl⟩ := s13_exists_calC_of_component D.M hJ
  have hπ := s13_Thirteen2_pow_bar hxM hk
  exact mem_sup_centralizer_barImage_of_shape hL hThin hCyc hp (hshape L hL)
    (fun h hp3 => h2 ⟨hp3, L, hL, h⟩)
    (uc22p21c_mem_commutator_of_oResidual_eq_top htop (orderOf_dvd_of_pow_eq_one hπ)) hπ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
