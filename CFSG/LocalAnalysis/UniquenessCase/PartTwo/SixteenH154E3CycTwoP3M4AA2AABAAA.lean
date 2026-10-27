module

public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup

variable {W : Type} [CommGroup W]

theorem s16h_e3_CycTwoP3M4AA2AABAAA_aut_card
    [Finite W] (hexp : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 4) :
    Nat.card (MulAut W) = 20160 := by
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (n := 4)
    (fun a b => mul_comm a b) hexp hcard
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e,
    CFSG.SectionRank.Ccomm.card_GL_zmod]
  decide

theorem s16h_e3_CycTwoP3M4AA2AABAAA_not_three_cube_dvd
    [Finite W] (hexp : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 4) :
    ¬ 3 ^ 3 ∣ Nat.card (MulAut W) := by
  rw [s16h_e3_CycTwoP3M4AA2AABAAA_aut_card hexp hcard]
  norm_num

theorem s16h_e3_CycTwoP3M4AA2AABAAA_pRank_le_two
    [Finite W] (hexp : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 4)
    (A : Subgroup (MulAut W)) : CFSG.Open.pRank 3 A ≤ 2 := by
  refine CFSG.SectionRank.pRank_le (p := 3) (by norm_num) (fun E _ hE => ?_)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.Open.IsElemAbelian.isPGroup hE)
  have hdvd : 3 ^ k ∣ Nat.card (MulAut W) := hk ▸ Subgroup.card_subgroup_dvd_card E
  have hk2 : k ≤ 2 := by
    by_contra h
    exact s16h_e3_CycTwoP3M4AA2AABAAA_not_three_cube_dvd hexp hcard
      ((pow_dvd_pow 3 (by omega)).trans hdvd)
  calc Nat.card ↥E = 3 ^ k := hk
    _ ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2

theorem s16h_e3_CycTwoP3M4AA2AABAAA_exists_elemAbelian
    [Finite W] (hexp : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 4)
    {A : Subgroup (MulAut W)} (h2 : 2 ≤ CFSG.Open.pRank 3 A) :
    ∃ E : Subgroup (MulAut W), E ≤ A ∧ IsElemAbelianOfRank 3 2 ↥E := by
  have hle := s16h_e3_CycTwoP3M4AA2AABAAA_pRank_le_two hexp hcard A
  have heq : CFSG.Open.pRank 3 A = 2 := le_antisymm hle h2
  obtain ⟨E, hEA, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) A
  refine ⟨E, hEA, ?_⟩
  rw [heq] at hEcard
  exact CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 3) (n := 2)
    (fun a b => hEel.1.is_comm.comm a b) (fun x => Subtype.ext (hEel.2 x x.2)) hEcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
