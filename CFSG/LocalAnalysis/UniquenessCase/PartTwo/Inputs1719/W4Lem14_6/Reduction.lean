module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Bender
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Config
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsNoO2Sixteen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem false_of_isSz
    (hSz : K_SzThirtyTwoMinM) {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L X : Subgroup (MulAut W)} (hO2 : O2Trivial Y) (hB : IsBasicModule Y)
    (hL : IsComponentOf L Y) (hX : X = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom)
    (h5 : UC22.IsSz ↥L 5) (hfix : fixV X = ⊥) (hm : 3 < E3.mParam Y)
    (hle : E3.mParam Y ≤ bParam X Y + 2) : False := by
  obtain ⟨hmn, hsum0, I, hI, hIm⟩ :=
    case2_of_hyps hW hO2 hB hL hX hfix (Or.inr ⟨h5, rfl⟩) hm hle
  have hs : IsSimpleGroup ↥L := UC22.uc22p22r_lieModel_isSimple_twistedB2 h5
  obtain ⟨hSN, hnorm, hirr, -, -, hmN⟩ := setup_of_case2 hW hL hX hfix hsum0 hI hIm
  have h8 := hSz ↥I (fun u => Subtype.ext (hW u)) (autSub Y I) (autSub L I) hSN hnorm
    (lieModel_autSub hL hX hfix hsum0 hs hI h5) hirr
  omega

theorem false_of_isL2
    (hL28 : K_L28SmallM) {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L X : Subgroup (MulAut W)} (hO2 : O2Trivial Y) (hB : IsBasicModule Y)
    (hL : IsComponentOf L Y) (hX : X = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom)
    (h3 : UC22.IsL2 ↥L 3) (hfix : fixV X = ⊥) (hm : 3 < E3.mParam Y)
    (hle : E3.mParam Y ≤ bParam X Y + 2) : False := by
  obtain ⟨hmn, hsum0, I, hI, hIm⟩ :=
    case2_of_hyps hW hO2 hB hL hX hfix (Or.inl ⟨h3, rfl⟩) hm hle
  have hs : IsSimpleGroup ↥L :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h3
  obtain ⟨hSN, hnorm, hirr, hrk, hmul, hmN⟩ := setup_of_case2 hW hL hX hfix hsum0 hI hIm
  obtain ⟨hm3, hcase⟩ := hL28 ↥I (fun u => Subtype.ext (hW u)) (autSub Y I) (autSub L I) hSN
    hnorm (lieModel_autSub hL hX hfix hsum0 hs hI h3) hirr
  have h3r : 3 * rk ↥(commV L) ≤ E3.mParam (autSub Y I) * rk ↥(commV L) :=
    Nat.mul_le_mul_right _ hm3
  have hY5 : E3.mParam Y * rk ↥I ≤ 5 * rk ↥I := Nat.mul_le_mul_right _ hmn
  have hd := dMinDeg_eq_six_of_isL2_three h3
  rcases hcase (by omega) with ⟨hrk6, t, htS, ht2, ht3⟩ | ⟨hrk8, ha⟩
  · have hLI : commV L = I := commV_eq_of_rk_lt_dMinDeg hW hL hI (by
      rw [hd]
      rw [hrk6] at hY5 hmul ⊢
      omega)
    obtain ⟨s, hsL, hs2, hsr⟩ := exists_involution_of_autSub hL hs hsum0 hI hLI htS ht2
    have := CFSG.Quasithin.Asc81c.Pf.mParam_le_of_orderOf_two (hL.1 hsL) hs2
    omega
  · have hLI : commV L = I := commV_eq_of_rk_lt_dMinDeg hW hL hI (by
      rw [hd]
      rw [hrk8] at hY5 hmul ⊢
      omega)
    have haY := aParam_le_one_of_summand hW hL
      (Thm14_5.isDirSumOver_commV_of_autQuot_bot hsum0) hLI ha
    have := Inputs1719.bParam_le_aParam (X := X) (Y := Y)
    omega

theorem w4Lem14_6aSmall_of_kfacts
    (hL28 : K_L28SmallM) (hSz : K_SzThirtyTwoMinM) : W4Lem14_6aSmall := by
  intro W _ _ hW Y L X _ hO2 hB hL hX hshape _ hfix hm hle
  rcases hshape with h3 | h5
  · exact false_of_isL2 hL28 hW hO2 hB hL hX h3 hfix hm hle
  · exact false_of_isSz hSz hW hO2 hB hL hX h5 hfix hm hle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
