module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZResAlg
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZResSum
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZResTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZWorld

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16h_L3World_of_row {W : Type} [CommGroup W] [Finite W] {A L : Subgroup (MulAut W)}
    {t : MulAut W} (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowL3 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))
    (hk : ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
      ∃ g ∈ A ⊓ Subgroup.normalizer (L : Set (MulAut W)), I₂ = I₁.map g.toMonoidHom) :
    s16h_L3World (autSub (A ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commSub ⊤ L))
      (autSub L (commSub ⊤ L)) := by
  obtain ⟨-, -, hL3, -⟩ := id h
  obtain ⟨helem, hle, hnorm, hquasi, hsl3, hcomm, hfaith⟩ := s16h_L3_res_algebra hc hL3
  exact ⟨helem, hle, hnorm, hquasi, hsl3, hcomm, s16h_L3_res_sum h, hfaith,
    s16h_L3_res_trans hk⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
