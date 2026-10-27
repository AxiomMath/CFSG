module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4RadM3Blk

public section

namespace CFSG.Quasithin.J4Rad

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc

theorem rad_M3
    (hF : J4Facts) {R : Subgroup J}
    (hRG : R ≤ Subgroup.normalizer (V0 : Set J))
    (hN : Subgroup.normalizer (V0 : Set J) ≤ Subgroup.normalizer (R : Set J))
    (hs : Group.IsSolvable ↥R) : ¬ 9 ∣ Nat.card ↥R := by
  have hM := hF.mat
  have hle : R ≤ Subgroup.centralizer (V0 : Set J) :=
    le_centralizer_of_solvable_normal V0 NV R (V0_comm hM) (V0_sq hM) (card_V0 hM) CV_le_normalizer
      (conjAut_NV_surjective hM) hRG hN hs
  intro h9
  exact not_nine_dvd_card_centralizer_V0 hF (h9.trans (Subgroup.card_dvd_of_le hle))

end CFSG.Quasithin.J4Rad
