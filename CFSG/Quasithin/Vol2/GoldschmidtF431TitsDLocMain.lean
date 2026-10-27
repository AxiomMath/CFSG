module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsDClause

public section

namespace CFSG.Quasithin.H13.F431.TitsD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.RuType
  CFSG.Quasithin.LieSetting CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.Sporadic.Schreier.Tits
  CFSG.Quasithin.TitsGeo CFSG.Quasithin.H13.F431.TwoF4

set_option linter.unusedSectionVars false


theorem titsLocalCent : TitsLocalCent := by
  intro G _ _ H₁ H₂ e hcz
  have hβ := clauseβD_faithful e
  have hε : Function.Injective (H₁ ⊔ H₂).subtype := Subtype.val_injective
  have hzam := amalgamMap_zD e
  have htam := amalgamMap_tD e
  have hrb1 := le_range_bOneD e
  have hrb2 := range_bTwo_leD e
  set b1 := bOne titsSetting.hι (clauseβD e) (H₁ ⊔ H₂).subtype with hb1
  set b2 := bTwo titsSetting.hι (clauseβD e) (H₁ ⊔ H₂).subtype with hb2
  have hb : Subgroup.centralizer ({amalgamMap b1 b2 (thetaD zD)} : Set G) ≤ b1.range := by
    rw [hzam]
    exact hcz.trans hrb1
  have hC := fComp titsSetting.hι (clauseβD e) hβ _ hε
  have hnc := F431LieI.not_conj_of_card titsD_F431LieI_G0 hC hb not_three_dvd_card_Mb1_D
    three_dvd_card_cent_G0_D
  have : Finite titsSetting.ι.G0 := Finite.of_equiv _ thetaD.toEquiv
  have h442 := loc442 titsD_Loc442Datum_G0 hC hb hnc
  rw [htam] at h442
  exact h442.trans hrb2

end CFSG.Quasithin.H13.F431.TitsD
