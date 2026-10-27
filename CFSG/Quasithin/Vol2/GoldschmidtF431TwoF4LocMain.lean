module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Clause
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4LocDatum
public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442Map

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.RuType
  CFSG.Quasithin.LieSetting CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.Sporadic.Schreier.Tits

set_option linter.unusedSectionVars false


theorem twoF4_Loc442Datum_G0 : Loc442Datum twoF4Setting.Mb1 twoF4Setting.Mb2
    (twoF4TT.map thetaM.toMonoidHom) (thetaM zM) (thetaM tM) (VM.map thetaM.toMonoidHom)
    (thetaM qM) := by
  rw [Mb1_eq, Mb2_eq]
  exact Loc442Datum.map thetaM twoF4_Loc442Datum

theorem range_bTwo_le {G : Type} [Group G] [Finite G] {H L2 : Subgroup G}
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups H L2)) :
    (bTwo twoF4Setting.hι (clauseβ e) (H ⊔ L2).subtype).range ≤ L2 := by
  rintro _ ⟨⟨x, a, rfl⟩, rfl⟩
  rw [bTwo_clause e a]
  exact (isoV2 e a).2

theorem twoF4LocalCent : TwoF4LocalCent := by
  intro G _ _ H₁ H₂ e hcz
  have hβ := clauseβ_faithful e
  have hε : Function.Injective (H₁ ⊔ H₂).subtype := Subtype.val_injective
  have hzam := amalgamMap_zM e
  have htam := amalgamMap_tM e
  have hrb1 := le_range_bOne e
  have hrb2 := range_bTwo_le e
  set b1 := bOne twoF4Setting.hι (clauseβ e) (H₁ ⊔ H₂).subtype with hb1
  set b2 := bTwo twoF4Setting.hι (clauseβ e) (H₁ ⊔ H₂).subtype with hb2
  have hb : Subgroup.centralizer ({amalgamMap b1 b2 (thetaM zM)} : Set G) ≤ b1.range := by
    rw [hzam]
    exact hcz.trans hrb1
  have hr1 : ¬ 3 ∣ Nat.card twoF4Setting.Mb1 := by
    rw [Mb1_eq, Subgroup.card_map_of_injective thetaM.injective, card_twoF4M1]
    decide
  have hr2 : 3 ∣ Nat.card (Subgroup.centralizer ({thetaM tM} : Set twoF4Setting.ι.G0)) := by
    rw [map_centralizer_singleton thetaM tM, Subgroup.card_map_of_injective thetaM.injective]
    exact three_dvd_card_cent_t
  have hC := fComp twoF4Setting.hι (clauseβ e) hβ _ hε
  have hnc := F431LieI.not_conj_of_card twoF4_F431LieI_G0 hC hb hr1 hr2
  have : Finite twoF4Setting.ι.G0 := Finite.of_equiv _ thetaM.toEquiv
  have h442 := loc442 twoF4_Loc442Datum_G0 hC hb hnc
  rw [htam] at h442
  exact h442.trans hrb2

end CFSG.Quasithin.H13.F431.TwoF4
