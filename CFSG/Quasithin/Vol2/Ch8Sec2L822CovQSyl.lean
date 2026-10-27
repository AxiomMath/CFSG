module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovArith
public import CFSG.Quasithin.Vol2.Ch8Sec2L822KzBranch
public import CFSG.Quasithin.Vol2.Ch1ModO2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem cov_modO2Image_mono {G : Type} [Group G] {Kz A B : Subgroup G} (h : A ≤ B) :
    modO2Image Kz A ≤ modO2Image Kz B :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono Kz h)

theorem cov_Q_sylow {G : Type} [Group G] [Finite G] {Gz T Kz : Subgroup G} (hT : IsSylowTwoOf T Gz)
    (hKG : Kz ≤ Gz) (hTK : T ≤ Subgroup.normalizer (Kz : Set G)) :
    IsPGroup 2 (modO2Image Kz (T ⊓ Kz)) ∧ ¬ 2 ∣ (modO2Image Kz (T ⊓ Kz)).index := by
  have hR2 : IsPGroup 2 ((T ⊓ Kz).subgroupOf Kz) :=
    (IsPGroup.to_inf_left hT.2.1 : IsPGroup 2 ↥(T ⊓ Kz)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ Kz ≤ Kz)).symm
  have hRodd : ¬ 2 ∣ ((T ⊓ Kz).subgroupOf Kz).index := by
    rw [Subgroup.inf_subgroupOf_right]
    exact not_two_dvd_relIndex_kz2 hT hKG hTK
  exact sylow_image_cv (CFSG.pCore 2 ↥Kz) ((T ⊓ Kz).subgroupOf Kz) hR2 hRodd

theorem cov_Q_P9 {G : Type} [Group G] [Finite G] {H Kz : Subgroup G} (h9 : ¬ 9 ∣ Nat.card H) :
    ¬ 9 ∣ Nat.card (modO2Image Kz (H ⊓ Kz)) := by
  intro h
  apply h9
  refine h.trans ?_
  have h1 : Nat.card (modO2Image Kz (H ⊓ Kz)) ∣ Nat.card ((H ⊓ Kz).subgroupOf Kz) :=
    Subgroup.card_map_dvd _ _
  have h2 : Nat.card ((H ⊓ Kz).subgroupOf Kz) = Nat.card (H ⊓ Kz : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : H ⊓ Kz ≤ Kz)).toEquiv
  rw [h2] at h1
  exact h1.trans (Subgroup.card_dvd_of_le inf_le_left)

end CFSG.Quasithin.H13
