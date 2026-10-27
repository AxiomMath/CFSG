module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F48Def
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Plain
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Comp2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LieData
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Trans

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique U42F431
  CFSG.Quasithin.LieSetting CFSG.Quasithin.H13

theorem plain_half'
    (hF45 : u42Setting.Facts45L) (hF48 : U42F48)
    (hLoc : U42LocalCent) {G : Type} [Group G] [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {M₁ M₂ : Subgroup G} {z : G}
    (hAm : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups M₁ M₂) (IsLieOverTwo .PSU 4 1))
    (hO2 : pCoreOf 2 (M₁ ⊔ M₂) = ⊥) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    (hzc : z ∈ centerOf (M₁ ⊓ M₂)) (hcz : Subgroup.centralizer ({z} : Set G) ≤ M₁)
    (hN1 : Subgroup.normalizer (centerOf (pCoreOf 2 M₁) : Set G) = M₁)
    (hN2 : Subgroup.normalizer (centerOf (pCoreOf 2 M₂) : Set G) = M₂) :
    LieModel G .PSU 4 2 1 := by
  rcases exists_iso_pair hAm with ⟨⟨iso'⟩⟩ | ⟨⟨iso'⟩⟩
  swap
  · exact (not_swapped iso' hz2 hz1 hzc hcz).elim
  let iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂) :=
    Am.isoSymm iso'
  have h1 : iso'.φ1 ⟨z, hzc.1.1⟩ = (⟨xY, xY_mem_P1⟩ : ↥P1) :=
    Subtype.ext (label_phi1 iso'.φ1 iso'.φ12 iso'.comm1 hz2 hz1 hzc)
  have hzx : ((isoP1 iso ⟨xY, xY_mem_P1⟩ : ↥M₁) : G) = z := by
    have : isoP1 iso ⟨xY, xY_mem_P1⟩ = ⟨z, hzc.1.1⟩ := (MulEquiv.symm_apply_eq _).2 h1.symm
    rw [this]
  have hcz' : Subgroup.centralizer ({((isoP1 iso ⟨xY, xY_mem_P1⟩ : ↥M₁) : G)} : Set G) ≤ M₁ := by
    rw [hzx]
    exact hcz
  have ht := hLoc G hG hnab M₁ M₂ iso hO2 hcz' hN1 hN2
  have hzeq : Subgroup.centralizer ({((isoP1 iso ⟨xY, xY_mem_P1⟩ : ↥M₁) : G)} : Set G) = M₁ :=
    le_antisymm hcz' (le_centralizer_image_x iso)
  have hag := (fComp u42Setting.hι (betaOf iso) (betaOf_faithful iso) (epsOf M₁ M₂)
    epsOf_injective).agree
  have hlz := amalgamMap_eG₁ iso xY_mem_P1
  have hlt := amalgamMap_eG₂ iso hag tY_mem_P2
  set b1 := bOne u42Setting.hι (betaOf iso) (epsOf M₁ M₂) with hb1
  set b2 := bTwo u42Setting.hι (betaOf iso) (epsOf M₁ M₂) with hb2
  have hb : Subgroup.centralizer ({amalgamMap b1 b2 (eG xY)} : Set G) ≤ b1.range := by
    rw [hlz, hb1, range_bOne iso]
    exact hcz'
  have hnc : ¬ IsConj (amalgamMap b1 b2 (eG xY)) (amalgamMap b1 b2 (eG tY)) := by
    rw [hlz, hlt]
    refine not_isConj_of_cent hzeq ht ?_
    rw [card_M1 iso, card_M2 iso]
    norm_num
  have h442 : Subgroup.centralizer ({amalgamMap b1 b2 (eG tY)} : Set G) ≤ b2.range := by
    rw [hlt, hb2, range_bTwo iso]
    exact ht
  have hF424 : Nat.card ↥(M₁ ⊔ M₂) ≤ Nat.card u42Setting.Yb →
      Nat.card ↥(M₁ ⊔ M₂) = Nat.card u42Setting.Yb ∧
        ∃ (Ġ : Type) (_ : Group Ġ), u42Setting.IsExtension Ġ ∧ Nonempty (↥(M₁ ⊔ M₂) ≃* Ġ) :=
    fun hle => hF45.lemma_F424 (betaOf iso) (betaOf_faithful iso) hle
      (fun hs => hF48 ↥(M₁ ⊔ M₂) (betaOf iso) (betaOf_faithful iso) hs)
  obtain ⟨-, Ġ, hĠ, hext, ⟨e⟩, hĠcard⟩ := lemma_F444 (betaOf iso) (betaOf_faithful iso)
    (epsOf M₁ M₂) epsOf_injective f431Lie_u42 hb hnc h442 hF424
  obtain ⟨ν, hνi, -⟩ := hext
  have hYb : 0 < Nat.card u42Setting.Yb := Nat.card_pos
  have hfin : Finite Ġ := Nat.finite_of_card_ne_zero (by omega)
  have hNcard : Nat.card ↥u42Setting.N = Nat.card u42Setting.Yb := by
    rw [← RankTwoAmalgam.Completion.card_G0 u42Setting.ι]
    rw [N_eq_top]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  have hbij : Function.Bijective ν := hνi.bijective_of_nat_card_le (by omega)
  let e2 : ↥u42Setting.N ≃* u42Setting.ι.G0 :=
    (MulEquiv.subgroupCongr N_eq_top).trans Subgroup.topEquiv
  let e3 : G ≃* Y := (e.trans (MulEquiv.ofBijective ν hbij).symm).trans (e2.trans eG.symm)
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e3.symm lieModel_Y

end CFSG.Quasithin.H13.F431.U42
