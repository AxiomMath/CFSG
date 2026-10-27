module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsDGlue

public section

namespace CFSG.Quasithin.H13.F431.TitsD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.RuType
  CFSG.Quasithin.LieSetting CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.Sporadic.Schreier.Tits
  CFSG.Quasithin.TitsGeo CFSG.Quasithin.H13.F431.TwoF4

set_option linter.unusedSectionVars false


@[expose] def TitsLocalCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H₁ H₂ : Subgroup G)
    (e : (RankTwoAmalgam.ofSubgroups titsH titsN).Iso (RankTwoAmalgam.ofSubgroups H₁ H₂)),
    Subgroup.centralizer ({((isoV1 e titsZH : ↥H₁) : G)} : Set G) ≤ H₁ →
      Subgroup.centralizer ({((isoV1 e titsTH : ↥H₁) : G)} : Set G) ≤ H₂

@[expose] def TitsF424 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (β : titsSetting.α.Completion Y), β.IsFaithful →
    Nat.card Y ≤ Nat.card titsSetting.Yb → Nat.card Y = Nat.card titsSetting.Yb ∧
      ∃ (Ġ : Type) (_ : Group Ġ), titsSetting.IsExtension Ġ ∧ Nonempty (Y ≃* Ġ)

section Completion

variable {G : Type} [Group G] [Finite G] {H L2 : Subgroup G}
  (e : (RankTwoAmalgam.ofSubgroups titsH titsN).Iso (RankTwoAmalgam.ofSubgroups H L2))

@[expose] noncomputable def clauseβD : titsSetting.α.Completion ↥(H ⊔ L2) :=
  precompIso e (subCompletion H L2)

theorem clauseβD_faithful : (clauseβD e).IsFaithful :=
  precompIso_isFaithful e (subCompletion_isFaithful H L2)

theorem bOne_clauseD (a : titsSetting.α.G1) :
    bOne titsSetting.hι (clauseβD e) (H ⊔ L2).subtype ⟨f1 (c := titsSetting.ι) a, a, rfl⟩ =
      ((isoV1 e a : ↥H) : G) :=
  (bOne_apply titsSetting.hι (clauseβD e) (H ⊔ L2).subtype a).trans rfl

theorem bTwo_clauseD (a : titsSetting.α.G2) :
    bTwo titsSetting.hι (clauseβD e) (H ⊔ L2).subtype ⟨f2 (c := titsSetting.ι) a, a, rfl⟩ =
      ((isoV2 e a : ↥L2) : G) :=
  (bTwo_apply titsSetting.hι (clauseβD e) (H ⊔ L2).subtype a).trans rfl

theorem le_range_bOneD :
    H ≤ (bOne titsSetting.hι (clauseβD e) (H ⊔ L2).subtype).range := by
  intro g hg
  refine ⟨⟨f1 (c := titsSetting.ι) ((isoV1 e).symm ⟨g, hg⟩), _, rfl⟩, ?_⟩
  have := bOne_clauseD e ((isoV1 e).symm ⟨g, hg⟩)
  simpa using this

theorem le_range_bTwoD :
    L2 ≤ (bTwo titsSetting.hι (clauseβD e) (H ⊔ L2).subtype).range := by
  intro g hg
  refine ⟨⟨f2 (c := titsSetting.ι) ((isoV2 e).symm ⟨g, hg⟩), _, rfl⟩, ?_⟩
  have := bTwo_clauseD e ((isoV2 e).symm ⟨g, hg⟩)
  simpa using this

theorem range_bTwo_leD :
    (bTwo titsSetting.hι (clauseβD e) (H ⊔ L2).subtype).range ≤ L2 := by
  rintro _ ⟨⟨x, a, rfl⟩, rfl⟩
  rw [bTwo_clauseD e a]
  exact (isoV2 e a).2

theorem amalgamMap_zD :
    amalgamMap (bOne titsSetting.hι (clauseβD e) (H ⊔ L2).subtype)
      (bTwo titsSetting.hι (clauseβD e) (H ⊔ L2).subtype) (thetaD zD) =
      ((isoV1 e titsZH : ↥H) : G) := by
  have hz : thetaD zD = f1 (c := titsSetting.ι) titsZH := Subtype.ext (Subtype.ext rfl)
  have hmem : thetaD zD ∈ titsSetting.Mb1 := ⟨titsZH, hz.symm⟩
  rw [amalgamMap_of_mem₁ _ _ hmem]
  have : (⟨thetaD zD, hmem⟩ : titsSetting.Mb1) =
      ⟨f1 (c := titsSetting.ι) titsZH, titsZH, rfl⟩ := Subtype.ext hz
  rw [this]
  exact bOne_clauseD e titsZH

theorem amalgamMap_tD :
    amalgamMap (bOne titsSetting.hι (clauseβD e) (H ⊔ L2).subtype)
      (bTwo titsSetting.hι (clauseβD e) (H ⊔ L2).subtype) (thetaD tD) =
      ((isoV1 e titsTH : ↥H) : G) := by
  have hz : thetaD tD = f1 (c := titsSetting.ι) titsTH := Subtype.ext (Subtype.ext rfl)
  have hmem : thetaD tD ∈ titsSetting.Mb1 := ⟨titsTH, hz.symm⟩
  rw [amalgamMap_of_mem₁ _ _ hmem]
  have : (⟨thetaD tD, hmem⟩ : titsSetting.Mb1) =
      ⟨f1 (c := titsSetting.ι) titsTH, titsTH, rfl⟩ := Subtype.ext hz
  rw [this]
  exact bOne_clauseD e titsTH

end Completion

theorem three_dvd_card_cent_tD : 3 ∣ Nat.card (Subgroup.centralizer ({tD} : Set ↥titsD)) := by
  have ho : orderOf cD = 3 := by
    have h := orderOf_cM
    rwa [← ιD_cD, orderOf_injective ιD ιD_injective] at h
  have hc : cD ∈ Subgroup.centralizer ({tD} : Set ↥titsD) := cD_mem_cent
  have ho' : orderOf (⟨cD, hc⟩ : Subgroup.centralizer ({tD} : Set ↥titsD)) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact ho
  rw [← ho']
  exact orderOf_dvd_natCard _

theorem mulEquiv_of_isExtension_D {Ġ : Type} [Group Ġ] (hext : titsSetting.IsExtension Ġ)
    (hcard : Nat.card Ġ = Nat.card titsSetting.Yb) : Nonempty (Ġ ≃* quasithinTits) := by
  obtain ⟨ν, hinj, -⟩ := hext
  have hG0 : Nat.card titsSetting.ι.G0 = Nat.card titsSetting.Yb := card_G0 titsSetting.ι
  have hpos : Nat.card titsSetting.Yb ≠ 0 := by
    rw [← hG0, Nat.card_congr thetaD.toEquiv.symm, card_titsD]
    norm_num
  have hfin : Finite Ġ := Nat.finite_of_card_ne_zero (hcard ▸ hpos)
  have e2 : ↥titsSetting.N ≃* titsSetting.ι.G0 := Subgroup.topEquiv
  have hN : Nat.card ↥titsSetting.N = Nat.card titsSetting.Yb := by
    rw [← hG0]
    exact Nat.card_congr e2.toEquiv
  have hbij : Function.Bijective ν :=
    hinj.bijective_of_nat_card_le (by rw [hcard, hN])
  exact ⟨(((MulEquiv.ofBijective ν hbij).symm.trans e2).trans thetaD.symm).trans
    quasithinTitsEquivD.symm⟩

theorem not_three_dvd_card_Mb1_D : ¬ 3 ∣ Nat.card titsSetting.Mb1 := by
  rw [Mb1_eq_D, Subgroup.card_map_of_injective (f := thetaD.toMonoidHom) thetaD.injective,
    card_titsHD]
  decide

theorem three_dvd_card_cent_G0_D :
    3 ∣ Nat.card (Subgroup.centralizer ({thetaD tD} : Set titsSetting.ι.G0)) := by
  rw [map_centralizer_singleton thetaD tD,
    Subgroup.card_map_of_injective (f := thetaD.toMonoidHom) thetaD.injective]
  exact three_dvd_card_cent_tD

theorem f431_clause1_of_inputs (hF424 : TitsF424) (hLoc : TitsLocalCent) :
    ∀ (G : Type) [Group G] [Finite G] (H₁ H₂ : Subgroup G) (z : G),
      IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H₁ H₂)
        (fun Y _ => Nonempty (Y ≃* quasithinTits)) →
      (Nonempty (oTwoQuot ↥H₁ ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥H₁ ≃* ↥(Sz 0))) →
      z ∈ H₁ → z ≠ 1 → z ^ 2 = 1 →
      H₁ ≤ Subgroup.centralizer ({z} : Set G) → Subgroup.centralizer ({z} : Set G) ≤ H₁ →
      Nonempty (G ≃* quasithinTits) := by
  intro G _ _ H₁ H₂ z hα hq hzH hz1 hz2 hHc hcH
  obtain ⟨e⟩ := exists_amalgamIso_of_clause1 hα hq
  have hβ := clauseβD_faithful e
  have hε : Function.Injective (H₁ ⊔ H₂).subtype := Subtype.val_injective
  have hzG : ((isoV1 e titsZH : ↥H₁) : G) = z := zidD e hzH hz2 hz1 hHc
  have hzam := amalgamMap_zD e
  rw [hzG] at hzam
  have htam := amalgamMap_tD e
  have hrb1 := le_range_bOneD e
  have hrb2 := le_range_bTwoD e
  set b1 := bOne titsSetting.hι (clauseβD e) (H₁ ⊔ H₂).subtype with hb1
  set b2 := bTwo titsSetting.hι (clauseβD e) (H₁ ⊔ H₂).subtype with hb2
  have hb : Subgroup.centralizer ({amalgamMap b1 b2 (thetaD zD)} : Set G) ≤ b1.range := by
    rw [hzam]
    exact hcH.trans hrb1
  have hLo := hLoc G H₁ H₂ e (by rw [hzG]; exact hcH)
  have h442 : Subgroup.centralizer ({amalgamMap b1 b2 (thetaD tD)} : Set G) ≤ b2.range := by
    rw [htam]
    exact hLo.trans hrb2
  have hnc := F431LieI.not_conj_of_card titsD_F431LieI_G0
    (fComp titsSetting.hι (clauseβD e) hβ _ hε) hb not_three_dvd_card_Mb1_D
    three_dvd_card_cent_G0_D
  obtain ⟨-, Ġ, _, hext, ⟨φ⟩, hGcard⟩ := LieSetting.lemma_F444I (clauseβD e) hβ _ hε
    titsD_F431LieI_G0 hb hnc h442 (fun hle => hF424 _ (clauseβD e) hβ hle)
  obtain ⟨χ⟩ := mulEquiv_of_isExtension_D hext hGcard
  exact ⟨φ.trans χ⟩

end CFSG.Quasithin.H13.F431.TitsD
