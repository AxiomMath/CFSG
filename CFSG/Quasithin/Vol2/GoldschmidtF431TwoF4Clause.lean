module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Glue
public import CFSG.Quasithin.Recognition.RuTypeJ47a
public import CFSG.Quasithin.Recognition.F4Main

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.RuType
  CFSG.Quasithin.LieSetting CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.Sporadic.Schreier.Tits

set_option linter.unusedSectionVars false


@[expose] def TwoF4LocalCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H₁ H₂ : Subgroup G)
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups H₁ H₂)),
    Subgroup.centralizer ({((isoV1 e twoF4ZH : ↥H₁) : G)} : Set G) ≤ H₁ →
      Subgroup.centralizer ({((isoV1 e twoF4TH : ↥H₁) : G)} : Set G) ≤ H₂

section Completion

variable {G : Type} [Group G] [Finite G] {H L2 : Subgroup G}
  (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups H L2))

@[expose] noncomputable def clauseβ : twoF4Setting.α.Completion ↥(H ⊔ L2) :=
  precompIso e (subCompletion H L2)

theorem clauseβ_faithful : (clauseβ e).IsFaithful :=
  precompIso_isFaithful e (subCompletion_isFaithful H L2)

theorem bOne_clause (a : twoF4Setting.α.G1) :
    bOne twoF4Setting.hι (clauseβ e) (H ⊔ L2).subtype ⟨f1 (c := twoF4Setting.ι) a, a, rfl⟩ =
      ((isoV1 e a : ↥H) : G) :=
  (bOne_apply twoF4Setting.hι (clauseβ e) (H ⊔ L2).subtype a).trans rfl

theorem bTwo_clause (a : twoF4Setting.α.G2) :
    bTwo twoF4Setting.hι (clauseβ e) (H ⊔ L2).subtype ⟨f2 (c := twoF4Setting.ι) a, a, rfl⟩ =
      ((isoV2 e a : ↥L2) : G) :=
  (bTwo_apply twoF4Setting.hι (clauseβ e) (H ⊔ L2).subtype a).trans rfl

theorem le_range_bOne :
    H ≤ (bOne twoF4Setting.hι (clauseβ e) (H ⊔ L2).subtype).range := by
  intro g hg
  refine ⟨⟨f1 (c := twoF4Setting.ι) ((isoV1 e).symm ⟨g, hg⟩), _, rfl⟩, ?_⟩
  have := bOne_clause e ((isoV1 e).symm ⟨g, hg⟩)
  simpa using this

theorem le_range_bTwo :
    L2 ≤ (bTwo twoF4Setting.hι (clauseβ e) (H ⊔ L2).subtype).range := by
  intro g hg
  refine ⟨⟨f2 (c := twoF4Setting.ι) ((isoV2 e).symm ⟨g, hg⟩), _, rfl⟩, ?_⟩
  have := bTwo_clause e ((isoV2 e).symm ⟨g, hg⟩)
  simpa using this

theorem amalgamMap_zM :
    amalgamMap (bOne twoF4Setting.hι (clauseβ e) (H ⊔ L2).subtype)
      (bTwo twoF4Setting.hι (clauseβ e) (H ⊔ L2).subtype) (thetaM zM) =
      ((isoV1 e twoF4ZH : ↥H) : G) := by
  have hz : thetaM zM = f1 (c := twoF4Setting.ι) twoF4ZH := Subtype.ext (Subtype.ext rfl)
  have hmem : thetaM zM ∈ twoF4Setting.Mb1 := ⟨twoF4ZH, hz.symm⟩
  rw [amalgamMap_of_mem₁ _ _ hmem]
  have : (⟨thetaM zM, hmem⟩ : twoF4Setting.Mb1) =
      ⟨f1 (c := twoF4Setting.ι) twoF4ZH, twoF4ZH, rfl⟩ := Subtype.ext hz
  rw [this]
  exact bOne_clause e twoF4ZH

theorem amalgamMap_tM :
    amalgamMap (bOne twoF4Setting.hι (clauseβ e) (H ⊔ L2).subtype)
      (bTwo twoF4Setting.hι (clauseβ e) (H ⊔ L2).subtype) (thetaM tM) =
      ((isoV1 e twoF4TH : ↥H) : G) := by
  have hz : thetaM tM = f1 (c := twoF4Setting.ι) twoF4TH := Subtype.ext (Subtype.ext rfl)
  have hmem : thetaM tM ∈ twoF4Setting.Mb1 := ⟨twoF4TH, hz.symm⟩
  rw [amalgamMap_of_mem₁ _ _ hmem]
  have : (⟨thetaM tM, hmem⟩ : twoF4Setting.Mb1) =
      ⟨f1 (c := twoF4Setting.ι) twoF4TH, twoF4TH, rfl⟩ := Subtype.ext hz
  rw [this]
  exact bOne_clause e twoF4TH

end Completion

theorem mulEquiv_of_isExtension {Ġ : Type} [Group Ġ] (hext : twoF4Setting.IsExtension Ġ)
    (hcard : Nat.card Ġ = Nat.card twoF4Setting.Yb) :
    Nonempty (Ġ ≃* MulAut CFSG.Open.quasithinTits) := by
  obtain ⟨ν, hinj, -⟩ := hext
  have hG0 : Nat.card twoF4Setting.ι.G0 = Nat.card twoF4Setting.Yb := card_G0 twoF4Setting.ι
  have hpos : Nat.card twoF4Setting.Yb ≠ 0 := by
    rw [← hG0, Nat.card_congr thetaM.toEquiv.symm, card_twoF4M, card_titsD]
    norm_num
  have hfin : Finite Ġ := Nat.finite_of_card_ne_zero (hcard ▸ hpos)
  have e2 : ↥twoF4Setting.N ≃* twoF4Setting.ι.G0 := Subgroup.topEquiv
  have hN : Nat.card ↥twoF4Setting.N = Nat.card twoF4Setting.Yb := by
    rw [← hG0]
    exact Nat.card_congr e2.toEquiv
  have hbij : Function.Bijective ν :=
    hinj.bijective_of_nat_card_le (by rw [hcard, hN])
  exact ⟨((((MulEquiv.ofBijective ν hbij).symm.trans e2).trans thetaM.symm).trans
    (twoF4AutEquiv titsOutBound).symm).symm.symm⟩

theorem f431_clause2_of_inputs (hF45 : F45TwoF4) (hF48 : F48TwoF4) (hLoc : TwoF4LocalCent) :
    ∀ (G : Type) [Group G] [Finite G] (H₁ H₂ : Subgroup G) (z : G),
      IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H₁ H₂) (IsTwistedF4Over 1) →
      Nonempty (oTwoQuot ↥H₁ ≃* Sz 0) → z ∈ H₁ → z ≠ 1 → z ^ 2 = 1 →
      H₁ ≤ Subgroup.centralizer ({z} : Set G) → Subgroup.centralizer ({z} : Set G) ≤ H₁ →
      Nonempty (G ≃* MulAut CFSG.Open.quasithinTits) := by
  intro G _ _ H₁ H₂ z hα hq hzH hz1 hz2 hHc hcH
  obtain ⟨e⟩ := exists_amalgamIso_of_clause2 hα hq
  have hβ := clauseβ_faithful e
  have hε : Function.Injective (H₁ ⊔ H₂).subtype := Subtype.val_injective
  have hzG : ((isoV1 e twoF4ZH : ↥H₁) : G) = z := zid e hzH hz2 hz1 hHc
  have hzam := amalgamMap_zM e
  rw [hzG] at hzam
  have htam := amalgamMap_tM e
  have hrb1 := le_range_bOne e
  have hrb2 := le_range_bTwo e
  set b1 := bOne twoF4Setting.hι (clauseβ e) (H₁ ⊔ H₂).subtype with hb1
  set b2 := bTwo twoF4Setting.hι (clauseβ e) (H₁ ⊔ H₂).subtype with hb2
  have hb : Subgroup.centralizer ({amalgamMap b1 b2 (thetaM zM)} : Set G) ≤ b1.range := by
    rw [hzam]
    exact hcH.trans hrb1
  have hLo := hLoc G H₁ H₂ e (by rw [hzG]; exact hcH)
  have h442 : Subgroup.centralizer ({amalgamMap b1 b2 (thetaM tM)} : Set G) ≤ b2.range := by
    rw [htam]
    exact hLo.trans hrb2
  have hF424 : Nat.card ↥(H₁ ⊔ H₂) ≤ Nat.card twoF4Setting.Yb →
      Nat.card ↥(H₁ ⊔ H₂) = Nat.card twoF4Setting.Yb ∧
        ∃ (Ġ : Type) (_ : Group Ġ), twoF4Setting.IsExtension Ġ ∧ Nonempty (↥(H₁ ⊔ H₂) ≃* Ġ) :=
    fun hle => hF45.lemma_F424 (clauseβ e) hβ hle (fun hs => hF48 ↥(H₁ ⊔ H₂) (clauseβ e) hβ hs)
  have hr1 : ¬ 3 ∣ Nat.card twoF4Setting.Mb1 := by
    rw [Mb1_eq, Subgroup.card_map_of_injective thetaM.injective, card_twoF4M1]
    decide
  have hr2 : 3 ∣ Nat.card (Subgroup.centralizer ({thetaM tM} : Set twoF4Setting.ι.G0)) := by
    rw [map_centralizer_singleton thetaM tM, Subgroup.card_map_of_injective thetaM.injective]
    exact three_dvd_card_cent_t
  have hnc := F431LieI.not_conj_of_card twoF4_F431LieI_G0
    (fComp twoF4Setting.hι (clauseβ e) hβ _ hε) hb hr1 hr2
  obtain ⟨-, Ġ, _, hext, ⟨φ⟩, hGcard⟩ := LieSetting.lemma_F444I (clauseβ e) hβ _ hε
    twoF4_F431LieI_G0 hb hnc h442 hF424
  obtain ⟨χ⟩ := mulEquiv_of_isExtension hext hGcard
  exact ⟨φ.trans χ⟩

end CFSG.Quasithin.H13.F431.TwoF4
