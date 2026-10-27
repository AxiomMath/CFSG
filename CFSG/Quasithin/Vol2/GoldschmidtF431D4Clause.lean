module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Glue
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Props
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4F424
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsEnd
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Am

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.Quasithin.LieSetting
  CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.Quasithin.H13.F431.U42.Am

section Completion

variable {G : Type} [Group G] {M₁ M₂ : Subgroup G}
  (e : (RankTwoAmalgam.ofSubgroups d4H d4N).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂))

@[expose] noncomputable def d4Clauseβ : d4Setting.α.Completion ↥(M₁ ⊔ M₂) :=
  precompIso e (subCompletion M₁ M₂)

theorem d4Clauseβ_faithful : (d4Clauseβ e).IsFaithful :=
  precompIso_isFaithful e (subCompletion_isFaithful M₁ M₂)

theorem d4_bOne_clause (a : d4Setting.α.G1) :
    bOne d4Setting.hι (d4Clauseβ e) (M₁ ⊔ M₂).subtype ⟨f1 (c := d4Setting.ι) a, a, rfl⟩ =
      ((d4IsoV1 e a : ↥M₁) : G) :=
  (bOne_apply d4Setting.hι (d4Clauseβ e) (M₁ ⊔ M₂).subtype a).trans rfl

theorem d4_bTwo_clause (a : d4Setting.α.G2) :
    bTwo d4Setting.hι (d4Clauseβ e) (M₁ ⊔ M₂).subtype ⟨f2 (c := d4Setting.ι) a, a, rfl⟩ =
      ((d4IsoV2 e a : ↥M₂) : G) :=
  (bTwo_apply d4Setting.hι (d4Clauseβ e) (M₁ ⊔ M₂).subtype a).trans rfl

theorem d4_le_range_bOne :
    M₁ ≤ (bOne d4Setting.hι (d4Clauseβ e) (M₁ ⊔ M₂).subtype).range := by
  intro g hg
  refine ⟨⟨f1 (c := d4Setting.ι) ((d4IsoV1 e).symm ⟨g, hg⟩), _, rfl⟩, ?_⟩
  have := d4_bOne_clause e ((d4IsoV1 e).symm ⟨g, hg⟩)
  simpa using this

theorem d4_le_range_bTwo :
    M₂ ≤ (bTwo d4Setting.hι (d4Clauseβ e) (M₁ ⊔ M₂).subtype).range := by
  intro g hg
  refine ⟨⟨f2 (c := d4Setting.ι) ((d4IsoV2 e).symm ⟨g, hg⟩), _, rfl⟩, ?_⟩
  have := d4_bTwo_clause e ((d4IsoV2 e).symm ⟨g, hg⟩)
  simpa using this

theorem d4_amalgamMap_z :
    amalgamMap (bOne d4Setting.hι (d4Clauseβ e) (M₁ ⊔ M₂).subtype)
      (bTwo d4Setting.hι (d4Clauseβ e) (M₁ ⊔ M₂).subtype) (d4Theta d4z) =
      ((d4IsoV1 e d4ZH : ↥M₁) : G) := by
  have hz : d4Theta d4z = f1 (c := d4Setting.ι) d4ZH := Subtype.ext (Subtype.ext rfl)
  have hmem : d4Theta d4z ∈ d4Setting.Mb1 := ⟨d4ZH, hz.symm⟩
  rw [amalgamMap_of_mem₁ _ _ hmem]
  have : (⟨d4Theta d4z, hmem⟩ : d4Setting.Mb1) =
      ⟨f1 (c := d4Setting.ι) d4ZH, d4ZH, rfl⟩ := Subtype.ext hz
  rw [this]
  exact d4_bOne_clause e d4ZH

theorem d4_amalgamMap_t :
    amalgamMap (bOne d4Setting.hι (d4Clauseβ e) (M₁ ⊔ M₂).subtype)
      (bTwo d4Setting.hι (d4Clauseβ e) (M₁ ⊔ M₂).subtype) (d4Theta d4t) =
      ((d4IsoV1 e d4TH : ↥M₁) : G) := by
  have hz : d4Theta d4t = f1 (c := d4Setting.ι) d4TH := Subtype.ext (Subtype.ext rfl)
  have hmem : d4Theta d4t ∈ d4Setting.Mb1 := ⟨d4TH, hz.symm⟩
  rw [amalgamMap_of_mem₁ _ _ hmem]
  have : (⟨d4Theta d4t, hmem⟩ : d4Setting.Mb1) =
      ⟨f1 (c := d4Setting.ι) d4TH, d4TH, rfl⟩ := Subtype.ext hz
  rw [this]
  exact d4_bOne_clause e d4TH

end Completion

section Extension


theorem d4_mulEquiv_of_isExtension {Ġ : Type} [Group Ġ]
    (hext : d4Setting.IsExtension Ġ) (hcard : Nat.card Ġ = Nat.card d4Setting.Yb) :
    Nonempty (Ġ ≃* D) := by
  obtain ⟨ν, hinj, -⟩ := hext
  have hG0 : Nat.card d4Setting.ι.G0 = Nat.card d4Setting.Yb := card_G0 d4Setting.ι
  have hpos : Nat.card d4Setting.Yb ≠ 0 := by
    rw [← hG0, Nat.card_congr d4Theta.toEquiv.symm, card_trialityGroup8]
    norm_num
  have hfin : Finite Ġ := Nat.finite_of_card_ne_zero (hcard ▸ hpos)
  have e2 : ↥d4Setting.N ≃* d4Setting.ι.G0 := Subgroup.topEquiv
  have hN : Nat.card ↥d4Setting.N = Nat.card d4Setting.Yb := by
    rw [← hG0]
    exact Nat.card_congr e2.toEquiv
  have hbij : Function.Bijective ν :=
    hinj.bijective_of_nat_card_le (by rw [hcard, hN])
  exact ⟨((MulEquiv.ofBijective ν hbij).symm.trans e2).trans d4Theta.symm⟩

theorem d4_clause_of_inputs
    (hF424 : D4F424) (hNF : D4NonFusion d4ZH d4TH)
    (hLoc : D4LocalCent d4ZH d4TH) :
    ∀ (G : Type) [Group G] [Finite G] (M₁ M₂ : Subgroup G) (z : G)
      (e : (RankTwoAmalgam.ofSubgroups d4H d4N).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂)),
      ((d4IsoV1 e d4ZH : ↥M₁) : G) = z → Subgroup.centralizer ({z} : Set G) ≤ M₁ →
        Nonempty (G ≃* D) := by
  intro G _ _ M₁ M₂ z e hzG hcent
  have hβ := d4Clauseβ_faithful e
  have hε : Function.Injective (M₁ ⊔ M₂).subtype := Subtype.val_injective
  have hcent' : Subgroup.centralizer ({((d4IsoV1 e d4ZH : ↥M₁) : G)} : Set G) ≤ M₁ := by
    rw [hzG]
    exact hcent
  have hzam := d4_amalgamMap_z e
  have htam := d4_amalgamMap_t e
  have hrb1 := d4_le_range_bOne e
  have hrb2 := d4_le_range_bTwo e
  set b1 := bOne d4Setting.hι (d4Clauseβ e) (M₁ ⊔ M₂).subtype with hb1
  set b2 := bTwo d4Setting.hι (d4Clauseβ e) (M₁ ⊔ M₂).subtype with hb2
  have hb : Subgroup.centralizer ({amalgamMap b1 b2 (d4Theta d4z)} : Set G) ≤ b1.range := by
    rw [hzam]
    exact hcent'.trans hrb1
  have hnc : ¬ IsConj (amalgamMap b1 b2 (d4Theta d4z)) (amalgamMap b1 b2 (d4Theta d4t)) := by
    rw [hzam, htam]
    exact hNF G M₁ M₂ e hcent'
  have h442 : Subgroup.centralizer ({amalgamMap b1 b2 (d4Theta d4t)} : Set G) ≤ b2.range := by
    rw [htam]
    exact (hLoc G M₁ M₂ e hcent').trans hrb2
  obtain ⟨-, Ġ, _, hext, ⟨φ⟩, hGcard⟩ := LieSetting.lemma_F444I (d4Clauseβ e) hβ _ hε
    d4_F431LieI_G0 hb hnc h442 (fun hle => hF424 _ (d4Clauseβ e) hβ hle)
  obtain ⟨χ⟩ := d4_mulEquiv_of_isExtension hext hGcard
  exact ⟨φ.trans χ⟩

end Extension

end CFSG.Quasithin.D4Hex
