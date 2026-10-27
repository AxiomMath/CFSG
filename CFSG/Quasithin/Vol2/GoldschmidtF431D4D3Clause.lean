module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4D3Glue
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4D3Props
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4F48D3Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431D3Lie
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsEnd
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Am
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4D3Top

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.Quasithin.LieSetting
  CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.Quasithin.H13.F431.U42.Am

section Completion

variable {G : Type} [Group G] {M₁ M₂ : Subgroup G}
  (e : (RankTwoAmalgam.ofSubgroups (autStab d4H) (autStab d4N)).Iso
    (RankTwoAmalgam.ofSubgroups M₁ M₂))

@[expose] noncomputable def d3Clauseβ : d3Setting.α.Completion ↥(M₁ ⊔ M₂) :=
  precompIso e (subCompletion M₁ M₂)

theorem d3Clauseβ_faithful : (d3Clauseβ e).IsFaithful :=
  precompIso_isFaithful e (subCompletion_isFaithful M₁ M₂)

theorem d3_bOne_clause (a : d3Setting.α.G1) :
    bOne d3Setting.hι (d3Clauseβ e) (M₁ ⊔ M₂).subtype ⟨f1 (c := d3Setting.ι) a, a, rfl⟩ =
      ((d4IsoV1 e a : ↥M₁) : G) :=
  (bOne_apply d3Setting.hι (d3Clauseβ e) (M₁ ⊔ M₂).subtype a).trans rfl

theorem d3_bTwo_clause (a : d3Setting.α.G2) :
    bTwo d3Setting.hι (d3Clauseβ e) (M₁ ⊔ M₂).subtype ⟨f2 (c := d3Setting.ι) a, a, rfl⟩ =
      ((d4IsoV2 e a : ↥M₂) : G) :=
  (bTwo_apply d3Setting.hι (d3Clauseβ e) (M₁ ⊔ M₂).subtype a).trans rfl

theorem d3_le_range_bOne :
    M₁ ≤ (bOne d3Setting.hι (d3Clauseβ e) (M₁ ⊔ M₂).subtype).range := by
  intro g hg
  refine ⟨⟨f1 (c := d3Setting.ι) ((d4IsoV1 e).symm ⟨g, hg⟩), _, rfl⟩, ?_⟩
  have := d3_bOne_clause e ((d4IsoV1 e).symm ⟨g, hg⟩)
  simpa using this

theorem d3_le_range_bTwo :
    M₂ ≤ (bTwo d3Setting.hι (d3Clauseβ e) (M₁ ⊔ M₂).subtype).range := by
  intro g hg
  refine ⟨⟨f2 (c := d3Setting.ι) ((d4IsoV2 e).symm ⟨g, hg⟩), _, rfl⟩, ?_⟩
  have := d3_bTwo_clause e ((d4IsoV2 e).symm ⟨g, hg⟩)
  simpa using this

theorem d3_amalgamMap_z (hK : autStab d4H ⊔ autStab d4N = ⊤) :
    amalgamMap (bOne d3Setting.hι (d3Clauseβ e) (M₁ ⊔ M₂).subtype)
      (bTwo d3Setting.hι (d3Clauseβ e) (M₁ ⊔ M₂).subtype) (d3Theta hK d3z) =
      ((d4IsoV1 e d3ZH : ↥M₁) : G) := by
  have hz : d3Theta hK d3z = f1 (c := d3Setting.ι) d3ZH := Subtype.ext (Subtype.ext rfl)
  have hmem : d3Theta hK d3z ∈ d3Setting.Mb1 := ⟨d3ZH, hz.symm⟩
  rw [amalgamMap_of_mem₁ _ _ hmem]
  have : (⟨d3Theta hK d3z, hmem⟩ : d3Setting.Mb1) =
      ⟨f1 (c := d3Setting.ι) d3ZH, d3ZH, rfl⟩ := Subtype.ext hz
  rw [this]
  exact d3_bOne_clause e d3ZH

theorem d3_amalgamMap_t (hK : autStab d4H ⊔ autStab d4N = ⊤) :
    amalgamMap (bOne d3Setting.hι (d3Clauseβ e) (M₁ ⊔ M₂).subtype)
      (bTwo d3Setting.hι (d3Clauseβ e) (M₁ ⊔ M₂).subtype) (d3Theta hK d3t) =
      ((d4IsoV1 e d3TH : ↥M₁) : G) := by
  have hz : d3Theta hK d3t = f1 (c := d3Setting.ι) d3TH := Subtype.ext (Subtype.ext rfl)
  have hmem : d3Theta hK d3t ∈ d3Setting.Mb1 := ⟨d3TH, hz.symm⟩
  rw [amalgamMap_of_mem₁ _ _ hmem]
  have : (⟨d3Theta hK d3t, hmem⟩ : d3Setting.Mb1) =
      ⟨f1 (c := d3Setting.ι) d3TH, d3TH, rfl⟩ := Subtype.ext hz
  rw [this]
  exact d3_bOne_clause e d3TH

end Completion

section Extension

variable
  {D' : Type} [Group D'] (hD' : IsLieOverTwo .trialityD4 0 1 D')

include hD' in
theorem d3_clause_of_inputs (hs : IsSimpleGroup D)
    (hCU : ∀ x : D, (∀ u ∈ d4U, x * u = u * x) → x = 1 ∨ x = d4z)
    (hF424 : D3F424) (hNF : D3NonFusion d3ZH d3TH) (hLoc : D3LocalCent d3ZH d3TH) :
    ∀ (G : Type) [Group G] [Finite G] (M₁ M₂ : Subgroup G) (z : G)
      (e : (RankTwoAmalgam.ofSubgroups (autStab d4H) (autStab d4N)).Iso
        (RankTwoAmalgam.ofSubgroups M₁ M₂)),
      ((d4IsoV1 e d3ZH : ↥M₁) : G) = z → Subgroup.centralizer ({z} : Set G) ≤ M₁ →
        IsSimpleGroup G → False := by
  intro G _ _ M₁ M₂ z e hzG hcent hG
  have hK := d3_K3_eq_top hD'
  have hinj := conj_injective hs
  have hodd : ¬ 2 ∣ (MulAut.conj : D →* MulAut D).range.index := by
    rw [d4_conj_index hD']
    decide
  have hβ := d3Clauseβ_faithful e
  have hε : Function.Injective (M₁ ⊔ M₂).subtype := Subtype.val_injective
  have hcent' : Subgroup.centralizer ({((d4IsoV1 e d3ZH : ↥M₁) : G)} : Set G) ≤ M₁ := by
    rw [hzG]
    exact hcent
  have hzam := d3_amalgamMap_z e hK
  have htam := d3_amalgamMap_t e hK
  have hrb1 := d3_le_range_bOne e
  have hrb2 := d3_le_range_bTwo e
  set b1 := bOne d3Setting.hι (d3Clauseβ e) (M₁ ⊔ M₂).subtype with hb1
  set b2 := bTwo d3Setting.hι (d3Clauseβ e) (M₁ ⊔ M₂).subtype with hb2
  have hb : Subgroup.centralizer ({amalgamMap b1 b2 (d3Theta hK d3z)} : Set G) ≤ b1.range := by
    rw [hzam]
    exact hcent'.trans hrb1
  have hnc : ¬ IsConj (amalgamMap b1 b2 (d3Theta hK d3z)) (amalgamMap b1 b2 (d3Theta hK d3t)) := by
    rw [hzam, htam]
    exact hNF G M₁ M₂ e hcent'
  have h442 : Subgroup.centralizer ({amalgamMap b1 b2 (d3Theta hK d3t)} : Set G) ≤ b2.range := by
    rw [htam]
    exact (hLoc G M₁ M₂ e hcent').trans hrb2
  obtain ⟨-, Ġ, _, hext, ⟨φ⟩, hĠcard⟩ := LieSetting.lemma_F444I (d3Clauseβ e) hβ _ hε
    (d3_F431LieI_G0 hK (d3_F431LieI hs hCU hodd)) hb hnc h442
    (fun hle => hF424 _ (d3Clauseβ e) hβ hle)
  obtain ⟨ν, hνinj, hνnorm, -⟩ := hext
  have hD0 : Nat.card D = 211341312 := card_trialityGroup8
  have hYb : Nat.card d3Setting.Yb = 3 * Nat.card D := (d3_card_Yb hK).trans (d4_card_aut hD').1
  have hN : Nat.card d3Setting.N = Nat.card D := d3_card_N hK hinj
  have hNcard : Nat.card d3Setting.N = Nat.card ν.range :=
    Nat.card_congr (MonoidHom.ofInjective hνinj).toEquiv
  have : IsSimpleGroup G := hG
  have : IsSimpleGroup Ġ := φ.symm.isSimpleGroup
  have := hνnorm
  rcases Subgroup.Normal.eq_bot_or_eq_top ν.range with h | h
  · rw [h, Subgroup.card_bot] at hNcard
    omega
  · rw [h, Subgroup.card_top] at hNcard
    omega

end Extension

end CFSG.Quasithin.D4Hex
