module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeO1ppModels
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeO1pp

public section

namespace CFSG.GGQ2Prime

open CFSG.Assembly CFSG.StandardType
open Matrix TauCeti CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports
open CFSG.LocalAnalysis.ComponentInitial
  (unique_field_nine_projective_linear_alternating_six_isomorphism)
open CFSG.ClassicalModels

private theorem pptp3_statedClassical_of_lieModel_PSU52 {X : Type} [Group X]
    (h : CFSG.Models.LieModel X .PSU 5 2 1) :
    CFSG.Open.StatedClassicalModel X .PSU 5 2 1 := by
  obtain ⟨-, hc | ⟨h0, -⟩⟩ := h
  · exact hc
  · omega

theorem pumpUp_u52_center {K : Type} [Group K] [Finite K] {W Wk : Subgroup K} {ζ ξ : MulAut K}
    {Q A : Subgroup (MulAut K)}
    (h : PumpUpAut W Wk ζ ξ Q A) : Subgroup.center W = ⊥ := by
  have hZ := center_trivial_of_U52 h.W_model
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  exact Subtype.ext (hZ z z.2 fun y hy =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨y, hy⟩).symm)

theorem pumpUp_u52_quotient_injective {K : Type} [Group K] [Finite K] {W Wk : Subgroup K}
    {ζ ξ : MulAut K}
    {Q A : Subgroup (MulAut K)}
    (h : PumpUpAut W Wk ζ ξ Q A) :
    Function.Injective ((QuotientGroup.mk' (Subgroup.center K)).comp W.subtype) := by
  have hZ := pumpUp_u52_center h
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro w hw
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hw
  rw [Subgroup.mem_bot]
  have hmem : w ∈ Subgroup.center W := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 hw (y : K))
  rwa [hZ, Subgroup.mem_bot] at hmem

theorem pumpUp_eleven_dvd {K : Type} [Group K] [Finite K] {W Wk : Subgroup K} {ζ ξ : MulAut K}
    {Q A : Subgroup (MulAut K)}
    (h : PumpUpAut W Wk ζ ξ Q A) : 11 ∣ Nat.card (K ⧸ Subgroup.center K) := by
  have hWc : Nat.card W = 13685760 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_two
      (pptp3_statedClassical_of_lieModel_PSU52 h.W_model)
  have hdvd : Nat.card W ∣ Nat.card (K ⧸ Subgroup.center K) :=
    CFSG.EvenSmallLie.CatalogOrders.card_dvd_card_quotient_center_of_injective
      W.subtype (fun _ _ hab => Subtype.ext hab) (pumpUp_u52_center h)
  rw [hWc] at hdvd
  exact dvd_trans (by norm_num : 11 ∣ 13685760) hdvd

theorem catalogIs_u52_of_model {G : Type} [Group G] [Finite G] {V : Subgroup G}
    (hV : CFSG.Models.LieModel V .PSU 5 2 1) :
    CFSG.Yardstones.Md0ec50421ce4.catalogIs V CFSG.LocalAnalysis.GLTheoremA.S9.isU5two := by
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := pptp3_statedClassical_of_lieModel_PSU52 hV
  let _ := hfield
  let _ := hfinite
  have hp : Nat.Prime 2 := by norm_num
  let _ : Fact (Nat.Prime 2) := ⟨hp⟩
  let q : PrimePower := ⟨2, 1, hp, by omega⟩
  have hv' : (LieTypeIndex.twistedA 4 q).Valid := by
    simpa [q] using (CFSG.ClassicalModels.unitaryCatalog_index_valid 5 2 1 hV.1)
  let c := ValidLieTypeIndex.characteristic ⟨LieTypeIndex.twistedA 4 q, hv'⟩
  let ex := ValidLieTypeIndex.fieldExponent ⟨LieTypeIndex.twistedA 4 q, hv'⟩
  have hc : c = 2 := by
    simp only [c, ValidLieTypeIndex.characteristic, LieTypeIndex.characteristic_twistedA, q]
  have he : ex = 1 := by
    simp only [ex, ValidLieTypeIndex.fieldExponent, LieTypeIndex.fieldExponent_twistedA, q]
  let L := GaloisField c (2 * ex)
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card K = Fintype.card L := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card c (2 * ex) (by omega)]
    rw [hc, he]
    norm_num
  let φ : K ≃+* L := FiniteField.ringEquivOfCardEq hcard
  let e1 := statedProjCongr (glCongr (ι := Fin 5) φ) (glCongr_statedSU φ 5 (2 ^ 1))
    (glCongr_statedScalars φ)
  let M : ℕ → Type := fun n => StatedProj (StatedSU 5 n L)
  have hpow : c ^ ex = 2 ^ 1 := by rw [hc, he]
  let eT := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 4 q hv'
  let e2 : M (2 ^ 1) ≃* M (c ^ ex) := (MulEquiv.cast hpow).symm
  refine ⟨.lie ⟨LieTypeIndex.twistedA 4 q, hv'⟩, ?_, ⟨(e.trans e1).trans (e2.trans eT.symm)⟩⟩
  show q.card = 2
  rw [PrimePower.card_def]
  norm_num

theorem pumpUp_not_u52 {K : Type} [Group K] [Finite K] {W Wk : Subgroup K} {ζ ξ : MulAut K}
    {Q A : Subgroup (MulAut K)}
    (h : PumpUpAut W Wk ζ ξ Q A)
    (hS : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .PSU 5 2 1) : False := by
  have hWc : Nat.card W = 13685760 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_two
      (pptp3_statedClassical_of_lieModel_PSU52 h.W_model)
  have hSc : Nat.card (K ⧸ Subgroup.center K) = 13685760 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_two
      (pptp3_statedClassical_of_lieModel_PSU52 hS)
  let φ : W →* K ⧸ Subgroup.center K :=
    (QuotientGroup.mk' (Subgroup.center K)).comp W.subtype
  have hinj : Function.Injective φ := pumpUp_u52_quotient_injective h
  haveI : Fintype W := Fintype.ofFinite W
  haveI : Fintype (K ⧸ Subgroup.center K) := Fintype.ofFinite _
  have hcard : Fintype.card W = Fintype.card (K ⧸ Subgroup.center K) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hWc, hSc]
  have hsurj : Function.Surjective φ :=
    (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard)).1 hinj
  have hmap : W.map (QuotientGroup.mk' (Subgroup.center K)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨w, hw⟩ := hsurj x
    exact Subgroup.mem_map.2 ⟨(w : K), w.2, by simpa [φ] using hw⟩
  have hsup : W ⊔ Subgroup.center K = ⊤ :=
    CFSG.LocalAnalysis.GLTheoremA.S11.y10xE_sup_center_of_map_top hmap
  exact h.W_ne (CFSG.LocalAnalysis.GLTheoremA.S11.y10xE_eq_top_of_sup_center h.quasi.1 hsup)

end CFSG.GGQ2Prime

end
