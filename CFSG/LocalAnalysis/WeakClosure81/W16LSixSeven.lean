module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2G1Bar
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveFam
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveIb

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

section Certified


private theorem w16l_hatK_transitive_img (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    ∀ B ∈ hatGamma D V, ∃ n : ↥(D.img H),
      (n : LGL 2 D.W) ∈ kHatOf (hatGamma D V) ∧ B = cj (n : LGL 2 D.W) (D.img V) := by
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  rintro B ⟨x, hxH, rfl⟩
  have hsup : S ⊔ CFSG.Quasithin.conjClosure V H = H := IsMinFam16.sup_conjClosure_eq h1 hS h hH hV
  have hK0_le_H : CFSG.Quasithin.conjClosure V H ≤ H :=
    CFSG.Quasithin.conjClosure_le fun g hg z hz =>
      H.mul_mem (H.mul_mem hg (hVH hz)) (H.inv_mem hg)
  have hS_le_NV : S ≤ Subgroup.normalizer (V : Set G) :=
    h.S_le_M.trans (le_of_eq h.hyp.h6.normalizer_eq.symm)
  have hS_le_NK0 : S ≤ Subgroup.normalizer (CFSG.Quasithin.conjClosure V H : Set G) :=
    hH.1.1.trans (CFSG.Quasithin.le_normalizer_conjClosure V H)
  have hx' : x ∈ (↑(S ⊔ CFSG.Quasithin.conjClosure V H) : Set G) := by rw [hsup]; exact hxH
  rw [Subgroup.coe_mul_of_left_le_normalizer_right S (CFSG.Quasithin.conjClosure V H)
    hS_le_NK0] at hx'
  obtain ⟨s, hsS, k, hkK0, hsk⟩ := hx'
  have hkH : k ∈ H := hK0_le_H hkK0
  have hVs : conjSubgroup V s = V :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (hS_le_NV hsS)
  have hconj_x : conjSubgroup V x = conjSubgroup V k := by
    rw [← hsk, ← conjSubgroup_conjSubgroup, hVs]
  let j : ↥H := ⟨k⁻¹, H.inv_mem hkH⟩
  refine ⟨⟨D.ρ j, D.mem_img.2 ⟨j, j.2, rfl⟩⟩, ?_, ?_⟩
  · rw [kHatOf_hatGamma_eq D V hVH]
    exact D.mem_img.2 ⟨j, (CFSG.Quasithin.conjClosure V H).inv_mem hkK0, rfl⟩
  · rw [hconj_x, D.img_conj (A := V) hVH j,
      show ((j : ↥H)⁻¹ : G) = k by simp [j]]

theorem IsMinFam16.hyp711_img (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    SevenK.Hyp711 (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H)) := by
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  have hass : Assumption131 (D.img H) (hatGamma D V) (hatVA D V₀ V) (mRank (D.img V)) :=
    Cex16.assumption131_iSub16 h1 h5 hS h hH.1 hV D
  exact hyp711_UAOf_orbit hass (Cex16.mRank_le_iSub16 h hH.1 D)
    (Cex16.conjImgSpace_le_fixSub_iSub16 h1 h5 hS h hH.1 hV D)
    (hatGamma_transitive D V hVH) ⟨1, H.one_mem, by rw [conjSubgroup_one]⟩
    (w16l_hatK_transitive_img h1 h5 hS h hH hV D)

theorem IsMinFam16.card_hatS_img (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    Nat.card (hatS D V) = 2 ^ E3.mQuot V (V ⊓ iSub16 V H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  have hK0_le_H : CFSG.Quasithin.conjClosure V H ≤ H :=
    CFSG.Quasithin.conjClosure_le fun g hg z hz =>
      H.mul_mem (H.mul_mem hg (hVH hz)) (H.inv_mem hg)
  have hVK : D.img V ≤ hatK D V := D.img_mono (le_conjClosure V H)
  have hpCore_le : pCoreOf 2 (hatK D V) ≤ pCoreOf 2 (D.img H) :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2
      (D.img_mono hK0_le_H)
      (D.img_le_normalizer le_rfl hK0_le_H (le_normalizer_conjClosure V H))
  have hVpCore_bot : D.img V ⊓ pCoreOf 2 (hatK D V) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ D.img V ⊓ pCoreOf 2 (D.img H) := ⟨hx.1, hpCore_le hx.2⟩
    rw [(Cex16.assumption131_iSub16 h1 h5 hS h hH.1 hV D).inf_pCore (D.img V)
      ⟨1, H.one_mem, by rw [conjSubgroup_one]⟩] at hx'
    exact hx'
  have hNS : (CFSG.pCore 2 ↥(hatK D V)) ⊓ (D.img V).subgroupOf (hatK D V) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxN, hxS⟩
    have hxpc : (x : LGL 2 D.W) ∈ pCoreOf 2 (hatK D V) :=
      (CFSG.mem_openPCoreOf_iff x).2 hxN
    have hxV : (x : LGL 2 D.W) ∈ D.img V := hxS
    have hxbot : (x : LGL 2 D.W) ∈ (⊥ : Subgroup (LGL 2 D.W)) := by
      rw [← hVpCore_bot]
      exact ⟨hxV, hxpc⟩
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 hxbot))
  have hrel : (CFSG.pCore 2 ↥(hatK D V)).relIndex
      ((D.img V).subgroupOf (hatK D V)) = Nat.card ((D.img V).subgroupOf (hatK D V)) := by
    have h := Subgroup.relIndex_mul_card (H := CFSG.pCore 2 ↥(hatK D V))
      (K := (D.img V).subgroupOf (hatK D V))
    rw [hNS, Subgroup.card_bot, mul_one] at h
    exact h
  have hmap := Subgroup.relIndex_ker ((D.img V).subgroupOf (hatK D V))
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK D V)))
  have hsub : Nat.card ((D.img V).subgroupOf (hatK D V)) = Nat.card (D.img V) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv
  have hcardV : Nat.card (D.img V) = 2 ^ E3.mQuot V (V ⊓ iSub16 V H) := by
    rw [D.card_img hVH,
      ← Subgroup.inf_relIndex_left (H := V) (K := centralizer (iSub16 V H : Set G)),
      Cex16.inf_centralizer_iSub16_eq h1 h5 hS h hH.1 hV,
      ← Cex16.inf_iSub16_eq h1 h5 hS h hH.1 hV]
    exact E3.relIndex_eq_two_pow h.hyp.h6.elemAbelian.isPGroup (V ⊓ iSub16 V H)
  calc Nat.card (hatS D V)
      = Nat.card (((D.img V).subgroupOf (hatK D V)).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK D V)))) := rfl
    _ = (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK D V))).ker.relIndex
          ((D.img V).subgroupOf (hatK D V)) := hmap.symm
    _ = (CFSG.pCore 2 ↥(hatK D V)).relIndex
          ((D.img V).subgroupOf (hatK D V)) := by rw [QuotientGroup.ker_mk']
    _ = Nat.card ((D.img V).subgroupOf (hatK D V)) := hrel
    _ = Nat.card (D.img V) := hsub
    _ = 2 ^ E3.mQuot V (V ⊓ iSub16 V H) := hcardV

theorem IsMinFam16.sevenElevenAlt_img (hTim : TimmesfeldTIRootInput)
    (hGen : SevenK.TwoConjugateGeneration) (hCore : OddTranspositionCoreInputSC)
    (hList : OddTranspListBundle) (hIn : OrthReflParabolic)
    (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) : SevenElevenAlt (hatX D V) (hatS D V) := by
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  have h711 : SevenK.Hyp711 (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H)))
      (vHat (D.img H)) := IsMinFam16.hyp711_img h1 h5 hS h hH hV D
  let A : Subgroup (VG (D.img H)) := hatV1 D V₀ V
  let K₁ : Subgroup (VG (D.img H)) := kSub A ⊤ (vHat (D.img H))
  have hmem : A ∈ omegaSet A ⊤ (vHat (D.img H)) := h711.mem
  have hAK₁ : A ≤ K₁ := le_iSup₂_of_le A hmem le_rfl
  have hass : Assumption131 (D.img H) (hatGamma D V) (hatVA D V₀ V) (mRank (D.img V)) :=
    Cex16.assumption131_iSub16 h1 h5 hS h hH.1 hV D
  have hrank : ∀ B ∈ hatGamma D V, mRank B ≤ mRank (D.img V) :=
    Cex16.mRank_le_iSub16 h hH.1 D
  have htrans : ∀ B ∈ hatGamma D V, ∀ C ∈ hatGamma D V, ∃ k ∈ D.img H, C = cj k B :=
    hatGamma_transitive D V hVH
  have hA₀ : D.img V ∈ hatGamma D V := ⟨1, H.one_mem, by rw [conjSubgroup_one]⟩
  have hmapK : K₁.map (projG (D.img H)) = hatK D V :=
    (map_projG_kSub_UAOf_orbit hass hrank htrans hA₀).trans (kHatOf_hatGamma_eq D V hVH)
  have hmapA : A.map (projG (D.img H)) = D.img V :=
    map_projG_wHat_sup_aHat (W := hatVA D V₀ V (D.img V)) (A := D.img V)
      (D.img_mono hVH)
  have hmap_to : Set.MapsTo (projG (D.img H)) (K₁ : Set (VG (D.img H)))
      (hatK D V : Set (LGL 2 D.W)) := fun x hx => by
    rw [← hmapK]
    exact Subgroup.mem_map_of_mem (projG (D.img H)) hx
  let ψ : ↥K₁ →* ↥(hatK D V) :=
    ((projG (D.img H)).domRestrict K₁).codRestrict (hatK D V) fun x => hmap_to x.2
  let φ : ↥K₁ →* hatX D V :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK D V))).comp ψ
  have hψ_eq : ∀ x : ↥K₁, ((ψ x : ↥(hatK D V)) : LGL 2 D.W) =
      projG (D.img H) (x : VG (D.img H)) := fun x => rfl
  have hφ_eq : ∀ x : ↥K₁, φ x =
      QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK D V)) (ψ x) := fun x => rfl
  have hψ_surj : Function.Surjective ψ := fun y => by
    have hy : (y : LGL 2 D.W) ∈ K₁.map (projG (D.img H)) := by
      rw [hmapK]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hsurj : Function.Surjective φ := fun y => by
    obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(hatK D V)) y
    obtain ⟨x, hx⟩ := hψ_surj z
    exact ⟨x, by rw [hφ_eq x, hx, hz]⟩
  have hker : ∀ k : ↥K₁, φ k = 1 ↔ (k : VG (D.img H)) ∈ pCoreOf 2 K₁ := by
    intro k
    have hiff := mem_pCoreOf_kSub_UAOf_orbit_iff hass hrank htrans hA₀
      (x := (k : VG (D.img H))) k.2
    have h1 : ψ k ∈ CFSG.pCore 2 ↥(hatK D V) ↔
        projG (D.img H) (k : VG (D.img H)) ∈ pCoreOf 2 (hatK D V) := by
      rw [← hψ_eq k]
      exact (CFSG.mem_openPCoreOf_iff (ψ k)).symm
    have h2 : projG (D.img H) (k : VG (D.img H)) ∈ pCoreOf 2 (hatK D V) ↔
        (k : VG (D.img H)) ∈ pCoreOf 2 K₁ := by
      rw [show hatK D V = kHatOf (hatGamma D V) from (kHatOf_hatGamma_eq D V hVH).symm]
      exact hiff.symm
    rw [hφ_eq k]
    exact (QuotientGroup.eq_one_iff (ψ k)).trans (h1.trans h2)
  have hbar : SevenK.IsBarMap K₁ (pCoreOf 2 K₁) φ := ⟨hsurj, hker⟩
  have hbarSub : SevenK.barSub K₁ φ A = hatS D V := by
    ext y
    rw [SevenK.mem_barSub]
    constructor
    · rintro ⟨k, hkA, hkφ⟩
      have hprojV : projG (D.img H) (k : VG (D.img H)) ∈ D.img V := by
        rw [← hmapA]
        exact Subgroup.mem_map_of_mem (projG (D.img H)) hkA
      have hprojK : projG (D.img H) (k : VG (D.img H)) ∈ hatK D V := by
        rw [← hmapK]
        exact Subgroup.mem_map_of_mem (projG (D.img H)) k.2
      rw [← hkφ]
      refine Subgroup.mem_map.2 ⟨⟨projG (D.img H) (k : VG (D.img H)), hprojK⟩,
        hprojV, ?_⟩
      rw [hφ_eq k]
      exact congrArg (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK D V)))
        (Subtype.ext (hψ_eq k).symm)
    · rintro ⟨x, hxS, hxφ⟩
      have hxV : (x : LGL 2 D.W) ∈ D.img V := hxS
      have hx'A : (x : LGL 2 D.W) ∈ A.map (projG (D.img H)) := by
        rw [hmapA]
        exact hxV
      obtain ⟨k, hkA, hkproj⟩ := Subgroup.mem_map.1 hx'A
      refine ⟨⟨k, hAK₁ hkA⟩, hkA, ?_⟩
      rw [hφ_eq ⟨k, hAK₁ hkA⟩]
      rw [show (ψ ⟨k, hAK₁ hkA⟩ : ↥(hatK D V)) = x from Subtype.ext hkproj]
      exact hxφ
  have hW3 := A6Case.w3Lem711Alt_of_inputs (G := VG (D.img H)) hTim hGen hCore hList hIn
  have hAlt : SevenElevenAlt (hatX D V) (SevenK.barSub K₁ φ A) :=
    (hW3 A ⊤ (vHat (D.img H)) h711).2 (hatX D V) φ hbar
  rwa [hbarSub] at hAlt

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
