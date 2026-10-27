module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2G1Asm
public import CFSG.LocalAnalysis.WeakClosure81.A6Case.Wrap711
public import CFSG.GroupTheory.PCore.NormalPCoreOf

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Defs

variable {H E : Subgroup G} (Mo : ModDataE H E) (V : Subgroup G)

abbrev hatK : Subgroup (LGL 2 Mo.W) := Mo.img (conjClosure V H)

abbrev hatX : Type := ↥(hatK Mo V) ⧸ CFSG.pCore 2 ↥(hatK Mo V)

@[expose] def hatS : Subgroup (hatX Mo V) :=
  ((Mo.img V).subgroupOf (hatK Mo V)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK Mo V)))

end Defs

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

theorem hyp711_hat (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    SevenK.Hyp711 (hatV1 Mo V₀ V) (⊤ : Subgroup (VG (Mo.img H))) (vHat (Mo.img H)) := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  exact hyp711_UAOf_orbit (assumption131_hat h1 h5 h15 hS c Mo)
    (mRank_le_hat h1 h5 h15 hS c Mo) (hatVA_le_fixSub h1 h5 h15 hS c Mo)
    (hatGamma_transitive Mo V hVH) (img_mem_hatGamma c Mo) (hatK_transitive h15 hS c Mo)

theorem card_hatS (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    Nat.card (hatS Mo V) = 2 ^ E3.mQuot V (U ⊔ V₀) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVK : Mo.img V ≤ hatK Mo V := Mo.img_mono (le_conjClosure V H)
  have hpCore_le : pCoreOf 2 (hatK Mo V) ≤ pCoreOf 2 (Mo.img H) :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2
      (Mo.img_mono c.conjClosure_le_H)
      (Mo.img_le_normalizer le_rfl c.conjClosure_le_H (le_normalizer_conjClosure V H))
  have hVpCore_bot : Mo.img V ⊓ pCoreOf 2 (hatK Mo V) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ Mo.img V ⊓ pCoreOf 2 (Mo.img H) := ⟨hx.1, hpCore_le hx.2⟩
    rw [(assumption131_hat h1 h5 h15 hS c Mo).inf_pCore (Mo.img V) (img_mem_hatGamma c Mo)]
      at hx'
    exact hx'
  have hNS : (CFSG.pCore 2 ↥(hatK Mo V)) ⊓ (Mo.img V).subgroupOf (hatK Mo V) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxN, hxS⟩
    have hxpc : (x : LGL 2 Mo.W) ∈ pCoreOf 2 (hatK Mo V) :=
      (CFSG.mem_openPCoreOf_iff x).2 hxN
    have hxV : (x : LGL 2 Mo.W) ∈ Mo.img V := hxS
    have hxbot : (x : LGL 2 Mo.W) ∈ (⊥ : Subgroup (LGL 2 Mo.W)) := by
      rw [← hVpCore_bot]
      exact ⟨hxV, hxpc⟩
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 hxbot))
  have hrel : (CFSG.pCore 2 ↥(hatK Mo V)).relIndex
      ((Mo.img V).subgroupOf (hatK Mo V)) = Nat.card ((Mo.img V).subgroupOf (hatK Mo V)) := by
    have h := Subgroup.relIndex_mul_card (H := CFSG.pCore 2 ↥(hatK Mo V))
      (K := (Mo.img V).subgroupOf (hatK Mo V))
    rw [hNS, Subgroup.card_bot, mul_one] at h
    exact h
  have hmap := Subgroup.relIndex_ker ((Mo.img V).subgroupOf (hatK Mo V))
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK Mo V)))
  have hsub : Nat.card ((Mo.img V).subgroupOf (hatK Mo V)) = Nat.card (Mo.img V) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv
  have hcardV : Nat.card (Mo.img V) = 2 ^ E3.mQuot V (U ⊔ V₀) := by
    simpa [conjSubgroup_one] using
      card_img_conjSubgroup h1 h5 h15 hS c Mo (Subgroup.one_mem H)
  calc Nat.card (hatS Mo V)
      = Nat.card (((Mo.img V).subgroupOf (hatK Mo V)).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK Mo V)))) := rfl
    _ = (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK Mo V))).ker.relIndex
          ((Mo.img V).subgroupOf (hatK Mo V)) := hmap.symm
    _ = (CFSG.pCore 2 ↥(hatK Mo V)).relIndex
          ((Mo.img V).subgroupOf (hatK Mo V)) := by rw [QuotientGroup.ker_mk']
    _ = Nat.card ((Mo.img V).subgroupOf (hatK Mo V)) := hrel
    _ = Nat.card (Mo.img V) := hsub
    _ = 2 ^ E3.mQuot V (U ⊔ V₀) := hcardV

section Certified


theorem sevenElevenAlt_hat (hTim : TimmesfeldTIRootInput) (hGen : SevenK.TwoConjugateGeneration)
    (hCore : OddTranspositionCoreInputSC) (hList : OddTranspListBundle)
    (hIn : OrthReflParabolic) (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) : SevenElevenAlt (hatX Mo V) (hatS Mo V) := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  have h711 : SevenK.Hyp711 (hatV1 Mo V₀ V) (⊤ : Subgroup (VG (Mo.img H)))
      (vHat (Mo.img H)) := hyp711_hat h1 h5 h15 hS c Mo
  let A : Subgroup (VG (Mo.img H)) := hatV1 Mo V₀ V
  let K₁ : Subgroup (VG (Mo.img H)) := kSub A ⊤ (vHat (Mo.img H))
  have hmem : A ∈ omegaSet A ⊤ (vHat (Mo.img H)) := h711.mem
  have hAK₁ : A ≤ K₁ := le_iSup₂_of_le A hmem le_rfl
  have hass : Assumption131 (Mo.img H) (hatGamma Mo V) (hatVA Mo V₀ V)
      (E3.mQuot V (U ⊔ V₀)) := assumption131_hat h1 h5 h15 hS c Mo
  have hrank : ∀ B ∈ hatGamma Mo V, mRank B ≤ E3.mQuot V (U ⊔ V₀) :=
    mRank_le_hat h1 h5 h15 hS c Mo
  have htrans : ∀ B ∈ hatGamma Mo V, ∀ C ∈ hatGamma Mo V, ∃ k ∈ Mo.img H, C = cj k B :=
    hatGamma_transitive Mo V hVH
  have hA₀ : Mo.img V ∈ hatGamma Mo V := img_mem_hatGamma c Mo
  have hmapK : K₁.map (projG (Mo.img H)) = hatK Mo V :=
    (map_projG_kSub_UAOf_orbit hass hrank htrans hA₀).trans (kHatOf_hatGamma_eq Mo V hVH)
  have hmapA : A.map (projG (Mo.img H)) = Mo.img V :=
    map_projG_wHat_sup_aHat (W := hatVA Mo V₀ V (Mo.img V)) (A := Mo.img V)
      (Mo.img_mono hVH)
  have hmap_to : Set.MapsTo (projG (Mo.img H)) (K₁ : Set (VG (Mo.img H)))
      (hatK Mo V : Set (LGL 2 Mo.W)) := fun x hx => by
    rw [← hmapK]
    exact Subgroup.mem_map_of_mem (projG (Mo.img H)) hx
  let ψ : ↥K₁ →* ↥(hatK Mo V) :=
    ((projG (Mo.img H)).domRestrict K₁).codRestrict (hatK Mo V) fun x => hmap_to x.2
  let φ : ↥K₁ →* hatX Mo V :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK Mo V))).comp ψ
  have hψ_eq : ∀ x : ↥K₁, ((ψ x : ↥(hatK Mo V)) : LGL 2 Mo.W) =
      projG (Mo.img H) (x : VG (Mo.img H)) := fun x => rfl
  have hφ_eq : ∀ x : ↥K₁, φ x =
      QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK Mo V)) (ψ x) := fun x => rfl
  have hψ_surj : Function.Surjective ψ := fun y => by
    have hy : (y : LGL 2 Mo.W) ∈ K₁.map (projG (Mo.img H)) := by
      rw [hmapK]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hsurj : Function.Surjective φ := fun y => by
    obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(hatK Mo V)) y
    obtain ⟨x, hx⟩ := hψ_surj z
    exact ⟨x, by rw [hφ_eq x, hx, hz]⟩
  have hker : ∀ k : ↥K₁, φ k = 1 ↔ (k : VG (Mo.img H)) ∈ pCoreOf 2 K₁ := by
    intro k
    have hiff := mem_pCoreOf_kSub_UAOf_orbit_iff hass hrank htrans hA₀
      (x := (k : VG (Mo.img H))) k.2
    have h1 : ψ k ∈ CFSG.pCore 2 ↥(hatK Mo V) ↔
        projG (Mo.img H) (k : VG (Mo.img H)) ∈ pCoreOf 2 (hatK Mo V) := by
      rw [← hψ_eq k]
      exact (CFSG.mem_openPCoreOf_iff (ψ k)).symm
    have h2 : projG (Mo.img H) (k : VG (Mo.img H)) ∈ pCoreOf 2 (hatK Mo V) ↔
        (k : VG (Mo.img H)) ∈ pCoreOf 2 K₁ := by
      rw [show hatK Mo V = kHatOf (hatGamma Mo V) from (kHatOf_hatGamma_eq Mo V hVH).symm]
      exact hiff.symm
    rw [hφ_eq k]
    exact (QuotientGroup.eq_one_iff (ψ k)).trans (h1.trans h2)
  have hbar : SevenK.IsBarMap K₁ (pCoreOf 2 K₁) φ := ⟨hsurj, hker⟩
  have hbarSub : SevenK.barSub K₁ φ A = hatS Mo V := by
    ext y
    rw [SevenK.mem_barSub]
    constructor
    · rintro ⟨k, hkA, hkφ⟩
      have hprojV : projG (Mo.img H) (k : VG (Mo.img H)) ∈ Mo.img V := by
        rw [← hmapA]
        exact Subgroup.mem_map_of_mem (projG (Mo.img H)) hkA
      have hprojK : projG (Mo.img H) (k : VG (Mo.img H)) ∈ hatK Mo V := by
        rw [← hmapK]
        exact Subgroup.mem_map_of_mem (projG (Mo.img H)) k.2
      rw [← hkφ]
      refine Subgroup.mem_map.2 ⟨⟨projG (Mo.img H) (k : VG (Mo.img H)), hprojK⟩,
        hprojV, ?_⟩
      rw [hφ_eq k]
      exact congrArg (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK Mo V)))
        (Subtype.ext (hψ_eq k).symm)
    · rintro ⟨x, hxS, hxφ⟩
      have hxV : (x : LGL 2 Mo.W) ∈ Mo.img V := hxS
      have hx'A : (x : LGL 2 Mo.W) ∈ A.map (projG (Mo.img H)) := by
        rw [hmapA]
        exact hxV
      obtain ⟨k, hkA, hkproj⟩ := Subgroup.mem_map.1 hx'A
      refine ⟨⟨k, hAK₁ hkA⟩, hkA, ?_⟩
      rw [hφ_eq ⟨k, hAK₁ hkA⟩]
      rw [show (ψ ⟨k, hAK₁ hkA⟩ : ↥(hatK Mo V)) = x from Subtype.ext hkproj]
      exact hxφ
  have hW3 := A6Case.w3Lem711Alt_of_inputs (G := VG (Mo.img H)) hTim hGen hCore hList hIn
  have hAlt : SevenElevenAlt (hatX Mo V) (SevenK.barSub K₁ φ A) :=
    (hW3 A ⊤ (vHat (Mo.img H)) h711).2 (hatX Mo V) φ hbar
  rwa [hbarSub] at hAlt

end Certified

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
