module

public import CFSG.LocalAnalysis.WeakClosure81.W16LSixSeven
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitSetup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

section Certified


theorem IsMinFam16.exists_hatBar (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    ∃ φ : ↥(kSub (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H))) →*
        hatX D V,
      SevenK.IsBarMap (kSub (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H)))
          (vHat (D.img H)))
        (pCoreOf 2 (kSub (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H)))
          (vHat (D.img H)))) φ ∧
      SevenK.barSub (kSub (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H)))
          (vHat (D.img H))) φ (hatV1 D V₀ V) = hatS D V := by
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
  exact ⟨φ, hbar, hbarSub⟩

theorem IsMinFam16.barSituation_hat (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) : BarSituation (hatX D V) (hatS D V) := by
  have h711 : SevenK.Hyp711 (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H)))
      (vHat (D.img H)) := IsMinFam16.hyp711_img h1 h5 hS h hH hV D
  obtain ⟨φ, hbar, hbarSub⟩ := IsMinFam16.exists_hatBar h1 h5 hS h hH hV D
  have := barSituation_of_hyp711 h711 hbar
  rwa [hbarSub] at this

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
