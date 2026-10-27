module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineHyp711

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

theorem exists_isBarMap_kSub_UAOf_zpowers (h : Assumption131 G Γ VA i)
    (hrank : ∀ A ∈ Γ, mRank A ≤ i) (hVAle : ∀ A ∈ Γ, VA A ≤ fixSub A) {a : ↥G}
    (ha : Subgroup.zpowers (a : LGL 2 V) ∈ Γ) (ha2 : orderOf a = 2)
    (hG2 : pCoreOf 2 G = ⊥) {U K : Subgroup (VG G)}
    (hU : U = UAOf G VA (Subgroup.zpowers (a : LGL 2 V)))
    (hK : K = kSub U (⊤ : Subgroup (VG G)) (vHat G)) :
    ∃ φ : ↥K →* ↥(Subgroup.normalClosure ({a} : Set ↥G)),
      IsBarMap K (pCoreOf 2 K) φ ∧ Nat.card (barSub K φ U) = 2 ∧
        barSub K φ U = Subgroup.zpowers ⟨a, Subgroup.subset_normalClosure rfl⟩ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinr := normalClosure_le_comap_inr_kSub h hrank ha hU
  have hΩ := (omegaSet_UAOf_zpowers h hrank ha).1
  have hUΩ : U ∈ omegaSet U (⊤ : Subgroup (VG G)) (vHat G) := by
    rw [hU, hΩ]
    exact ⟨_, ⟨1, by simp⟩, rfl⟩
  have hUK : U ≤ K := hK ▸ le_kSub hUΩ
  set N : Subgroup ↥G := Subgroup.normalClosure ({a} : Set ↥G) with hNdef
  haveI hNn : N.Normal := Subgroup.normalClosure_normal
  have haN : a ∈ N := Subgroup.subset_normalClosure rfl
  have hKN : K ≤ N.comap (SemidirectProduct.rightHom : VG G →* ↥G) := by
    rw [hK]
    refine iSup₂_le fun U' hU' => ?_
    have hU'' := hU'
    rw [hU, hΩ] at hU''
    obtain ⟨B, ⟨y, rfl⟩, rfl⟩ := hU''
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨v, -, rfl⟩ := mem_wHat.mp hx
      rw [Subgroup.mem_comap]
      simp
    · obtain ⟨g, hg, rfl⟩ := mem_aHat.mp hx
      rw [Subgroup.mem_comap, SemidirectProduct.rightHom_inr]
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hgn : g = (y * a * y⁻¹) ^ n := Subtype.ext (by rw [← hn]; simp)
      rw [hgn]
      exact N.zpow_mem (hNn.conj_mem a haN y) n
  let φ : ↥K →* ↥N :=
    ((SemidirectProduct.rightHom : VG G →* ↥G).comp K.subtype).codRestrict N
      (fun k => Subgroup.mem_comap.mp (hKN k.2))
  have hφ : ∀ k : ↥K, ((φ k : ↥N) : ↥G) = SemidirectProduct.rightHom (k : VG G) := fun k => rfl
  have hsurj : Function.Surjective φ := by
    intro x
    have hx : (SemidirectProduct.inr (x : ↥G) : VG G) ∈ K := by rw [hK]; exact hinr x.2
    exact ⟨⟨_, hx⟩, Subtype.ext (by rw [hφ]; exact SemidirectProduct.rightHom_inr _)⟩
  have hPbot : pCoreOf 2 N = ⊥ := by
    haveI hPn : (pCoreOf 2 N).Normal := by
      apply Subgroup.normalizer_eq_top_iff.mp
      refine top_le_iff.mp ?_
      have h1 : Subgroup.normalizer (N : Set ↥G) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hNn
      rw [← h1]
      exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 N
    have hle : pCoreOf 2 N ≤ pCore 2 ↥G :=
      CFSG.LieType.BorelTits.le_pCore 2 hPn (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
    have hG2' : pCore 2 ↥G = ⊥ := by
      have h1 := hG2
      unfold pCoreOf at h1
      rwa [Subgroup.map_eq_bot_iff_of_injective _ G.subtype_injective] at h1
    rw [eq_bot_iff]
    exact hle.trans hG2'.le
  have hVK : K ⊓ vHat G ≤ pCoreOf 2 K := by
    refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left ?_
      (((isElemAbelian_wHat (G := G) ⊤).isPGroup).to_le inf_le_right)
    rw [Subgroup.inf_subgroupOf_left]
    exact normal_vHat.subgroupOf K
  have hker : ∀ k : ↥K, φ k = 1 ↔ (k : VG G) ∈ pCoreOf 2 K := by
    intro k
    constructor
    · intro hk1
      have h1 : SemidirectProduct.rightHom (k : VG G) = 1 := congrArg Subtype.val hk1
      have hkV : (k : VG G) ∈ vHat G := by
        refine mem_wHat.mpr ⟨Multiplicative.toAdd (k : VG G).left, Submodule.mem_top, ?_⟩
        rw [ofAdd_toAdd]
        conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right (k : VG G)]
        have h2 : (k : VG G).right = 1 := h1
        rw [h2, map_one, mul_one]
      exact hVK ⟨k.2, hkV⟩
    · intro hk
      have hmap : (pCoreOf 2 K).map (SemidirectProduct.rightHom : VG G →* ↥G) ≤ pCoreOf 2 N := by
        unfold pCoreOf
        rw [Subgroup.map_map]
        have e : (SemidirectProduct.rightHom : VG G →* ↥G).comp K.subtype = N.subtype.comp φ := by
          ext k
          rfl
        rw [e, ← Subgroup.map_map]
        exact Subgroup.map_mono (CFSG.LieType.BorelTits.map_pCore_le 2 φ hsurj)
      have h1 : SemidirectProduct.rightHom (k : VG G) ∈ pCoreOf 2 N := hmap ⟨k, hk, rfl⟩
      rw [hPbot, Subgroup.mem_bot] at h1
      exact Subtype.ext h1
  refine ⟨φ, ⟨hsurj, hker⟩, ?_⟩
  let ι : ↥N →* LGL 2 V := G.subtype.comp N.subtype
  have hι : Function.Injective ι := G.subtype_injective.comp N.subtype_injective
  have himg : (barSub K φ U).map ι = Subgroup.zpowers (a : LGL 2 V) := by
    unfold barSub
    rw [Subgroup.map_map]
    have e : ι.comp φ = (projG G).comp K.subtype := by
      ext k
      rfl
    rw [e, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hUK, hU]
    exact map_projG_wHat_sup_aHat ((Subgroup.zpowers_le).mpr a.2)
  have hzp : barSub K φ U = Subgroup.zpowers ⟨a, haN⟩ := by
    apply Subgroup.map_injective hι
    rw [himg, MonoidHom.map_zpowers]
    rfl
  refine ⟨?_, hzp⟩
  rw [← Subgroup.card_map_of_injective hι, himg, Nat.card_zpowers, Subgroup.orderOf_coe, ha2]

end CFSG.LocalAnalysis.WeakClosure81

end
