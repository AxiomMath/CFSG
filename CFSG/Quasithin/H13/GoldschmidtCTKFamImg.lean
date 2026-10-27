module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamRed
public import CFSG.Quasithin.H13.GoldschmidtCTKFamDelta

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Config

variable {G : Type} [Group G] [Finite G] {J D K V T₁ T₂ : Subgroup G}

namespace A5Setup

variable (h : A5Setup J D K V T₁ T₂)
include h

@[expose] def phi : ↥K →* ↥J ⧸ Subgroup.center ↥J :=
  (projJ J).comp (Subgroup.inclusion h.K_le)

theorem phi_injective : Function.Injective h.phi := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have h1 := h.eq_one_of_mem_K x.2 ((QuotientGroup.eq_one_iff _).1 hx)
  exact (Subgroup.inclusion_injective h.K_le (h1.trans (map_one _).symm)).trans rfl

omit [Finite G] in
theorem phi_range : h.phi.range = imgJ J K := by
  ext s
  rw [MonoidHom.mem_range, mem_imgJ]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨Subgroup.inclusion h.K_le k, k.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

@[expose] noncomputable def equivImg : ↥K ≃* ↥(imgJ J K) :=
  (MonoidHom.ofInjective h.phi_injective).trans (MulEquiv.subgroupCongr h.phi_range)

theorem equivImg_coe (k : ↥K) : ((h.equivImg k : ↥(imgJ J K)) : ↥J ⧸ Subgroup.center ↥J) =
    projJ J (Subgroup.inclusion h.K_le k) := rfl

theorem equivImg_mem (x : ↥K) :
    x ∈ V.subgroupOf K ↔ h.equivImg x ∈ (imgJ J V).subgroupOf (imgJ J K) := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, equivImg_coe]
  constructor
  · intro hx
    exact mem_imgJ.2 ⟨Subgroup.inclusion h.K_le x, hx, rfl⟩
  · intro hx
    obtain ⟨y, hy, hyx⟩ := mem_imgJ.1 hx
    have hyK : (y : G) ∈ K := h.V_le hy
    have hc : y⁻¹ * Subgroup.inclusion h.K_le x ∈ Subgroup.center ↥J := by
      apply (QuotientGroup.eq_one_iff _).1
      change projJ J (y⁻¹ * Subgroup.inclusion h.K_le x) = 1
      rw [map_mul, map_inv, hyx, inv_mul_cancel]
    have h1 := h.eq_one_of_mem_K (K.mul_mem (K.inv_mem hyK) x.2) hc
    have h2 : y = Subgroup.inclusion h.K_le x := by
      rw [inv_mul_eq_one] at h1
      exact h1
    rw [show ((x : ↥K) : G) = (y : G) from (congrArg Subtype.val h2).symm]
    exact hy

theorem card_img_V : Nat.card ↥(imgJ J V) = 16 := by
  have hmap : (V.subgroupOf K).map h.equivImg.toMonoidHom =
      (imgJ J V).subgroupOf (imgJ J K) := by
    ext y
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h.equivImg_mem x).1 hx
    · intro hy
      exact ⟨h.equivImg.symm y, (h.equivImg_mem _).2 (by simpa using hy), by simp⟩
  have hle : imgJ J V ≤ imgJ J K := imgJ_mono h.V_le
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).symm.toEquiv, ← hmap,
    Subgroup.card_map_of_injective h.equivImg.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.V_le).toEquiv]
  exact h.card_V

theorem elemAbelian_img : IsElemAbelian 2 (imgJ J V) := by
  have hel := h.elemAbelian
  have hc : V ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.2 hel.1
  refine ⟨Subgroup.le_centralizer_iff_isMulCommutative.1 ?_, ?_⟩
  · intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨x, hx, rfl⟩ := mem_imgJ.1 hs
    obtain ⟨y, hy, rfl⟩ := mem_imgJ.1 ht
    have : y * x = x * y := Subtype.ext (Subgroup.mem_centralizer_iff.1 (hc hx) y hy)
    rw [← map_mul, ← map_mul, this]
  · intro s hs
    obtain ⟨x, hx, rfl⟩ := mem_imgJ.1 hs
    have : x ^ 2 = 1 := Subtype.ext (hel.2 _ hx)
    rw [← map_pow, this, map_one]

theorem delta5_img : IsDelta5Ext ↥(imgJ J K) ((imgJ J V).subgroupOf (imgJ J K)) :=
  IsDelta5Ext.of_mulEquiv h.equivImg h.equivImg_mem
    (isDelta5Ext_of_alt5 h.short h.alt h.pCore_K h.card_V)

omit [Finite G] in
theorem T₁_img_norm :
    imgJ J T₁ ≤ Subgroup.normalizer (imgJ J K : Set (↥J ⧸ Subgroup.center ↥J)) := by
  apply le_normalizer_of_conj
  intro s hs y hy
  obtain ⟨t, ht, rfl⟩ := mem_imgJ.1 hs
  obtain ⟨k, hk, rfl⟩ := mem_imgJ.1 hy
  refine mem_imgJ.2 ⟨t * k * t⁻¹, ?_, by simp [map_mul, map_inv]⟩
  exact (Subgroup.mem_normalizer_iff.1 (h.T₁_norm ht) k).1 hk

theorem normalizer_img : Subgroup.normalizer ((imgJ J V : Subgroup (↥J ⧸ Subgroup.center ↥J)) :
    Set (↥J ⧸ Subgroup.center ↥J)) = imgJ J K ⊔ imgJ J T₁ := by
  apply le_antisymm
  · intro s hs
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ s
    have hx1 : ∀ v : ↥J, (v : G) ∈ V → projJ J (x * v * x⁻¹) ∈ imgJ J V := by
      intro v hv
      have := (Subgroup.mem_normalizer_iff.1 hs (projJ J v)).1 (mem_imgJ.2 ⟨v, hv, rfl⟩)
      simpa [map_mul, map_inv] using this
    have hx2 : ∀ v : ↥J, (v : G) ∈ V → projJ J (x⁻¹ * v * x⁻¹⁻¹) ∈ imgJ J V := by
      intro v hv
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hs) (projJ J v)).1
        (mem_imgJ.2 ⟨v, hv, rfl⟩)
      simpa [map_mul, map_inv] using this
    have hxn : (x : G) ∈ Subgroup.normalizer ((V ⊔ D : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · exact h.conj_sup_of_img hx1 y
      · intro hy
        have := h.conj_sup_of_img hx2 _ hy
        simpa [mul_assoc] using this
    have hmem : (x : G) ∈ K ⊔ T₁ := h.norm_V ▸ ⟨Subgroup.mem_sup_left x.2, hxn⟩
    obtain ⟨k, t, hk, ht, rfl⟩ := h.exists_mul_of_mem_sup hmem
    rw [map_mul]
    exact Subgroup.mul_mem_sup (mem_imgJ.2 ⟨k, hk, rfl⟩) (mem_imgJ.2 ⟨t, ht, rfl⟩)
  · refine sup_le ?_ ?_
    · apply le_normalizer_of_conj
      intro s hs y hy
      obtain ⟨k, hk, rfl⟩ := mem_imgJ.1 hs
      obtain ⟨v, hv, rfl⟩ := mem_imgJ.1 hy
      have hkn : (k : G) ∈ Subgroup.normalizer (V : Set G) := by
        have := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk
        rwa [h.pCore_K] at this
      refine mem_imgJ.2 ⟨k * v * k⁻¹, ?_, by simp [map_mul, map_inv]⟩
      exact (Subgroup.mem_normalizer_iff.1 hkn v).1 hv
    · apply le_normalizer_of_conj
      intro s hs y hy
      obtain ⟨t, ht, rfl⟩ := mem_imgJ.1 hs
      obtain ⟨v, hv, rfl⟩ := mem_imgJ.1 hy
      have htN : (t : G) ∈ Subgroup.normalizer ((V ⊔ D : Subgroup G) : Set G) := by
        have : (t : G) ∈ K ⊔ T₁ := Subgroup.mem_sup_right ht
        rw [← h.norm_V] at this
        exact this.2
      have := h.conj_img_of_mem_normalizer htN v hv
      simpa [map_mul, map_inv] using this

theorem a5Config : A5Config (↥J ⧸ Subgroup.center ↥J) :=
  ⟨imgJ J K, imgJ J V, imgJ J T₁, imgJ J T₂, imgJ_mono h.V_le, h.card_img_V, h.elemAbelian_img,
    h.delta5_img, h.T₁_img_norm, h.normalizer_img, h.sylow_img_one, h.sylow_img_two,
    imgJ_mono h.T₁_le_T₂, h.relIndex_img⟩

end A5Setup

theorem ExclA5BlockFor.of_not_config {P : ∀ (S : Type) [Group S], Prop}
    (h : ∀ (S : Type) [Group S] [Finite S], P S → ¬ A5Config S) : ExclA5BlockFor P := by
  intro G _ _ J D K V T₁ T₂ _ hP hD2 hDJ hOJD hKJ hKs hKa hKV hV16 hDT1 hT1JD hT1N hN hT1S hT2S
    hT12 hrel
  exact h _ hP (A5Setup.a5Config
    ⟨hD2, hDJ, hOJD, hKJ, hKs, hKa, hKV, hV16, hDT1, hT1JD, hT1N, hN, hT1S, hT2S, hT12, hrel⟩)

end Config

end CFSG.Quasithin.H13.CTK
