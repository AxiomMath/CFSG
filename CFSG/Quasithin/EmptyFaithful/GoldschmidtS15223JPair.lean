module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223JCount
public import CFSG.Quasithin.EmptyFaithful.S152NDelta

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223

variable {G : Type} [Group G] [Finite G] {T H V H₁ H₂ : Subgroup G}

omit [Finite G] in
theorem cjSub_mul_eq (g h : G) (A : Subgroup G) : cjSub (g * h) A = cjSub g (cjSub h A) := by
  ext x
  simp [mem_cjSub, mul_assoc]

theorem exists_swap_mem (hT : IsSylowTwoOf T H) (φ : OTwoQuot H ≃* S152N.W3)
    (hP : IsHPair H V H₁ H₂) : ∃ s ∈ T, cjSub s H₁ = H₂ := by
  obtain ⟨t, htH, -, ht, -⟩ := hP.swap
  have hB := relIndex_sup_pair φ hP
  have hN := pair_le_normalizer hP
  have hBN₁ : H₁ ⊔ H₂ ≤ Subgroup.normalizer (H₁ : Set G) := sup_le Subgroup.le_normalizer hN.2
  have hBN₂ : H₁ ⊔ H₂ ≤ Subgroup.normalizer (H₂ : Set G) := sup_le hN.1 Subgroup.le_normalizer
  have hH12 : H₁ ≠ H₂ := fun h => by
    have h1 := image_pair_inf hP
    rw [h, inf_idem] at h1
    have := (card_image_pair hP).2
    rw [h1, Subgroup.card_bot] at this
    omega
  have htB : t ∉ H₁ ⊔ H₂ := fun h =>
    hH12 ((B2F.cjSub_eq_of_mem_normalizer (hBN₁ h)).symm.trans ht)
  have hTB : ¬ T ≤ H₁ ⊔ H₂ := by
    intro h
    have h1 := Subgroup.relIndex_mul_relIndex T (H₁ ⊔ H₂) H h (sup_le hP.le₁.2 hP.le₂.2)
    rw [hB, S152N.relIndex_eq_nine hT φ] at h1
    omega
  obtain ⟨s, hsT, hsB⟩ := IsConcreteLE.not_le_iff_exists.mp hTB
  refine ⟨s, hsT, ?_⟩
  have hidx : ((H₁ ⊔ H₂).subgroupOf H).index = 2 := hB
  have hmem := (Subgroup.mul_mem_iff_of_index_two hidx
    (a := ⟨s, hT.1 hsT⟩) (b := ⟨t⁻¹, H.inv_mem htH⟩)).mpr
    (by
      simp only [Subgroup.mem_subgroupOf, inv_mem_iff]
      exact iff_of_false hsB htB)
  have hb : s * t⁻¹ ∈ H₁ ⊔ H₂ := hmem
  have e : s = (s * t⁻¹) * t := by group
  rw [e, cjSub_mul_eq]
  have : cjSub t H₁ = H₂ := ht
  rw [this]
  exact B2F.cjSub_eq_of_mem_normalizer (hBN₂ hb)

theorem exists_delta_pair (hT : IsSylowTwoOf T H) (φ : OTwoQuot H ≃* S152N.W3)
    (hP : IsHPair H V H₁ H₂) (hne : (deltaSet H V).Nonempty) :
    ∃ A₁ ∈ deltaSet H V, ∃ A₂ ∈ deltaSet H V, A₁ ≤ T ∧ A₂ ≤ T ∧ A₁ ≤ H₁ ∧ A₂ ≤ H₂ := by
  obtain ⟨A₀, hA₀⟩ := hne
  obtain ⟨h, hh, hmax⟩ := exists_conj_isMaxElemAbelian hT hA₀.1
  have hA : cjSub h A₀ ∈ deltaSet H V := S152N.cjSub_mem_deltaSet hh hA₀
  have hAT : cjSub h A₀ ≤ T := hmax.1
  obtain ⟨s, hsT, hs⟩ := exists_swap_mem hT φ hP
  have hsH : s ∈ H := hT.1 hsT
  have hsN : s ∈ Subgroup.normalizer (T : Set G) := Subgroup.le_normalizer hsT
  have hsiN : s⁻¹ ∈ Subgroup.normalizer (T : Set G) := Subgroup.le_normalizer (T.inv_mem hsT)
  rcases hP.delta_le _ hA with h1 | h2
  · exact ⟨_, hA, _, S152N.cjSub_mem_deltaSet hsH hA, hAT, cjSub_le hsN hAT, h1,
      hs ▸ cjSub_mono h1⟩
  · refine ⟨_, S152N.cjSub_mem_deltaSet (H.inv_mem hsH) hA, _, hA,
      cjSub_le hsiN hAT, hAT, ?_, h2⟩
    have := cjSub_mono (g := s⁻¹) h2
    rwa [← hs, cjSub_inv_cjSub] at this

theorem card_image_eq_two {A : Subgroup G} (hAH : A ≤ H)
    (h2 : (A ⊓ pCoreOf 2 H).relIndex A = 2) : Nat.card (imageOTwoQuot H A) = 2 := by
  have h1 := S143.card_imageOTwoQuot_mul hAH
  have h3 := Subgroup.relIndex_mul_card (A ⊓ pCoreOf 2 H) A
  rw [inf_eq_left.mpr (inf_le_left : A ⊓ pCoreOf 2 H ≤ A), h2] at h3
  have hpos : 0 < Nat.card ↥(A ⊓ pCoreOf 2 H) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h3.symm)

theorem card_join_pair (hP : IsHPair H V H₁ H₂) {A₁ A₂ : Subgroup G} (h₁ : A₁ ≤ H₁) (h₂ : A₂ ≤ H₂)
    (c₁ : (A₁ ⊓ pCoreOf 2 H).relIndex A₁ = 2) (c₂ : (A₂ ⊓ pCoreOf 2 H).relIndex A₂ = 2) :
    Nat.card ↥(A₁ ⊔ A₂ ⊔ pCoreOf 2 H) = 4 * Nat.card (pCoreOf 2 H) := by
  have hA₁H : A₁ ≤ H := h₁.trans hP.le₁.2
  have hA₂H : A₂ ≤ H := h₂.trans hP.le₂.2
  have hY : A₁ ⊔ A₂ ⊔ pCoreOf 2 H ≤ H := sup_le (sup_le hA₁H hA₂H) (pCoreOf_le 2 H)
  have h1 := card_eq_image_mul le_sup_right hY
  rw [imageOTwoQuot_sup (sup_le hA₁H hA₂H) (pCoreOf_le 2 H), imageOTwoQuot_sup hA₁H hA₂H] at h1
  have hQ : imageOTwoQuot H (pCoreOf 2 H) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨x, hxH, hxQ, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    exact Subgroup.mem_bot.mpr ((mk_eq_one_iff_mem_pCoreOf ⟨x, hxH⟩).mpr hxQ)
  rw [hQ, sup_bot_eq] at h1
  have hinf : imageOTwoQuot H A₁ ⊓ imageOTwoQuot H A₂ = ⊥ :=
    le_bot_iff.mp ((inf_le_inf (imageOTwoQuot_mono h₁) (imageOTwoQuot_mono h₂)).trans
      (image_pair_inf hP).le)
  have h2 := B2F.card_sup_mul_card_inf_of_commute (imageOTwoQuot_commute
    (X := A₁) (Y := A₂) fun x hx y hy => hP.comm x (h₁ hx) y (h₂ hy))
  rw [hinf, Subgroup.card_bot, card_image_eq_two hA₁H c₁, card_image_eq_two hA₂H c₂] at h2
  have h4 : Nat.card ↥(imageOTwoQuot H A₁ ⊔ imageOTwoQuot H A₂) = 4 := by omega
  rw [h1, h4]

end S15223

end CFSG.Quasithin
