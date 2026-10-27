module

public import CFSG.Quasithin.EmptyFaithful.S152Defs
public import CFSG.Quasithin.EmptyFaithful.S152NQuot
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Quot

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223

variable {G : Type} [Group G] {T H V H₁ H₂ : Subgroup G}

theorem card_H (φ : OTwoQuot H ≃* S152N.W3) : Nat.card H = 72 * Nat.card (pCoreOf 2 H) := by
  have h := card_eq_image_mul (pCoreOf_le 2 H) le_rfl
  rw [imageOTwoQuot_self_top, Subgroup.card_top, Nat.card_congr φ.toEquiv,
    S152N.W3.card_eq] at h
  exact h

theorem card_T [Finite G] (hT : IsSylowTwoOf T H) (φ : OTwoQuot H ≃* S152N.W3) :
    Nat.card T = 8 * Nat.card (pCoreOf 2 H) := by
  have h9 := S152N.relIndex_eq_nine hT φ
  have h1 := Subgroup.relIndex_mul_card T H
  rw [inf_eq_left.mpr hT.1, h9, card_H φ] at h1
  omega

theorem card_image_pair (hP : IsHPair H V H₁ H₂) :
    Nat.card (imageOTwoQuot H H₁) = 6 ∧ Nat.card (imageOTwoQuot H H₂) = 6 := by
  have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm]
    simp [Nat.factorial]
  obtain ⟨e₁⟩ := hP.iso₁
  obtain ⟨e₂⟩ := hP.iso₂
  exact ⟨(Nat.card_congr e₁.toEquiv).trans h6, (Nat.card_congr e₂.toEquiv).trans h6⟩

theorem pair_le_normalizer (hP : IsHPair H V H₁ H₂) :
    H₁ ≤ Subgroup.normalizer (H₂ : Set G) ∧ H₂ ≤ Subgroup.normalizer (H₁ : Set G) := by
  refine ⟨le_normalizer_of_commutator_mem hP.le₂.1 hP.comm, ?_⟩
  refine le_normalizer_of_commutator_mem hP.le₁.1 fun b hb a ha => ?_
  have e : b * a * b⁻¹ * a⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ := by group
  rw [e]
  exact (pCoreOf 2 H).inv_mem (hP.comm a ha b hb)

theorem image_pair_inf (hP : IsHPair H V H₁ H₂) :
    imageOTwoQuot H H₁ ⊓ imageOTwoQuot H H₂ = ⊥ :=
  imageOTwoQuot_inf_eq_bot hP.le₂.1 hP.inf_eq.le

theorem card_sup_pair (hP : IsHPair H V H₁ H₂) :
    Nat.card ↥(H₁ ⊔ H₂) = 36 * Nat.card (pCoreOf 2 H) := by
  have hle : H₁ ⊔ H₂ ≤ H := sup_le hP.le₁.2 hP.le₂.2
  have hQ : pCoreOf 2 H ≤ H₁ ⊔ H₂ := hP.le₁.1.trans le_sup_left
  have h1 := card_eq_image_mul hQ hle
  rw [imageOTwoQuot_sup hP.le₁.2 hP.le₂.2] at h1
  have h2 := B2F.card_sup_mul_card_inf_of_commute (imageOTwoQuot_commute hP.comm)
  rw [image_pair_inf hP, Subgroup.card_bot, (card_image_pair hP).1,
    (card_image_pair hP).2] at h2
  have h36 : Nat.card ↥(imageOTwoQuot H H₁ ⊔ imageOTwoQuot H H₂) = 36 := by omega
  rw [h1, h36]

theorem relIndex_sup_pair [Finite G] (φ : OTwoQuot H ≃* S152N.W3)
    (hP : IsHPair H V H₁ H₂) : (H₁ ⊔ H₂).relIndex H = 2 := by
  have h1 := Subgroup.relIndex_mul_card (H₁ ⊔ H₂) H
  rw [inf_eq_left.mpr (sup_le hP.le₁.2 hP.le₂.2 : H₁ ⊔ H₂ ≤ H), card_sup_pair hP, card_H φ] at h1
  have hq : 0 < Nat.card (pCoreOf 2 H) := Nat.card_pos
  have h2 : ((H₁ ⊔ H₂).relIndex H * 36) * Nat.card (pCoreOf 2 H) = 72 * Nat.card (pCoreOf 2 H) := by
    rw [mul_assoc]
    exact h1
  have h3 := Nat.eq_of_mul_eq_mul_right hq h2
  omega

end S15223

end CFSG.Quasithin
