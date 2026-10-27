module

public import CFSG.Quasithin.EmptyFaithful.S14612DB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

section Faith

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G}

theorem Setting146.centralizerMod_uK_eq (S : Setting146 G T M) (hH : IsHTM T M H) :
    centralizerMod (quasithinOmegaOneCenter T) H (uK T M H) = pCoreOf 2 H := by
  classical
  have hHN : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (S.le_mcOf hH).trans S.normalizer_Z.ge
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have h4 : centralizerMod (quasithinOmegaOneCenter T) H (conjClosure (VZ T M) H) = pCoreOf 2 H :=
    S.lemma_14_5_15_four hH
  have huK_le : uK T M H ≤ conjClosure (VZ T M) H := S145.commutator_le_of_le_normalizer hHU
  apply le_antisymm
  · set C := centralizerMod (quasithinOmegaOneCenter T) H (uK T M H) with hC
    have hCH : C ≤ H := centralizerMod_le_left _ _ _
    have hsq : ∀ y ∈ C, y * y ∈ pCoreOf 2 H := by
      intro y hy
      rw [← h4]
      refine ⟨H.mul_mem (hCH hy) (hCH hy), hHN (H.mul_mem (hCH hy) (hCH hy)), fun u hu => ?_⟩
      have hyH : y ∈ H := hCH hy
      have hc : y * u * y⁻¹ * u⁻¹ ∈ uK T M H := by
        have h1 : u * y * u⁻¹ * y⁻¹ ∈ uK T M H := Subgroup.commutator_mem_commutator hu hyH
        have e : y * u * y⁻¹ * u⁻¹ = (u * y * u⁻¹ * y⁻¹)⁻¹ := by group
        rw [e]
        exact (uK T M H).inv_mem h1
      have hz := hy.2.2 _ hc
      have hcU : y * u * y⁻¹ * u⁻¹ ∈ conjClosure (VZ T M) H := huK_le hc
      have hc2 : (y * u * y⁻¹ * u⁻¹) * (y * u * y⁻¹ * u⁻¹) = 1 := by
        have := isElemAbelian_pow_eq_one hUab hcU
        simpa [pow_two] using this
      have e : y * y * u * (y * y)⁻¹ * u⁻¹ =
          (y * (y * u * y⁻¹ * u⁻¹) * y⁻¹ * (y * u * y⁻¹ * u⁻¹)⁻¹) *
            ((y * u * y⁻¹ * u⁻¹) * (y * u * y⁻¹ * u⁻¹)) := by group
      rw [e, hc2, mul_one]
      exact hz
    have hHuK : H ≤ Subgroup.normalizer (uK T M H : Set G) :=
      S145.le_normalizer_commutator hHU Subgroup.le_normalizer
    have hHC : H ≤ Subgroup.normalizer (C : Set G) :=
      le_normalizer_centralizerMod hHN Subgroup.le_normalizer hHuK
    have hCn : (C.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hCH).mpr hHC
    have hC2 : IsPGroup 2 ↥C := by
      intro k
      obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 H ⟨(k : G) * (k : G), hsq _ k.2⟩
      refine ⟨j + 1, Subtype.ext ?_⟩
      have h1 := congrArg Subtype.val hj
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1 ⊢
      rw [pow_succ, pow_mul', pow_two]
      exact h1
    exact le_pCoreOf 2 hCH hCn hC2
  · intro q hq
    have hq' : q ∈ centralizerMod (quasithinOmegaOneCenter T) H (conjClosure (VZ T M) H) := by
      rw [h4]; exact hq
    exact ⟨hq'.1, hq'.2.1, fun u hu => hq'.2.2 u (huK_le hu)⟩

end Faith

section Perm

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.perm_uHi (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) {x : G} (hx : x ∈ H) :
    (conjSub x (uHi T M H H₁) = uHi T M H H₁ ∧ conjSub x (uHi T M H H₂) = uHi T M H H₂) ∨
      (conjSub x (uHi T M H H₁) = uHi T M H H₂ ∧ conjSub x (uHi T M H H₂) = uHi T M H H₁) := by
  have hTH : T ≤ H := hred.isHTM.1.1
  have hTN : T ≤ Subgroup.normalizer (H₀ : Set G) := hTH.trans h.normal
  have hmul : (↑(H₀ ⊔ T) : Set G) = ↑H₀ * ↑T :=
    Subgroup.coe_mul_of_right_le_normalizer_left H₀ T hTN
  have hx' : x ∈ (↑(H₀ ⊔ T) : Set G) := by rw [← h.eq]; exact hx
  rw [hmul] at hx'
  obtain ⟨y, hy, τ, hτ, rfl⟩ := hx'
  have h₁ := conjSub_eq_of_mem_normalizer (h.le_normalizer_uHi₁ S hred hy)
  have h₂ := conjSub_eq_of_mem_normalizer (h.le_normalizer_uHi₂ S hred hy)
  by_cases hτN : τ ∈ Subgroup.normalizer (H₁ : Set G)
  · left
    have hτ₁ : τ ∈ Subgroup.normalizer (uHi T M H H₁ : Set G) :=
      inf_normalizer_le_normalizer_uHi hTH H₁ ⟨hτ, hτN⟩
    have hτ₂ : τ ∈ Subgroup.normalizer (uHi T M H H₂ : Set G) := by
      have : τ ∈ T ⊓ Subgroup.normalizer (H₂ : Set G) := by
        rw [h.inf_normalizer_swap_eq]; exact ⟨hτ, hτN⟩
      exact inf_normalizer_le_normalizer_uHi hTH H₂ this
    refine ⟨?_, ?_⟩
    · rw [conjSub_mul, conjSub_eq_of_mem_normalizer hτ₁, h₁]
    · rw [conjSub_mul, conjSub_eq_of_mem_normalizer hτ₂, h₂]
  · right
    have hτN₂ : τ ∉ Subgroup.normalizer (H₂ : Set G) := by
      intro hh
      have : τ ∈ T ⊓ Subgroup.normalizer (H₁ : Set G) := by
        rw [← h.inf_normalizer_swap_eq]; exact ⟨hτ, hh⟩
      exact hτN this.2
    refine ⟨?_, ?_⟩
    · rw [conjSub_mul, h.conjSub_uHi_of_not_mem hred hτ hτN, h₂]
    · rw [conjSub_mul, h.swap.conjSub_uHi_of_not_mem hred hτ hτN₂, h₁]

end Perm

section Order

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.relIndex_pCoreOf_eq_72 (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ 3) (h : IsDecP T M H 3 H₀ H₁ H₂ t) :
    (pCoreOf 2 H).relIndex H = 72 := by
  have hQH₀ : pCoreOf 2 H ≤ H₀ := h.Q₁.trans h.le₁
  have h1 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 H) H₀ H hQH₀ h.le
  have h2 := Subgroup.relIndex_mul_card (pCoreOf 2 H) H₀
  rw [inf_eq_left.mpr hQH₀, h.card_H₀] at h2
  have hpos : 0 < Nat.card (pCoreOf 2 H) := Nat.card_pos
  have h36 : (pCoreOf 2 H).relIndex H₀ = 36 := Nat.eq_of_mul_eq_mul_right hpos h2
  rw [← h1, h36, h.relIndex_eq_two_of_p_three S hred]

end Order

end CFSG.Quasithin
