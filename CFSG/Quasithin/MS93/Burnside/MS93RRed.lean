module

public import CFSG.Quasithin.MS93.RedHyp

public section

namespace CFSG.Quasithin.MS93

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem burnsideMS93R_inf_pCoreOf_le_pCoreOf {H G₀ : Subgroup G} (hH : H ≤ G₀) :
    H ⊓ pCoreOf 2 G₀ ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    (le_normalizer_inf Subgroup.le_normalizer (hH.trans (le_normalizer_pCoreOf G₀))) ?_
  exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₀).to_le inf_le_right

theorem burnsideMS93R_exists_charMin {G₀ R K : Subgroup G} (h : PUHyp G₀ R K) :
    ∃ T : Subgroup G, T ≤ R ∧ (T.subgroupOf R).Characteristic ∧
      (K ⊔ T) ⊓ pCoreOf 2 G₀ ≤ T ∧ PUHyp (K ⊔ T) T K ∧ PUMin (K ⊔ T) T K ∧
      Vq (K ⊔ T) K = Vq G₀ K := by
  have key : ∀ (m : ℕ) (T : Subgroup G), Nat.card T = m → T ≤ R →
      (T.subgroupOf R).Characteristic → (K ⊔ T) ⊓ pCoreOf 2 G₀ ≤ T → PUHyp (K ⊔ T) T K →
      Vq (K ⊔ T) K = Vq G₀ K →
      ∃ T' : Subgroup G, T' ≤ R ∧ (T'.subgroupOf R).Characteristic ∧
        (K ⊔ T') ⊓ pCoreOf 2 G₀ ≤ T' ∧ PUHyp (K ⊔ T') T' K ∧ PUMin (K ⊔ T') T' K ∧
        Vq (K ⊔ T') K = Vq G₀ K := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro T hm hTR hTc hTO hT hTV
      by_cases hmin : PUMin (K ⊔ T) T K
      · exact ⟨T, hTR, hTc, hTO, hT, hmin, hTV⟩
      · unfold PUMin at hmin
        push Not at hmin
        obtain ⟨T₁, hT₁T, hc₁, hO₁, hne⟩ := hmin
        have hne₁ : T₁ ≠ ⊥ := hT.ne_bot_of_inf_le hO₁
        have hKT : K ⊔ T ≤ G₀ := by
          rw [h.eq_sup]
          exact sup_le_sup_left hTR K
        have hO : (K ⊔ T₁) ⊓ pCoreOf 2 G₀ ≤ T₁ := by
          intro x hx
          refine hO₁ ⟨hx.1, burnsideMS93R_inf_pCoreOf_le_pCoreOf hKT ⟨?_, hx.2⟩⟩
          exact (sup_le_sup_left hT₁T K) hx.1
        have hlt : Nat.card T₁ < m := hm ▸ Subgroup.card_lt_of_lt (lt_of_le_of_ne hT₁T hne)
        exact ih _ hlt T₁ rfl (hT₁T.trans hTR)
          (C1GN.characteristic_subgroupOf_trans hTR hT₁T hTc hc₁) hO
          (hT.reduce hT₁T hc₁ hO₁ hne₁) ((hT.vq_reduce hT₁T hc₁ hO₁ hne₁).trans hTV)
  have hR : PUHyp (K ⊔ R) R K := h.eq_sup ▸ h
  refine key _ R rfl le_rfl ?_ ?_ hR (by rw [← h.eq_sup])
  · rw [Subgroup.subgroupOf_self]
    exact Subgroup.topCharacteristic
  · exact inf_le_right.trans h.pCore_le

end CFSG.Quasithin.MS93
