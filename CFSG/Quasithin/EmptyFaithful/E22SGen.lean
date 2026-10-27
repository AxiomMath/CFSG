module

public import CFSG.Quasithin.EmptyFaithful.E22PGen

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b

variable {G : Type*} [Group G] [Finite G]

theorem inEFor_top_of_generation {T : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hII : ∀ A : Subgroup G, A ≤ T → Nat.card A = 2 → IsE 1 ⊤ T A ⊤)
    (hK : ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A → 4 ≤ Nat.card A →
      T ⊔ ⨆ K ∈ {K : Subgroup G | IsE 1 ⊤ T A K}, K = ⊤) : InEFor 1 ⊤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine inEFor_top_of_noTwo hT hII ?_
  intro Ω hΩ h2
  by_cases h4 : ∃ A ∈ Ω, A ≤ T ∧ 4 ≤ Nat.card A
  · obtain ⟨A, hA, hAT, hA4⟩ := h4
    have hgen := hK A hAT (hΩ.isElemAbelian A hA) hA4
    have hTX : T ≤ eGen 1 ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (weakClosure T Ω : Set G)) :=
      (le_normalizer_weakClosure hΩ).trans fun x hx =>
        Subgroup.mem_sup_right ⟨Subgroup.mem_top x, hx⟩
    have hKX : (⨆ K ∈ {K : Subgroup G | IsE 1 ⊤ T A K}, K) ≤
        eGen 1 ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (weakClosure T Ω : Set G)) :=
      iSup₂_le fun K hK => (le_eGen hA hAT hK).trans le_sup_left
    refine eq_top_iff.mpr ?_
    calc (⊤ : Subgroup G) = T ⊔ ⨆ K ∈ {K : Subgroup G | IsE 1 ⊤ T A K}, K := hgen.symm
      _ ≤ _ := sup_le hTX hKX
  · push Not at h4
    have hW : weakClosure T Ω = ⊥ := by
      refine le_bot_iff.mp (iSup₂_le fun A hA => iSup_le fun hAT => ?_)
      have hp := isPGroup_of_isElemAbelian (hΩ.isElemAbelian A hA)
      obtain ⟨k, hk⟩ := hp.exists_card_eq
      have h4' := h4 A hA hAT
      have h2' := h2 A hA
      rcases k with _ | _ | k
      · exact le_bot_iff.mpr (Subgroup.card_eq_one.mp (by simpa using hk))
      · exact absurd (by simpa using hk) h2'
      · exfalso
        apply h4'.not_ge
        rw [hk]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hW, Subgroup.normalizer_eq_top_iff.mpr inferInstance, inf_top_eq, sup_top_eq]

theorem nParam_top_le_one_of_generation {T : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hII : ∀ A : Subgroup G, A ≤ T → Nat.card A = 2 → IsE 1 ⊤ T A ⊤)
    (hK : ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A → 4 ≤ Nat.card A →
      T ⊔ ⨆ K ∈ {K : Subgroup G | IsE 1 ⊤ T A K}, K = ⊤) : nParam (⊤ : Subgroup G) ≤ 1 :=
  (nParam_le_iff Nat.one_pos).mpr ((inE_iff_inEFor hT).mpr (inEFor_top_of_generation hT hII hK))

end E1

end CFSG.Quasithin
