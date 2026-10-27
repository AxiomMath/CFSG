module

public import CFSG.Quasithin.Background.F6Cat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111Case
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111Lift

public section

namespace CFSG.Quasithin

namespace Y15111

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {I : Type} [Group I] [Finite I]

theorem card_eq_four_of_isCaseTwo {D : Type} [Group D] [Finite D] (hc2 : F6.IsF618CaseTwo D) :
    ∃ m : ℕ, Odd m ∧ Nat.card D = 4 * m := by
  rcases hc2 with he | ⟨φ, hφ, hN⟩
  · obtain ⟨e⟩ := he
    refine ⟨9, by decide, ?_⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, gold_card_perm_fin_three]
  · refine ⟨27, by decide, ?_⟩
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv,
      Nat.card_prod, hN.2.1] at h1
    simp at h1
    omega

theorem rank_two_perfect {P H V : Subgroup I} {c ch : I}
    (h : IsGoldschmidtTriple P H) (hsq : CFSG.SectionRank.IsSQTKCat I)
    (hV16 : Nat.card V = 16) (hVP : V ≤ P) (hVn : P ≤ Subgroup.normalizer (V : Set I))
    (hVH : ¬ V ≤ pCoreOf 2 H) (hc : c ∈ P) (hc3 : c ^ 3 = 1)
    (hfree : ∀ v ∈ V, c * v * c⁻¹ = v → v = 1) (hch : ch ∈ H) (hch3 : ch ^ 3 = 1) :
    c ∈ perfectCore (⊤ : Subgroup I) ∨ ch ∈ perfectCore (⊤ : Subgroup I) := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 4) (by rw [hV16]; norm_num)
  have hVQ : V ≤ pCoreOf 2 P :=
    le_pCoreOf 2 hVP ((Subgroup.normal_subgroupOf_iff_le_normalizer hVP).mpr hVn) hV2
  have hcV : c ∈ Subgroup.normalizer (V : Set I) := hVn hc
  rcases F6.goldschmidt_mod_pPrimeCore h with ⟨hinf, hA, -⟩ | ⟨hq1, hq2, -, -, -⟩
  · set X := CFSG.pPrimeCore 3 I with hX
    set π := QuotientGroup.mk' X with hπ
    obtain ⟨hO, hm⟩ := F6.pPrimeCore_eq_bot_and_pRank_le_of_isSQTKCat hsq (MulEquiv.refl (I ⧸ X))
    have hT := hA.toIsGoldschmidtTriple
    have hodd : ∀ x : I, x ^ 3 = 1 → Odd (orderOf (π x)) := fun x hx =>
      Odd.of_dvd_nat (by decide : Odd 3)
        (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one]))
    have hcπ : π c ∈ twoResidual (P.map π) :=
      F6.mem_twoResidual_of_odd ⟨c, hc, rfl⟩ (hodd c hc3)
    have hchπ : π ch ∈ twoResidual (H.map π) :=
      F6.mem_twoResidual_of_odd ⟨ch, hch, rfl⟩ (hodd ch hch3)
    rcases F6.f618_trichotomy hT hO hm with (hc1 | hc2) | ⟨-, K, hK, -, hcase⟩ | ⟨-, hL⟩
    ·
      obtain ⟨-, hq, -, -⟩ := hc1
      exact absurd ((hVQ.trans (pCoreOf_le_pCore_of_map_eq_bot h hq)).trans
        (pCore_le_pCoreOf_right h)) hVH
    ·
      obtain ⟨m, hm, hD⟩ := card_eq_four_of_isCaseTwo hc2
      have hS := F6.isSylowTwoOf_inf_top hT
      have h4 := card_eq_four_of_isSylow hS hm hD
      rw [hinf] at h4
      have h5 := F6.card_map_mk (P ⊓ H) X
      rw [h4, ← Subgroup.inf_relIndex_right, inf_comm, F6.inf_inf_pPrimeCore_eq_pCore h] at h5
      exact (false_of_index_four h hV16 hVQ hVH hcV hc3 hfree h5.symm).elim
    ·
      have hKperf : K ≤ perfectCore (⊤ : Subgroup (I ⧸ X)) :=
        le_perfectCore_of_perfect le_top (commutator_eq_self_of_perfect' hK.1.1)
      rcases hcase with ⟨h₁, -, -⟩ | ⟨h₂, -, -⟩
      · exact Or.inl (mem_perfectCore_of_map_pPrimeCore hc3 (hKperf (h₁ hcπ)))
      · exact Or.inr (mem_perfectCore_of_map_pPrimeCore hch3 (hKperf (h₂ hchπ)))
    ·
      have hLperf : twoResidual (⊤ : Subgroup (I ⧸ X)) ≤ perfectCore (⊤ : Subgroup (I ⧸ X)) :=
        le_perfectCore_of_perfect le_top (commutator_eq_self_of_perfect' hL.1)
      have hcπ' : π c ∈ twoResidual (⊤ : Subgroup (I ⧸ X)) :=
        F6.mem_twoResidual_of_odd (Subgroup.mem_top _) (hodd c hc3)
      exact Or.inl (mem_perfectCore_of_map_pPrimeCore hc3 (hLperf hcπ'))
  · exact absurd (hVQ.trans (hq1.trans hq2.symm).le) hVH

end Y15111

end CFSG.Quasithin
