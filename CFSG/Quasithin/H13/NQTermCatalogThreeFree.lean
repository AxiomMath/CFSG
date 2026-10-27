module

public import CFSG.RankThree.ThinCatalog.FiveModels
public import CFSG.Quasithin.SteinbergBQSmallClassicalSylow
public import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentClassical

public section

namespace CFSG.Quasithin.H13.NQTerm

open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.SteinbergCD (simple_order_two_power_three_prime_sylow_product_rigidity)
open scoped Pointwise

theorem card_of_mulEquiv_alternatingFive {S : Type} [Group S]
    (e : S ≃* alternatingGroup (Fin 5)) : Nat.card S = 2 ^ 2 * 3 * 5 := by
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  rfl

theorem le_sylow_of_statedClassicalModel_small {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a) {n p f : ℕ} [Fact p.Prime]
    (hnpf : (n, p, f) = (2, 2, 2) ∨ (n, p, f) = (2, 5, 1) ∨ (n, p, f) = (2, 7, 1) ∨
      (n, p, f) = (3, 2, 1))
    (hS : StatedClassicalModel S .PSL n p f) (T : Sylow 2 S) (A : Subgroup S)
    (hA : ¬ 3 ∣ Nat.card A) (hAT : (A : Set S) * (T : Set S) = (T : Set S) * (A : Set S)) :
    A ≤ T :=
  CFSG.Quasithin.SteinbergBQ.small_classical_model_three_free_sylow_product_rigidity hnab hnpf
    (CFSG.ComponentClassification.QuaternionComponent.classicalModel_of_statedClassicalModel
      .PSL n p f hS) T A hA hAT

theorem odd_rank_one_catalog_three_free_sylow_product_model_restriction
    (S : Type) [Group S]
    [Finite S] [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a) (hcat : Catalog S)
    (hodd : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r S ≤ 1) (T : Sylow 2 S) (A : Subgroup S)
    (hA : ¬ 3 ∣ Nat.card A) (hAT : (A : Set S) * (T : Set S) = (T : Set S) * (A : Set S))
    (hAT' : ¬ A ≤ T) :
    (∃ f : ℕ, 3 ≤ f ∧ StatedClassicalModel S .PSL 2 2 f) ∨
      (∃ ℓ : ℕ, ℓ.Prime ∧ 11 ≤ ℓ ∧ StatedClassicalModel S .PSL 2 ℓ 1) ∨
      (∃ a : ℕ, 1 ≤ a ∧ SuzukiModel S 2 (2 * a + 1)) ∨
      Nonempty (S ≃* NativeSporadic.J1) := by
  have hno : 2 ≤ CFSG.pRank 3 S → False := fun h => by
    have := hodd 3 Nat.prime_three (by norm_num)
    omega
  rcases hcat with ⟨p, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, hm⟩ | hex | hspor
  ·
    obtain ⟨a, b, hab⟩ := hnab
    exact (hab (CFSG.RankThree.ThinCatalog.commute_of_mulEquiv_zmod e a b)).elim
  ·
    rcases (show n = 5 ∨ 6 ≤ n by omega) with rfl | h6
    · exact (hAT' (simple_order_two_power_three_prime_sylow_product_rigidity
        (by norm_num) (by norm_num) (card_of_mulEquiv_alternatingFive e) T A hA hAT)).elim
    · refine (hno ?_).elim
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
      exact CFSG.SectionRank.le_pRank (by norm_num) le_top
        (CFSG.SectionRank.isElemAbelian_sylowThreeAlt h6) (CFSG.SectionRank.card_sylowThreeAlt h6)
  ·
    have hp : p.Prime := hm.1.1
    have : Fact p.Prime := ⟨hp⟩
    by_cases hp2 : p = 2
    · subst hp2
      rcases CFSG.QuasithinUnique.Vol2Native.EvenWit.oddRankOneEvenClassical S hodd t n f hm with
        ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl, rfl⟩
      · rcases (show f = 2 ∨ 3 ≤ f by omega) with rfl | hf3
        · exact (hAT' (le_sylow_of_statedClassicalModel_small hnab (.inl rfl) hm T A hA
            hAT)).elim
        · exact Or.inl ⟨f, hf3, hm⟩
      · exact (hAT' (le_sylow_of_statedClassicalModel_small hnab (.inr (.inr (.inr rfl))) hm T A
          hA hAT)).elim
    · obtain ⟨rfl, rfl, rfl, hp5⟩ :=
        CFSG.QuasithinUnique.Setup.Family.oddRankOneOddClassical S hodd p hp hp2 t n f hm
      by_cases h5 : p = 5
      · subst h5
        exact (hAT' (le_sylow_of_statedClassicalModel_small hnab (.inr (.inl rfl)) hm T A hA
          hAT)).elim
      by_cases h7 : p = 7
      · subst h7
        exact (hAT' (le_sylow_of_statedClassicalModel_small hnab (.inr (.inr (.inl rfl))) hm T A
          hA hAT)).elim
      have h11 : 11 ≤ p := by
        by_contra hlt
        have : p = 6 ∨ p = 8 ∨ p = 9 ∨ p = 10 := by omega
        rcases this with rfl | rfl | rfl | rfl <;> norm_num at hp
      exact Or.inr (Or.inl ⟨p, hp, h11, hm⟩)
  ·
    rcases hex with ⟨t, p, f, -, hm⟩ | ⟨t, p, f, -, hm⟩ | ⟨p, f, hm⟩
    · obtain ⟨rfl, rfl, rfl⟩ :=
        CFSG.RankThree.Chevalley.odd_rank_one_Chevalley_exceptional_model_is_binary_triality S
          hodd t p f hm
      exact (hno (CFSG.QuasithinUnique.Setup.Family.trialityTwoHasRankTwo S hm)).elim
    · exact (CFSG.RankThree.Chevalley.odd_rank_one_excludes_all_Ree_Tits_models S hodd t p f
        hm).elim
    · obtain ⟨rfl, a, ha, K, hK, hKf, rfl, hcard, he⟩ := hm
      exact Or.inr (Or.inr (Or.inl ⟨a, ha, rfl, a, ha, K, hK, hKf, rfl, hcard, he⟩))
  ·
    have hSQT : CFSG.IsStronglyQuasithin S := fun r hr hr2 => (hodd r hr hr2).trans (by norm_num)
    have : Nontrivial S := IsSimpleGroup.toNontrivial
    exact Or.inr (Or.inr (Or.inr
      (CFSG.RankThree.ThinCatalog.sqt_sporadic_three_rank_one_is_J1 S hSQT
        (hodd 3 Nat.prime_three (by norm_num)) hspor)))

end CFSG.Quasithin.H13.NQTerm
