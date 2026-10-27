module

public import CFSG.RankThree.ThinCatalog.SporadicJ1
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134EvenClassicalProp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddRankOne
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddRankOneGlue
public import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.RankThree.ThinCatalog

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem commute_of_mulEquiv_zmod {S : Type} [Group S] {p : ℕ}
    (e : S ≃* Multiplicative (ZMod p)) (a b : S) : a * b = b * a :=
  e.injective (by rw [map_mul, map_mul, mul_comm])

theorem three_dvd_card_of_pRank_eq_one {S : Type} [Group S] [Finite S]
    (h3 : CFSG.pRank 3 S = 1) : 3 ∣ Nat.card S := by
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (⊤ : Subgroup S)
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top, h3, pow_one] at hE
  rw [← hE]
  exact Subgroup.card_subgroup_dvd_card E

theorem two_pow_odd_mod_three (a : ℕ) : 2 ^ (2 * a + 1) % 3 = 2 := by
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem not_three_dvd_suzuki_order (a : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := two_pow_odd_mod_three a
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  have hq2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  have h3 : Nat.Prime 3 := Nat.prime_three
  intro h
  rcases (Nat.Prime.dvd_mul h3).1 h with h | h
  · rcases (Nat.Prime.dvd_mul h3).1 h with h | h
    · have := h3.dvd_of_dvd_pow h
      omega
    · omega
  · omega

theorem not_three_dvd_card_of_suzukiModel {S : Type} [Group S] {p f : ℕ}
    (h : SuzukiModel S p f) : ¬ 3 ∣ Nat.card S := by
  obtain ⟨-, a, -, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  exact not_three_dvd_suzuki_order a

theorem odd_rank_one_catalog_five_model_alternatives (S : Type) [Group S] [Finite S]
    [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a) (hcat : Catalog S)
    (hodd : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r S ≤ 1) (h3 : CFSG.pRank 3 S = 1) :
    Nonempty (S ≃* alternatingGroup (Fin 5)) ∨
      (∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ 5 ≤ ℓ ∧ StatedClassicalModel S .PSL 2 ℓ 1) ∨
      (∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel S .PSL 2 2 f) ∨
      StatedClassicalModel S .PSL 3 2 1 ∨
      Nonempty (S ≃* NativeSporadic.J1) := by
  have hno : 2 ≤ CFSG.pRank 3 S → False := fun h => by omega
  rcases hcat with ⟨p, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, hm⟩ | hex | hspor
  ·
    obtain ⟨a, b, hab⟩ := hnab
    exact (hab (commute_of_mulEquiv_zmod e a b)).elim
  ·
    rcases (show n = 5 ∨ 6 ≤ n by omega) with rfl | h6
    · exact Or.inl ⟨e⟩
    · refine (hno ?_).elim
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
      exact CFSG.SectionRank.le_pRank (by norm_num) le_top
        (CFSG.SectionRank.isElemAbelian_sylowThreeAlt h6) (CFSG.SectionRank.card_sylowThreeAlt h6)
  ·
    have hp : p.Prime := hm.1.1
    by_cases hp2 : p = 2
    · subst hp2
      rcases CFSG.QuasithinUnique.Vol2Native.EvenWit.oddRankOneEvenClassical S hodd t n f hm with
        ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl, rfl⟩
      · exact Or.inr (Or.inr (Or.inl ⟨f, hf, hm⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hm)))
    · obtain ⟨rfl, rfl, rfl, hp5⟩ :=
        CFSG.QuasithinUnique.Setup.Family.oddRankOneOddClassical S hodd p hp hp2 t n f hm
      exact Or.inr (Or.inl ⟨p, hp, hp2, hp5, hm⟩)
  ·
    rcases hex with ⟨t, p, f, -, hm⟩ | ⟨t, p, f, -, hm⟩ | ⟨p, f, hm⟩
    · obtain ⟨rfl, rfl, rfl⟩ :=
        CFSG.RankThree.Chevalley.odd_rank_one_Chevalley_exceptional_model_is_binary_triality S
          hodd t p f hm
      exact (hno (CFSG.QuasithinUnique.Setup.Family.trialityTwoHasRankTwo S hm)).elim
    · exact (CFSG.RankThree.Chevalley.odd_rank_one_excludes_all_Ree_Tits_models S hodd t p f
        hm).elim
    · exact (not_three_dvd_card_of_suzukiModel hm (three_dvd_card_of_pRank_eq_one h3)).elim
  ·
    have hSQT : CFSG.IsStronglyQuasithin S := fun r hr hr2 => (hodd r hr hr2).trans (by norm_num)
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (sqt_sporadic_three_rank_one_is_J1 S hSQT (by omega) hspor))))

end CFSG.RankThree.ThinCatalog
