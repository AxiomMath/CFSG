module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.KInputsLie
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (LieFam811 IsLie811 qPlusPi)

private theorem exists_top_cover_of_mulEquiv {Y T : Type} [Group Y] [Group T]
    (e : Y ⧸ center Y ≃* T) :
    ∃ φ : (⊤ : Subgroup Y) →* T, Function.Surjective φ ∧ φ.ker ≤ center (⊤ : Subgroup Y) := by
  refine ⟨e.toMonoidHom.comp ((QuotientGroup.mk' (center Y)).comp (⊤ : Subgroup Y).subtype),
    fun t => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (center Y) (e.symm t)
    refine ⟨⟨y, mem_top y⟩, ?_⟩
    change e (QuotientGroup.mk' (center Y) y) = t
    rw [hy, MulEquiv.apply_symm_apply]
  · have hx' : (x : Y) ∈ center Y := by simpa using hx
    rw [mem_center_iff] at hx' ⊢
    exact fun g => Subtype.ext (hx' g)

private theorem four_le_rank_of_char_two {n p : ℕ} (hn : n = 6 ∨ n = 7) (hp : p.Prime)
    (hp5 : 5 ≤ p) :
    4 ≤ if (2 : ℕ) = 2 then n - 2 - (if p ∣ n then 1 else 0)
      else n - 1 - (if p ∣ n then 1 else 0) := by
  rcases hn with rfl | rfl
  · have h6 : ¬ p ∣ 6 := fun h => by
      have := Nat.le_of_dvd (by norm_num) h
      interval_cases p
      · norm_num at h
      · norm_num at hp
    simp [h6]
  · split_ifs <;> omega

theorem four_le_pRank_of_lieModel_psl {Y : Type} [Group Y] [Finite Y] {n f p : ℕ}
    (hn : n = 6 ∨ n = 7) (h : LieModel (Y ⧸ center Y) .PSL n 2 f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ f - 1) : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) := by
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have hKcard : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow hKcard
  obtain ⟨φ, hφ, hker⟩ := exists_top_cover_of_mulEquiv
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm)
  obtain ⟨-, -, -, V, -, hV, hcard, -⟩ :=
    CFSG.RankThree.CentralCover.linear_split_prime_central_cover_two_local_rank (⊤ : Subgroup Y)
      Nat.prime_two hp (by omega) (by rw [hKcard]; exact hpq) hn3 φ hφ hker
  exact (four_le_rank_of_char_two hn hp hp5).trans
    (CFSG.SectionRank.le_pRank hp.one_lt le_top hV hcard)

theorem four_le_pRank_of_lieModel_psu {Y : Type} [Group Y] [Finite Y] {n f p : ℕ}
    (hn : n = 6 ∨ n = 7) (h : LieModel (Y ⧸ center Y) .PSU n 2 f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ f + 1) : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) := by
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨⟨-, hf1, -⟩, K, _, -, hK, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by omega)
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨φ, hφ, hker⟩ := exists_top_cover_of_mulEquiv
    (e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by omega)).symm)
  obtain ⟨-, -, -, V, -, hV, hcard⟩ :=
    CFSG.RankThree.Classical2.unitary_split_prime_central_cover_two_local_rank (⊤ : Subgroup Y)
      hU hp (by omega) hpq hn3 φ hφ hker
  exact (four_le_rank_of_char_two hn hp hp5).trans
    (CFSG.SectionRank.le_pRank hp.one_lt le_top hV hcard)

theorem lieL67PlusRank_holds : LieL67PlusRank := by
  intro Y _ _ fam f hfam hY p hp hp5 hpq
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank p (⊤ : Subgroup Y)]
  rcases hfam with rfl | rfl
  · obtain ⟨-, -, -, ⟨h3, hm⟩ | ⟨h3, hm⟩⟩ := hY
    · rw [qPlusPi, if_neg (show ¬ 2 ^ f % 3 = 1 by omega)] at hpq
      exact four_le_pRank_of_lieModel_psl (.inl rfl) hm hp hp5 hpq
    · rw [qPlusPi, if_pos h3] at hpq
      exact four_le_pRank_of_lieModel_psu (.inl rfl) hm hp hp5 hpq
  · obtain ⟨-, -, -, ⟨h3, hm⟩ | ⟨h3, hm⟩⟩ := hY
    · rw [qPlusPi, if_neg (show ¬ 2 ^ f % 3 = 1 by omega)] at hpq
      exact four_le_pRank_of_lieModel_psl (.inr rfl) hm hp hp5 hpq
    · rw [qPlusPi, if_pos h3] at hpq
      exact four_le_pRank_of_lieModel_psu (.inr rfl) hm hp hp5 hpq

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
