module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.KInputsLie
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811Centre
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
  (LieFam811 IsLieFam811 IsLie811 qPlusPi qMinusPi center_eq_bot_of_isLie811_of_ne
    card_center_dvd_of_isLie811_l7)

private theorem four_le_pRank_of_statedClassicalModel_psl {X : Type} [Group X] [Finite X]
    {n r f : ℕ} (hr2 : r ≠ 2) (hn : 4 ≤ n) (h : StatedClassicalModel X .PSL n r f) :
    4 ≤ CFSG.Open.pRank r (⊤ : Subgroup X) := by
  rcases (CFSG.SectionRank.classical_model_rank (p := r) hr2 h).2.2 with
    ⟨-, h⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | h4
  · rcases h with ⟨h2, -⟩ | ⟨h3, -⟩ | h4
    · omega
    · omega
    · exact h4
  · cases ht
  · cases ht
  · exact h4

private theorem four_le_pRank_of_statedClassicalModel_psu {X : Type} [Group X] [Finite X]
    {n r f : ℕ} (hr2 : r ≠ 2) (hn : 4 ≤ n) (h : StatedClassicalModel X .PSU n r f) :
    4 ≤ CFSG.Open.pRank r (⊤ : Subgroup X) := by
  rcases (CFSG.SectionRank.classical_model_rank (p := r) hr2 h).2.2 with
    ⟨ht, -⟩ | ⟨-, h⟩ | ⟨ht, -⟩ | h4
  · cases ht
  · rcases h with ⟨h3, -⟩ | h4
    · omega
    · exact h4
  · cases ht
  · exact h4

private theorem four_le_pRank_of_statedClassicalModel_psp {X : Type} [Group X] [Finite X]
    {n r f : ℕ} (hr2 : r ≠ 2) (hn : 3 ≤ n) (h : StatedClassicalModel X .PSp n r f) :
    4 ≤ CFSG.Open.pRank r (⊤ : Subgroup X) := by
  rcases (CFSG.SectionRank.classical_model_rank (p := r) hr2 h).2.2 with
    ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨-, h⟩ | h4
  · cases ht
  · cases ht
  · rcases h with ⟨h2, -⟩ | h4
    · omega
    · exact h4
  · exact h4

private theorem four_le_pRank_of_statedClassicalModel_orthogonal {X : Type} [Group X] [Finite X]
    {t : StatedLieTag} {n r f : ℕ} (hr2 : r ≠ 2)
    (ht : t = .POmegaOdd ∨ t = .POmegaMinus) (h : StatedClassicalModel X t n r f) :
    4 ≤ CFSG.Open.pRank r (⊤ : Subgroup X) := by
  rcases (CFSG.SectionRank.classical_model_rank (p := r) hr2 h).2.2 with
    ⟨ht', -⟩ | ⟨ht', -⟩ | ⟨ht', -⟩ | h4
  · rcases ht with rfl | rfl <;> cases ht'
  · rcases ht with rfl | rfl <;> cases ht'
  · rcases ht with rfl | rfl <;> cases ht'
  · exact h4

private theorem seven_not_dvd_pow_add_one (f : ℕ) : ¬ 7 ∣ 7 ^ f + 1 := by
  rcases f with _ | f
  · norm_num
  · intro h
    have h1 : 7 ∣ 1 := by
      have h2 : 7 ∣ 7 ^ (f + 1) := dvd_pow_self 7 (Nat.succ_ne_zero f)
      simpa using Nat.dvd_sub h h2
    norm_num at h1

private theorem gcd_seven_qPlusPi_seven (f : ℕ) : Nat.gcd 7 (qPlusPi 7 f) = 1 := by
  have hmod : ∀ n : ℕ, 7 ^ n % 3 = 1 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih => rw [pow_succ, Nat.mul_mod, ih]
  have hq : qPlusPi 7 f = 7 ^ f + 1 := by simp [qPlusPi, hmod f]
  rw [hq]
  rcases Nat.prime_seven.eq_one_or_self_of_dvd (Nat.gcd 7 (7 ^ f + 1))
    (Nat.gcd_dvd_left 7 (7 ^ f + 1)) with h | h
  · exact h
  · have hbad := Nat.gcd_dvd_right 7 (7 ^ f + 1)
    rw [h] at hbad
    exact absurd hbad (seven_not_dvd_pow_add_one f)

private theorem not_dvd_card_center_of_isLie811
    {Y : Type} [Group Y] [Finite Y] {fam : LieFam811} {r f : ℕ} (hY : IsLie811 Y fam r f)
    (hr : r.Prime) (hr2 : r ≠ 2) : ¬ r ∣ Nat.card (center Y) := by
  rcases eq_or_ne fam .l7 with h7 | h7
  · subst h7
    have hdvd := card_center_dvd_of_isLie811_l7 hY
    rcases eq_or_ne r 7 with hr7 | hr7
    · subst hr7
      rw [gcd_seven_qPlusPi_seven f] at hdvd
      rw [Nat.dvd_one.1 hdvd]
      norm_num
    · intro h
      have h77 : r ∣ 7 := h.trans (hdvd.trans (Nat.gcd_dvd_left 7 (qPlusPi r f)))
      exact hr7 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_seven).1 h77)
  · have hsp : fam = .psp6 → r ^ f ≠ 2 := by
      intro _ hq
      have hf : f ≠ 0 := by rintro rfl; simp at hq
      have hdvd : r ∣ 2 := by
        rw [← hq]
        exact dvd_pow_self r hf
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 hdvd)
    rw [center_eq_bot_of_isLie811_of_ne hY h7 hsp, Subgroup.card_bot, Nat.dvd_one]
    exact hr.ne_one

private theorem four_le_pRank_of_isLieFam811 {X : Type} [Group X] [Finite X]
    {fam : LieFam811} {r f : ℕ} (hfam : IsLieFam811 X fam r f) (hr2 : r ≠ 2) :
    4 ≤ CFSG.Open.pRank r (⊤ : Subgroup X) := by
  rcases fam with _ | _ | _ | _ | _ | _
  · obtain ⟨-, -, hm⟩ := hfam
    exact four_le_pRank_of_statedClassicalModel_psp hr2 (by norm_num)
      (hm.statedClassicalModel (by decide))
  · obtain ⟨-, -, -, hm⟩ := hfam
    exact four_le_pRank_of_statedClassicalModel_orthogonal hr2 (Or.inl rfl)
      (hm.statedClassicalModel (by decide))
  · obtain ⟨-, -, hm⟩ := hfam
    exact four_le_pRank_of_statedClassicalModel_orthogonal hr2 (Or.inr rfl)
      (hm.statedClassicalModel (by decide))
  · obtain ⟨-, -, hm⟩ := hfam
    rcases hm with ⟨-, hm⟩ | ⟨-, hm⟩
    · exact four_le_pRank_of_statedClassicalModel_psl hr2 (by norm_num)
        (hm.statedClassicalModel (by decide))
    · exact four_le_pRank_of_statedClassicalModel_psu hr2 (by norm_num)
        (hm.statedClassicalModel (by decide))
  all_goals
    obtain ⟨-, hm⟩ := hfam
    rcases hm with ⟨-, hm⟩ | ⟨-, hm⟩
    · exact four_le_pRank_of_statedClassicalModel_psl hr2 (by norm_num)
        (hm.statedClassicalModel (by decide))
    · exact four_le_pRank_of_statedClassicalModel_psu hr2 (by norm_num)
        (hm.statedClassicalModel (by decide))

theorem lieOddCharRank_holds :
    LieOddCharRank := by
  intro Y _ _ fam r f hY hr2
  have hfam : IsLieFam811 (Y ⧸ center Y) fam r f := hY.2.2
  have hr : r.Prime := by
    rcases fam with _ | _ | _ | _ | _ | _ <;> exact hfam.1
  haveI : Fact r.Prime := ⟨hr⟩
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank r (⊤ : Subgroup Y),
    ← CFSG.SectionRank.pRank_quotient_eq (center Y) (not_dvd_card_center_of_isLie811 hY hr hr2)]
  exact four_le_pRank_of_isLieFam811 hfam hr2

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3