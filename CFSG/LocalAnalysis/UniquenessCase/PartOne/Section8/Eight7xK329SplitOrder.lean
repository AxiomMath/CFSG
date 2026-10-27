module

public import CFSG.Adapters.LieModelOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel)
open CFSG.Open (StatedLieTag)
open CFSG.EvenSmallLie.CatalogOrders (lieOrd lieExp lieMin lieAdm searchTags lieSearch
  lieSearch_sound le_lieExp_add_one)

theorem k329_card_psl28 {Y : Type} [Group Y] (hY : LieModel Y .PSL 2 2 3) :
    Nat.card Y = 504 := by
  rw [LieModel.card_eq_lieOrd (by norm_num) hY]
  decide

theorem k329_primes_dvd_504 (p : ℕ) (hp : p.Prime) (hd : p ∣ 504) : p ∈ [2, 3, 7] := by
  have h : p ∣ 2 ^ 3 * 3 ^ 2 * 7 := by norm_num; exact hd
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)
      simp [this]
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h2)
      simp [this]
  · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).1 h1
    simp [this]

theorem k329_search_504 :
    lieSearch [2, 3, 7] 504
      (fun t n q v => decide (v = 504 → t = .PSL ∧ n = 2 ∧ q = 8)) = true := by
  decide +kernel

theorem k329_S2_order504 {Y : Type} [Group Y] {t : StatedLieTag} {n r e : ℕ} (hn : n ≠ 0)
    (h : LieModel Y t n r e) (hY : Nat.card Y = 504) : t = .PSL ∧ n = 2 ∧ r ^ e = 8 := by
  have hord : lieOrd t n (r ^ e) = 504 := by
    rw [← LieModel.card_eq_lieOrd hn h]
    exact hY
  have hcl := h.statedClassicalModel_of_ne_zero hn
  have hadm := hcl.1
  have hp : r.Prime := hadm.1
  have hf : 1 ≤ e := hadm.2.1
  have key : t ∈ searchTags ∧ lieMin t ≤ n ∧ n ≤ lieExp t n + 1 ∧ lieAdm t r e = true := by
    cases t
    case PSL =>
      exact ⟨by decide, hadm.2.2.1, le_lieExp_add_one hadm.2.2.1 (by simp), rfl⟩
    case PSU =>
      exact ⟨by decide, hadm.2.2.1, le_lieExp_add_one hadm.2.2.1 (by simp), rfl⟩
    case PSp =>
      exact ⟨by decide, hadm.2.2.1, le_lieExp_add_one hadm.2.2.1 (by simp), rfl⟩
    case POmegaOdd =>
      exact ⟨by decide, hadm.2.2.1, le_lieExp_add_one hadm.2.2.1 (by simp), rfl⟩
    case POmegaPlus =>
      exact ⟨by decide, hadm.2.2, le_lieExp_add_one hadm.2.2 (by simp), rfl⟩
    case POmegaMinus =>
      exact ⟨by decide, hadm.2.2, le_lieExp_add_one hadm.2.2 (by simp), rfl⟩
    all_goals exact hcl.2.elim
  obtain ⟨hst, hmin, hnB, hla⟩ := key
  have hsound := lieSearch_sound (by norm_num) k329_primes_dvd_504 k329_search_504 hst hp hf hmin
    hnB hla (hord ▸ dvd_refl _)
  have := of_decide_eq_true hsound
  exact this hord

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
