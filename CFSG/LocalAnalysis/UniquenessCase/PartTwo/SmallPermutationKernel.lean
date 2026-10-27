module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

universe u v

theorem sq_le_card_ker_and_not_isCyclic_of_perm
    {p : ℕ} (hp : p.Prime)
    {E : Type u} {X : Type v} [Group E] [Finite E] [Finite X]
    (hexp : ∀ e : E, e ^ p = 1)
    (hcard : Nat.card E = p ^ 3)
    (hperm : ¬ p ^ 2 ∣ (Nat.card X).factorial)
    (φ : E →* Equiv.Perm X) :
    p ^ 2 ≤ Nat.card φ.ker ∧ ¬ IsCyclic φ.ker := by
  have hE : IsPGroup p E :=
    isPGroup_iff_pow_pow_eq_one.mpr fun e => ⟨1, by simpa using hexp e⟩
  have hI : IsPGroup p φ.range :=
    IsPGroup.of_surjective hE φ.rangeRestrict φ.rangeRestrict_surjective
  have hperm' : ¬ p ^ (1 + 1) ∣ Nat.card (Equiv.Perm X) := by
    rw [Nat.card_perm]
    simpa using hperm
  have hle : Nat.card φ.range ≤ p := by
    simpa using card_le_pow_of_isPGroup_of_not_dvd (s := 1) hp hperm' hI
  have hmul : Nat.card φ.ker * Nat.card φ.range = p ^ 3 := by
    simpa [hcard] using Subgroup.card_ker_mul_card_range φ
  have hker : p ^ 2 ≤ Nat.card φ.ker := by
    have hpos : 0 < Nat.card φ.range := Nat.card_pos
    have h : p ^ 2 * Nat.card φ.range ≤ Nat.card φ.ker * Nat.card φ.range := by
      calc
        p ^ 2 * Nat.card φ.range ≤ p ^ 2 * p := Nat.mul_le_mul_left _ hle
        _ = p ^ 3 := by ring
        _ = Nat.card φ.ker * Nat.card φ.range := hmul.symm
    exact Nat.le_of_mul_le_mul_right h hpos
  refine ⟨hker, ?_⟩
  intro hcyc
  have hexpK : Monoid.exponent φ.ker ∣ p :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
      apply Subtype.ext
      simpa using hexp (x : E)
  have hKle : Nat.card φ.ker ≤ p := by
    rw [← @IsCyclic.exponent_eq_card φ.ker _ hcyc]
    exact Nat.le_of_dvd hp.pos hexpK
  have hp2 : p < p ^ 2 := by
    calc
      p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  exact absurd (hker.trans hKle) (not_le.mpr hp2)

theorem sq_le_card_ker_and_not_isCyclic_of_perm_card_eq_prime_add_one
    {p : ℕ} (hp : p = 3 ∨ p = 7)
    {E : Type u} {X : Type v} [Group E] [Finite E] [Finite X]
    (hexp : ∀ e : E, e ^ p = 1)
    (hcard : Nat.card E = p ^ 3)
    (hX : Nat.card X = p + 1)
    (φ : E →* Equiv.Perm X) :
    p ^ 2 ≤ Nat.card φ.ker ∧ ¬ IsCyclic φ.ker := by
  rcases hp with rfl | rfl
  · refine sq_le_card_ker_and_not_isCyclic_of_perm (p := 3) (by norm_num) hexp hcard ?_ φ
    rw [hX]
    decide
  · refine sq_le_card_ker_and_not_isCyclic_of_perm (p := 7) (by norm_num) hexp hcard ?_ φ
    rw [hX]
    decide

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
