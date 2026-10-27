module

public import CFSG.Permutation.FiveTransitive.Degree48LargeSylowNormalizer
public import CFSG.Permutation.FiveTransitive.Degree48LargePrimeFree

public section

namespace CFSG

namespace FiveTransitive.Degree48LargeSylowActual

open MulAction

private theorem constraints
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {p : ℕ} (hp : p = 47 ∨ p = 23 ∨ p = 11) :
    ∃ d k : ℕ, d ∣ (48 / p).factorial * (p - 1) ∧ (48 % p).factorial ∣ d ∧
      k % p = 1 ∧ d * k * p = Nat.card P := by
  apply Degree48LargeSylowNormalizer.constraints_of_prime_free P hcard h5 hnotAlt hp
  intro s hs
  exact Degree48LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs p
    (by rcases hp with rfl | rfl | rfl <;> norm_num)
    (by rcases hp with rfl | rfl | rfl <;> omega)

theorem forty_seven
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    ∃ d k : ℕ, d ∣ 46 ∧ k % 47 = 1 ∧ d * k * 47 = Nat.card P := by
  obtain ⟨d,k,hd,_,hk,he⟩ := constraints P hcard h5 hnotAlt (Or.inl rfl)
  exact ⟨d,k,by norm_num at hd ⊢; exact hd,hk,he⟩

theorem twenty_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    ∃ d k : ℕ, d ∣ 44 ∧ 2 ∣ d ∧ k % 23 = 1 ∧ d * k * 23 = Nat.card P := by
  obtain ⟨d,k,hd,hdiv,hk,he⟩ := constraints P hcard h5 hnotAlt (Or.inr (Or.inl rfl))
  exact ⟨d,k,by norm_num at hd ⊢; exact hd,by norm_num at hd ⊢; exact hdiv,hk,he⟩

theorem eleven
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    ∃ d k : ℕ, d ∣ 240 ∧ 24 ∣ d ∧ k % 11 = 1 ∧ d * k * 11 = Nat.card P := by
  obtain ⟨d,k,hd,hdiv,hk,he⟩ := constraints P hcard h5 hnotAlt (Or.inr (Or.inr rfl))
  exact ⟨d,k,by norm_num at hd ⊢; exact hd,by norm_num at hd ⊢; exact hdiv,hk,he⟩

theorem sylow_eleven_fixed_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (S : Sylow 11 P) : Nat.card (fixedPoints S X) = 4 := by
  have hfree : ∀ s : Set X, s.ncard = 5 → ¬ 11 ∣ Nat.card (fixingSubgroup P s) := by
    intro s hs
    exact Degree48LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs 11
      (by norm_num) (by omega)
  exact Degree48LargeSylowData.sylow_fixed_card P hcard h5 (Or.inr (Or.inr rfl)) hfree S

theorem eleven_normalizer_constraints
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (S : Sylow 11 P) :
    let N := Subgroup.normalizer (S : Set P)
    ∃ d : ℕ, d ∣ 240 ∧ 24 ∣ d ∧ N.index % 11 = 1 ∧
      d * N.index * 11 = Nat.card P ∧ Nat.card N = d * 11 := by
  have hfree : ∀ s : Set X, s.ncard = 5 → ¬ 11 ∣ Nat.card (fixingSubgroup P s) := by
    intro s hs
    exact Degree48LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs 11
      (by norm_num) (by omega)
  obtain ⟨d,k,hd,hdiv,hk,he,hkN,hN⟩ := Degree48LargeSylowNormalizer.constraints_for_sylow
    P hcard h5 hnotAlt (Or.inr (Or.inr rfl)) hfree S
  rw [hkN] at hk he
  refine ⟨d,?_,?_,hk,he,hN⟩
  · norm_num at hd ⊢; exact hd
  · norm_num at hdiv ⊢; exact hdiv

end FiveTransitive.Degree48LargeSylowActual

end CFSG
