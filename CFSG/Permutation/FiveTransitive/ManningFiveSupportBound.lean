module

public import CFSG.Permutation.FiveTransitive.PrimeOrderMinimalSupport
public import CFSG.Permutation.FiveTransitive.InvolutionMinimalSupportBound
public import CFSG.Permutation.FiveTransitive.ManningLargePrimeBound
public import CFSG.Permutation.FiveTransitive.ManningThreeCycleBound

public section

namespace CFSG

namespace FiveTransitive.ManningFiveSupportBound

open Equiv

theorem bound_of_five_transitive
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (g : Perm X) (hg : g ∈ P) (hm : 8 ≤ g.support.card)
    (hmin : ∀ w : Perm X, w ∈ P → w ≠ 1 → g.support.card ≤ w.support.card) :
    Fintype.card X ≤ 2 * g.support.card := by
  classical
  by_cases hinv : ∃ s : Perm X, s ∈ P ∧ orderOf s = 2 ∧ s.support.card = g.support.card
  · obtain ⟨s, hsP, hs, hsm⟩ := hinv
    have hb := InvolutionMinimalSupportBound.degree_le_two_mul_support P h5 s hsP hs
      (by omega) (by simpa only [hsm] using hmin)
    simpa only [hsm] using hb
  have hno : ∀ s : Perm X, s ∈ P → orderOf s = 2 → s.support.card ≠ g.support.card := by
    intro s hsP hs hsm
    exact hinv ⟨s, hsP, hs, hsm⟩
  have hgne : g ≠ 1 := by
    intro h
    simp only [h, Perm.support_one, Finset.card_empty] at hm
    omega
  obtain ⟨p,u,hp,huP,huo,hune,hum,humin⟩ :=
    PrimeOrderMinimalSupport.exists_prime_order_minimal P hg hgne
  have humeq : u.support.card = g.support.card := Nat.le_antisymm hum (hmin u huP hune)
  by_cases hp2 : p = 2
  · exact (hno u huP (huo.trans hp2) humeq).elim
  by_cases hp3 : p = 3
  · have hb := ManningThreeCycleBound.degree_le_two_mul_support P h5 u huP
      (huo.trans hp3) (by omega) humin
      (by simpa only [humeq] using hno)
    simpa only [humeq] using hb
  have hp4 : p ≠ 4 := by intro h; rw [h] at hp; exact (by decide : ¬ Nat.Prime 4) hp
  have hp5 : 5 ≤ orderOf u := by have := hp.two_le; omega
  have hb := ManningLargePrimeBound.degree_lt_two_mul_support P h5 u huP
    (by simpa only [huo] using hp) hp5 (by omega) humin
  omega

end FiveTransitive.ManningFiveSupportBound

end CFSG
