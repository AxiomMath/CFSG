module

public import CFSG.Permutation.FiveTransitive.Degree39LargeSylowData
public import CFSG.Permutation.FiveTransitive.Degree31FiveFixerNormalizer
import CFSG.Permutation.FiveTransitive.Degree48LargeSylowCentralizer
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

public section

namespace CFSG

namespace FiveTransitive.Degree39LargeSylowNormalizer

open MulAction Subgroup

private theorem centralizer_card_dvd_power
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5)
    {p : ℕ} (hp : p = 19 ∨ p = 13)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ p ∣ Nat.card (fixingSubgroup P s))
    (S : Sylow p P) :
    Nat.card (Subgroup.centralizer (S : Set P)) ∣ (39 / p).factorial * p ^ (39 / p) := by
  classical
  let _ : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> norm_num⟩
  have hScard := Degree39LargeSylowData.sylow_card P hcard h5 hp hfree S
  let _ : IsCyclic S := isCyclic_of_prime_card hScard
  obtain ⟨u,hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huP : orderOf u.val = p := (Subgroup.orderOf_coe u).trans (hu.trans hScard)
  have htype := Degree39LargeSylowData.element_cycle_type P hcard h5 hp hfree u.val huP
  let C := Subgroup.centralizer (S : Set P)
  let g : Equiv.Perm X := u.val.val
  let f : C →* Equiv.Perm X := P.subtype.comp C.subtype
  have hmem : ∀ c : C, f c ∈ Subgroup.centralizer ({g} : Set (Equiv.Perm X)) := by
    intro c
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val ((c.property u.val u.property).symm)
  let ff := f.codRestrict (Subgroup.centralizer ({g} : Set (Equiv.Perm X))) hmem
  have hinj : Function.Injective ff := by
    intro a b he
    have hh : f a = f b := congrArg
      (fun c : Subgroup.centralizer ({g} : Set (Equiv.Perm X)) => c.val) he
    exact Subtype.ext (Subtype.ext hh)
  have hd := Subgroup.card_dvd_of_injective ff hinj
  have hc : Nat.card (Subgroup.centralizer ({g} : Set (Equiv.Perm X))) =
      (39 / p).factorial * p ^ (39 / p) := by
    rw [Equiv.Perm.nat_card_centralizer,htype,hcard]
    rcases hp with rfl | rfl <;> norm_num
  rwa [hc] at hd

theorem centralizer_card_dvd
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5)
    {p : ℕ} (hp : p = 19 ∨ p = 13)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ p ∣ Nat.card (fixingSubgroup P s))
    (S : Sylow p P) : Nat.card (Subgroup.centralizer (S : Set P)) ∣ p * (39 / p).factorial := by
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hbound := ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
    (Subgroup.card_subgroup_dvd_card (Subgroup.centralizer (S : Set P)))) p
  rw [Degree39LargeSylowData.factorization_eq_one P hcard h5 hp hfree] at hbound
  apply FiveTransitive.Degree48LargeSylowCentralizer.remove_prime_powers hprime Nat.card_pos.ne' (Nat.factorial_ne_zero _)
  · rw [mul_comm]
    exact centralizer_card_dvd_power P hcard h5 hp hfree S
  · exact hbound

theorem constraints
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5)
    {p : ℕ} (hp : p = 19 ∨ p = 13)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ p ∣ Nat.card (fixingSubgroup P s)) :
    ∃ d k : ℕ, d ∣ (39 / p).factorial * (p - 1) ∧ k % p = 1 ∧
      d * k * p = Nat.card P := by
  classical
  let _ : Fintype P := Fintype.ofFinite P
  let _ : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> norm_num⟩
  let S : Sylow p P := Sylow.nonempty.some
  have hS := Degree39LargeSylowData.sylow_card P hcard h5 hp hfree S
  obtain ⟨hc,hr,_,_,hmod,hprod⟩ :=
    Degree31FiveFixerNormalizer.normalizer_constraints P (39 / p).factorial S hS
      (centralizer_card_dvd P hcard h5 hp hfree S)
  exact ⟨_,_,Nat.mul_dvd_mul hc hr,hmod,hprod⟩

end FiveTransitive.Degree39LargeSylowNormalizer

end CFSG
