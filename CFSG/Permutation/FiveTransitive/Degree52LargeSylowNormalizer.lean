module

public import CFSG.Permutation.FiveTransitive.Degree52LargeSylowData
public import Mathlib.GroupTheory.Perm.Centralizer
import CFSG.Permutation.FiveTransitive.Degree48LargeSylowCentralizer
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG

namespace FiveTransitive.Degree52LargeSylowNormalizer

open MulAction Subgroup

private theorem centralizer_card_dvd_power
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5)
    {p : ℕ} (hp : p = 17 ∨ p = 13)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ p ∣ Nat.card (fixingSubgroup P s))
    (S : Sylow p P) :
    Nat.card (Subgroup.centralizer (S : Set P)) ∣ (52 / p).factorial * p ^ (52 / p) := by
  classical
  let _ : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> norm_num⟩
  have hScard := Degree52LargeSylowData.sylow_card P hcard h5 hp hfree S
  let _ : IsCyclic S := isCyclic_of_prime_card hScard
  obtain ⟨u,hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huP : orderOf u.val = p := (Subgroup.orderOf_coe u).trans (hu.trans hScard)
  have htype := Degree52LargeSylowData.element_cycle_type P hcard h5 hp hfree u.val huP
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
      (52 / p).factorial * p ^ (52 / p) := by
    rw [Equiv.Perm.nat_card_centralizer,htype,hcard]
    rcases hp with rfl | rfl <;> norm_num
  rwa [hc] at hd

theorem centralizer_card_dvd
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5)
    {p : ℕ} (hp : p = 17 ∨ p = 13)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ p ∣ Nat.card (fixingSubgroup P s))
    (S : Sylow p P) : Nat.card (Subgroup.centralizer (S : Set P)) ∣ p * (52 / p).factorial := by
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hbound := ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
    (Subgroup.card_subgroup_dvd_card (Subgroup.centralizer (S : Set P)))) p
  rw [Degree52LargeSylowData.factorization_eq_one P hcard h5 hp hfree] at hbound
  apply FiveTransitive.Degree48LargeSylowCentralizer.remove_prime_powers hprime Nat.card_pos.ne' (Nat.factorial_ne_zero _)
  · rw [mul_comm]
    exact centralizer_card_dvd_power P hcard h5 hp hfree S
  · exact hbound

end FiveTransitive.Degree52LargeSylowNormalizer

end CFSG
