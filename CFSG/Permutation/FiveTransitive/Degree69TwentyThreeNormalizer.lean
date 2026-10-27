module

public import CFSG.Permutation.FiveTransitive.Degree69LargePrimeFree
public import CFSG.Permutation.FiveTransitive.Degree69TwentyThreeData
public import CFSG.Permutation.FiveTransitive.Degree31FiveFixerNormalizer
import CFSG.Permutation.FiveTransitive.Degree48LargeSylowCentralizer
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

public section

namespace CFSG

namespace FiveTransitive.Degree69TwentyThreeNormalizer

open MulAction Subgroup

private theorem centralizer_card_dvd_power
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5)
    {p : ℕ} (hp : p = 23)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ p ∣ Nat.card (fixingSubgroup P s))
    (S : Sylow p P) :
    Nat.card (Subgroup.centralizer (S : Set P)) ∣ (69 / p).factorial * p ^ (69 / p) := by
  classical
  let _ : Fact p.Prime := ⟨by subst p; norm_num⟩
  have hScard := Degree69TwentyThreeData.sylow_card P hcard h5 hp hfree S
  let _ : IsCyclic S := isCyclic_of_prime_card hScard
  obtain ⟨u,hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huP : orderOf u.val = p := (Subgroup.orderOf_coe u).trans (hu.trans hScard)
  have htype := Degree69TwentyThreeData.element_cycle_type P hcard h5 hp hfree u.val huP
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
      (69 / p).factorial * p ^ (69 / p) := by
    rw [Equiv.Perm.nat_card_centralizer,htype,hcard]
    subst p; norm_num
  rwa [hc] at hd

private theorem centralizer_card_dvd
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5)
    {p : ℕ} (hp : p = 23)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ p ∣ Nat.card (fixingSubgroup P s))
    (S : Sylow p P) : Nat.card (Subgroup.centralizer (S : Set P)) ∣ p * (69 / p).factorial := by
  have hprime : p.Prime := by subst p; norm_num
  have hbound := ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
    (Subgroup.card_subgroup_dvd_card (Subgroup.centralizer (S : Set P)))) p
  rw [Degree69TwentyThreeData.factorization_eq_one P hcard h5 hp hfree] at hbound
  apply FiveTransitive.Degree48LargeSylowCentralizer.remove_prime_powers hprime Nat.card_pos.ne' (Nat.factorial_ne_zero _)
  · rw [mul_comm]
    exact centralizer_card_dvd_power P hcard h5 hp hfree S
  · exact hbound

private theorem constraints
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5)
    {p : ℕ} (hp : p = 23)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ p ∣ Nat.card (fixingSubgroup P s)) :
    ∃ d k : ℕ, d ∣ (69 / p).factorial * (p - 1) ∧ k % p = 1 ∧
      d * k * p = Nat.card P := by
  classical
  let _ : Fintype P := Fintype.ofFinite P
  let _ : Fact p.Prime := ⟨by subst p; norm_num⟩
  let S : Sylow p P := Sylow.nonempty.some
  have hS := Degree69TwentyThreeData.sylow_card P hcard h5 hp hfree S
  obtain ⟨hc,hr,_,_,hmod,hprod⟩ :=
    Degree31FiveFixerNormalizer.normalizer_constraints P (69 / p).factorial S hS
      (centralizer_card_dvd P hcard h5 hp hfree S)
  exact ⟨_,_,Nat.mul_dvd_mul hc hr,hmod,hprod⟩

theorem actual_constraints
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    ∃ d k : ℕ, d ∣ 132 ∧ k % 23 = 1 ∧ d * k * 23 = Nat.card P := by
  simpa [Nat.factorial] using constraints P hcard h5 (p := 23) rfl (fun s hs =>
    Degree69LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs 23 (by norm_num) (by omega))

end FiveTransitive.Degree69TwentyThreeNormalizer

end CFSG
