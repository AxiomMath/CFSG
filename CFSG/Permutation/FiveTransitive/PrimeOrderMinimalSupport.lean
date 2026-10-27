module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG

namespace FiveTransitive.PrimeOrderMinimalSupport

open Equiv

theorem exists_prime_order_minimal
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) {g : Perm X} (hg : g ∈ P) (hne : g ≠ 1) :
    ∃ (p : ℕ) (u : Perm X), p.Prime ∧ u ∈ P ∧ orderOf u = p ∧
      u ≠ 1 ∧ u.support.card ≤ g.support.card ∧
      (∀ v : Perm X, v ∈ P → v ≠ 1 → u.support.card ≤ v.support.card) := by
  classical
  let _ : Fintype P := Fintype.ofFinite P
  let S := Finset.univ.filter (fun u : P => (u : Perm X) ≠ 1)
  have hS : S.Nonempty := ⟨⟨g, hg⟩, by simp [S, hne]⟩
  obtain ⟨v, hv, hmin⟩ := Finset.exists_min_image S (fun u : P => (u : Perm X).support.card) hS
  have hvne : (v : Perm X) ≠ 1 := (Finset.mem_filter.mp hv).2
  have hminimal : ∀ w : Perm X, w ∈ P → w ≠ 1 → (v : Perm X).support.card ≤ w.support.card := by
    intro w hw hwne
    exact hmin ⟨w, hw⟩ (by simp [S, hwne])
  let Z := Subgroup.zpowers (v : Perm X)
  have hZnt : Nontrivial Z := Z.nontrivial_iff_ne_bot.mpr (Subgroup.zpowers_ne_bot.mpr hvne)
  have hZcard : 1 < Nat.card Z := Finite.one_lt_card_iff_nontrivial.mpr hZnt
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card Z) (by omega)
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, huorder⟩ := exists_prime_orderOf_dvd_card' (G := Z) p hpdvd
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp u.property
  have huP : (u : Perm X) ∈ P := by
    rw [← hk]
    exact P.zpow_mem v.property k
  have huorder' : orderOf (u : Perm X) = p := (Subgroup.orderOf_coe u).trans huorder
  have hune : (u : Perm X) ≠ 1 := by
    intro heq
    rw [heq, orderOf_one] at huorder'
    exact hp.ne_one huorder'.symm
  have hle : (u : Perm X).support.card ≤ (v : Perm X).support.card := by
    rw [← hk]
    exact Finset.card_le_card (Perm.support_zpow_le _ _)
  refine ⟨p, u, hp, huP, huorder', hune, hle.trans (hminimal g hg hne), ?_⟩
  intro w hw hwne
  exact hle.trans (hminimal w hw hwne)

end FiveTransitive.PrimeOrderMinimalSupport

end CFSG
