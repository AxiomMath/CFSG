module

public import CFSG.RankThree.PartOne.S9.Extraction.Basic
public import CFSG.RankThree.PGroups.SolvableFittingSelfCentralizing
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.RankThree.PartOne.Extract

open Subgroup CFSG
open scoped commutatorElement

theorem exists_prime_core_not_centralized {G : Type*} [Group G] [Finite G] (p : ℕ)
    (N Y : Subgroup G) [N.Normal] (hNs : Group.IsSolvable N) (hO2 : pCore 2 G = ⊥)
    (hpN : ¬ p ∣ Nat.card N) (hYN : Y ≤ N) (hY2 : IsPGroup 2 Y) (hY : Y ≠ ⊥) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ≠ p ∧ ⁅Y, pCore q G⁆ ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  have hself := CFSG.RankThree.PGroups.solvable_fitting_self_centralizing N
  set Y' : Subgroup N := Y.subgroupOf N with hY'
  have h2N : pCore 2 N = ⊥ := by
    have h := map_pCore_subtype_le N 2
    rw [hO2, le_bot_iff] at h
    exact (map_eq_bot_iff_of_injective _ N.subtype_injective).mp h
  have hYc : Y' ≤ centralizer (fittingSubgroup N : Set N) := by
    rw [le_centralizer_iff, CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_le fun r => ?_
    have hrp : (r : ℕ).Prime := Nat.prime_of_mem_primeFactors r.2
    have hrN : (r : ℕ) ∣ Nat.card N := Nat.dvd_of_mem_primeFactors r.2
    by_cases hr2 : (r : ℕ) = 2
    · rw [hr2, h2N]
      exact bot_le
    have hrp' : (r : ℕ) ≠ p := fun h => hpN (h ▸ hrN)
    have hcomm : ⁅Y, pCore (r : ℕ) G⁆ = ⊥ := hcon r hrp hr2 hrp'
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    have hxG : (x : G) ∈ pCore (r : ℕ) G := map_pCore_subtype_le N r ⟨x, hx, rfl⟩
    have hyG : (y : G) ∈ Y := hy
    have h1 : ⁅(y : G), (x : G)⁆ ∈ ⁅Y, pCore (r : ℕ) G⁆ := commutator_mem_commutator hyG hxG
    rw [hcomm, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact Subtype.ext h1
  have hYF : Y' ≤ fittingSubgroup N := hYc.trans hself
  have hY'2 : IsPGroup 2 Y' := hY2.of_equiv (subgroupOfEquivOfLe hYN).symm
  have hY'' : IsPGroup 2 (Y'.subgroupOf (fittingSubgroup N)) :=
    hY'2.of_equiv (subgroupOfEquivOfLe hYF).symm
  obtain ⟨P, hP⟩ := hY''.exists_le_sylow
  have hFnil : Group.IsNilpotent (fittingSubgroup N) := fittingSubgroup_nilpotent
  have hPle := Sylow.map_le_pCore (G := N) (N := fittingSubgroup N) fittingSubgroup_normal hFnil
    2 P
  have hY'le : Y' ≤ pCore 2 N := by
    intro x hx
    apply hPle
    exact ⟨⟨x, hYF hx⟩, hP hx, rfl⟩
  rw [h2N] at hY'le
  apply hY
  rw [eq_bot_iff]
  intro y hy
  have : (⟨y, hYN hy⟩ : N) ∈ Y' := hy
  have h1 := hY'le this
  rw [mem_bot] at h1 ⊢
  exact congrArg Subtype.val h1

end CFSG.RankThree.PartOne.Extract
