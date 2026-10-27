module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DGroupQuotientNotTwoGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddSubgroupLeNormalIndexTwo
public meta import Mathlib.GroupTheory.Perm.Support
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.Algebra.Group.End
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Normal `2`-subgroups of `S₄`

Every normal `2`-subgroup of `S₄` lies in the alternating subgroup `A₄`,
and every odd-order subgroup also lies in `A₄`.  This is the reduction
needed to apply the `A₄` no-involution endpoint in the `PGL₂(3)` branch.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

open Equiv

private lemma all_swaps_conjugate :
    ∀ t s : Equiv.Perm (Fin 4), t.support.card = 2 → s.support.card = 2 →
      ∃ g : Equiv.Perm (Fin 4), g * t * g⁻¹ = s := by
  intro t s ht hs
  revert t s ht hs
  decide

set_option maxRecDepth 10000 in
private lemma all_four_cycles_conjugate :
    ∀ t s : Equiv.Perm (Fin 4), t.support.card = 4 → t ^ 2 ≠ 1 →
      s.support.card = 4 → s ^ 2 ≠ 1 →
        ∃ g : Equiv.Perm (Fin 4), g * t * g⁻¹ = s := by
  intro t s ht ht2 hs hs2
  revert t s ht ht2 hs hs2
  decide

set_option maxRecDepth 10000 in
private lemma four_cycles_product_swap :
    ∀ t : Equiv.Perm (Fin 4), t.support.card = 4 → t ^ 2 ≠ 1 →
      ∃ u v : Equiv.Perm (Fin 4),
        u.support.card = 4 ∧ u ^ 2 ≠ 1 ∧
        v.support.card = 4 ∧ v ^ 2 ≠ 1 ∧
          (t * u * v).support.card = 2 := by
  intro t ht ht2
  revert t ht ht2
  decide

private lemma odd_class_swap_or_four_cycle :
    ∀ t : Equiv.Perm (Fin 4), t.sign = -1 →
      t.support.card = 2 ∨ (t.support.card = 4 ∧ t ^ 2 ≠ 1) := by
  intro t ht
  revert t ht
  decide

private lemma sign_ne_one_eq_neg_one :
    ∀ t : Equiv.Perm (Fin 4), t.sign ≠ 1 → t.sign = -1 := by
  intro t ht
  revert t ht
  decide

private theorem not_isPGroup_two_perm_four :
    ¬ IsPGroup 2 (Equiv.Perm (Fin 4)) := by
  intro hP
  have hcard : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card]
    decide
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hP
  have h3 : 3 ∣ 2 ^ n := by
    rw [← hn, hcard]
    norm_num
  have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3
  norm_num at h32

/-- Every normal `2`-subgroup of `A₄` lies in the characteristic Klein
four subgroup. -/
public theorem normal_two_subgroup_le_kleinFour_of_alternatingGroup_four
    (N : Subgroup (alternatingGroup (Fin 4)))
    (hNnormal : N.Normal) (hN2 : IsPGroup 2 N) :
    N ≤ alternatingGroup.kleinFour (Fin 4) := by
  let : N.Normal := hNnormal
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨S : Sylow 2 (alternatingGroup (Fin 4))⟩ :=
    Sylow.nonempty (G := alternatingGroup (Fin 4))
  have hNleS : N ≤ (S : Subgroup (alternatingGroup (Fin 4))) :=
    hN2.le_sylow_of_normal S
  have hS_eq : (S : Subgroup (alternatingGroup (Fin 4))) =
      alternatingGroup.kleinFour (Fin 4) :=
    alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four (by simp) S
  simpa [hS_eq] using hNleS

/-- Every normal `2`-subgroup of `S₄` lies in `A₄`. -/
public theorem normal_two_subgroup_le_alternating_of_perm_four
    (T : Subgroup (Equiv.Perm (Fin 4)))
    (hTnormal : T.Normal) (hT2 : IsPGroup 2 T) :
    T ≤ alternatingGroup (Fin 4) := by
  classical
  intro t htT
  by_contra htA
  have hnotsign : (t : Equiv.Perm (Fin 4)).sign ≠ 1 := by
    intro hs
    exact htA (by rw [Perm.mem_alternatingGroup]; exact hs)
  have hsign : (t : Equiv.Perm (Fin 4)).sign = -1 :=
    sign_ne_one_eq_neg_one (t : Equiv.Perm (Fin 4)) hnotsign
  rcases odd_class_swap_or_four_cycle (t : Equiv.Perm (Fin 4)) hsign with
    htSwap | htFour
  · have hclosure : Subgroup.closure
        ({σ : Equiv.Perm (Fin 4) | σ.IsSwap} : Set _) = ⊤ :=
      Equiv.Perm.closure_isSwap
    have hTtop : T = ⊤ := by
      apply le_antisymm le_top
      rw [← hclosure]
      apply (Subgroup.closure_le _).2
      intro σ hσ
      have hσswap : σ.IsSwap := hσ
      have hσcard : σ.support.card = 2 := Equiv.Perm.card_support_eq_two.mpr hσswap
      rcases all_swaps_conjugate (t : Equiv.Perm (Fin 4)) σ htSwap hσcard with ⟨g, hg⟩
      have hmem := hTnormal.conj_mem (t : Equiv.Perm (Fin 4)) htT g
      simpa [hg] using hmem
    have hwhole : IsPGroup 2 (Equiv.Perm (Fin 4)) := by
      rw [hTtop] at hT2
      exact hT2.of_equiv (Subgroup.topEquiv (G := Equiv.Perm (Fin 4)))
    exact False.elim (not_isPGroup_two_perm_four hwhole)
  · rcases htFour with ⟨hfour, hsquare⟩
    rcases four_cycles_product_swap (t : Equiv.Perm (Fin 4)) hfour hsquare with
      ⟨u, v, hUV⟩
    rcases hUV with ⟨hu1, hu2, hv1, hv2, hprod⟩
    have huT : (u : Equiv.Perm (Fin 4)) ∈ T := by
      rcases all_four_cycles_conjugate (t : Equiv.Perm (Fin 4)) u hfour hsquare hu1 hu2 with ⟨g, hg⟩
      have hmem := hTnormal.conj_mem (t : Equiv.Perm (Fin 4)) htT g
      simpa [hg] using hmem
    have hvT : (v : Equiv.Perm (Fin 4)) ∈ T := by
      rcases all_four_cycles_conjugate (t : Equiv.Perm (Fin 4)) v hfour hsquare hv1 hv2 with ⟨g, hg⟩
      have hmem := hTnormal.conj_mem (t : Equiv.Perm (Fin 4)) htT g
      simpa [hg] using hmem
    have hswapT : (t * u * v : Equiv.Perm (Fin 4)) ∈ T :=
      T.mul_mem (T.mul_mem htT huT) hvT
    have hclosure : Subgroup.closure
        ({σ : Equiv.Perm (Fin 4) | σ.IsSwap} : Set _) = ⊤ :=
      Equiv.Perm.closure_isSwap
    have hTtop : T = ⊤ := by
      apply le_antisymm le_top
      rw [← hclosure]
      apply (Subgroup.closure_le _).2
      intro σ hσ
      have hσswap : σ.IsSwap := hσ
      have hσcard : σ.support.card = 2 := Equiv.Perm.card_support_eq_two.mpr hσswap
      rcases all_swaps_conjugate (t * u * v) σ hprod hσcard with ⟨g, hg⟩
      have hmem := hTnormal.conj_mem (t * u * v) hswapT g
      simpa [hg] using hmem
    have hwhole : IsPGroup 2 (Equiv.Perm (Fin 4)) := by
      rw [hTtop] at hT2
      exact hT2.of_equiv (Subgroup.topEquiv (G := Equiv.Perm (Fin 4)))
    exact False.elim (not_isPGroup_two_perm_four hwhole)

/-- Every odd-order subgroup of `S₄` lies in `A₄`. -/
public theorem odd_order_subgroup_le_alternating_of_perm_four
    (P : Subgroup (Equiv.Perm (Fin 4))) (hPodd : Odd (Nat.card P)) :
    P ≤ alternatingGroup (Fin 4) := by
  let A : Subgroup (Equiv.Perm (Fin 4)) := alternatingGroup (Fin 4)
  have hAnormal : A.Normal := by
    dsimp [A]
    infer_instance
  have hAindex : A.index = 2 := by
    dsimp [A]
    exact alternatingGroup.index_eq_two
  exact odd_card_subgroup_le_normal_index_two A P hAnormal hAindex hPodd

end CFSG.GorensteinWalter
