module

import CFSG.Permutation.FiveTransitive.Degree24SevenCycle
public import CFSG.Permutation.FiveTransitive.Helpers

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup
open Equiv

namespace FiniteChecks

private def sourceTuple : Fin 5 → Fin 24 :=
  ![0, 1, 2, 3, 7]

private def tripleSwap : Perm (Fin 24) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] *
    List.formPerm [4, 5]

private def comparisonTripleSwap (x y : Fin 24) : Perm (Fin 24) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] *
    List.formPerm [x, y]

private theorem tripleSwap_cycleType :
    tripleSwap.cycleType = {2, 2, 2} := by
  unfold tripleSwap
  rw [Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide)]
  rw [Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide)]
  rw [(List.isCycle_formPerm (by decide : ([0, 1] : List (Fin 24)).Nodup) (by norm_num)).cycleType,
    (List.isCycle_formPerm (by decide : ([2, 3] : List (Fin 24)).Nodup) (by norm_num)).cycleType,
    (List.isCycle_formPerm (by decide : ([4, 5] : List (Fin 24)).Nodup) (by norm_num)).cycleType]
  decide

private theorem tripleSwap_difference_small :
    ∀ x y : Fin 24, 5 ≤ x.val → 5 ≤ y.val → x ≠ y →
      let w := tripleSwap * (comparisonTripleSwap x y)⁻¹
      w ≠ 1 ∧ w.support.card ≤ 5 := by
  decide

private def doubleThreeCycle : Perm (Fin 24) :=
  List.formPerm [0, 1, 2] * List.formPerm [3, 4, 5]

private def comparisonDoubleThreeCycle (x y : Fin 24) : Perm (Fin 24) :=
  List.formPerm [0, 1, 2] * List.formPerm [3, x, y]

private theorem doubleThreeCycle_cycleType :
    doubleThreeCycle.cycleType = {3, 3} := by
  unfold doubleThreeCycle
  rw [Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide)]
  rw [(List.isCycle_formPerm (by decide : ([0, 1, 2] : List (Fin 24)).Nodup) (by norm_num)).cycleType,
    (List.isCycle_formPerm (by decide : ([3, 4, 5] : List (Fin 24)).Nodup) (by norm_num)).cycleType]
  decide

private theorem doubleThreeCycle_difference_small :
    ∀ x y : Fin 24, 5 ≤ x.val → 5 ≤ y.val → x ≠ y →
      let w := doubleThreeCycle *
        (comparisonDoubleThreeCycle x y)⁻¹
      w ≠ 1 ∧ w.support.card ≤ 5 := by
  decide

end FiniteChecks

private theorem alternatingGroup_le_of_tripleSwap_mem
    (P : Subgroup (Equiv.Perm (Fin 24)))
    (h5 : ∀ a b : Fin 5 → Fin 24,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hg : FiniteChecks.tripleSwap ∈ P) :
    alternatingGroup (Fin 24) ≤ P := by
  classical
  obtain ⟨p, hp0, hp1, hp2, hp3, hp7⟩ :=
    FiveTransitive.Degree24Seven.exists_controlled_conjugator P h5
  let x : Fin 24 := (p : Equiv.Perm (Fin 24)) 4
  let y : Fin 24 := (p : Equiv.Perm (Fin 24)) 5
  have hx : 5 ≤ x.val := by
    apply FiveTransitive.Degree24Seven.five_le_image_of_controlled_conjugator
      (p : Equiv.Perm (Fin 24)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hy : 5 ≤ y.val := by
    apply FiveTransitive.Degree24Seven.five_le_image_of_controlled_conjugator
      (p : Equiv.Perm (Fin 24)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hxy : x ≠ y :=
    (p : Equiv.Perm (Fin 24)).injective.ne (by decide)
  let h : Equiv.Perm (Fin 24) :=
    (p : Equiv.Perm (Fin 24)) * FiniteChecks.tripleSwap *
      (p : Equiv.Perm (Fin 24))⁻¹
  have hh : h = FiniteChecks.comparisonTripleSwap x y := by
    change
      (p : Equiv.Perm (Fin 24)) * FiniteChecks.tripleSwap *
          (p : Equiv.Perm (Fin 24))⁻¹ =
        FiniteChecks.comparisonTripleSwap x y
    rw [← Equiv.permCongr_eq_mul, FiniteChecks.tripleSwap,
      Equiv.permCongr_mul, Equiv.permCongr_mul,
      Helpers.permCongr_formPerm, Helpers.permCongr_formPerm,
      Helpers.permCongr_formPerm]
    simp [FiniteChecks.comparisonTripleSwap, x, y,
      hp0, hp1, hp2, hp3]
  let w :=
    FiniteChecks.tripleSwap *
      (FiniteChecks.comparisonTripleSwap x y)⁻¹
  obtain ⟨hwNe, hwsupport⟩ :=
    FiniteChecks.tripleSwap_difference_small x y hx hy hxy
  have hwP : w ∈ P := by
    apply P.mul_mem hg
    apply P.inv_mem
    rw [← hh]
    exact P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)
  exact Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
    (Fin 24) P h5 (by norm_num) hwP hwNe hwsupport

private theorem alternatingGroup_le_of_doubleThreeCycle_mem
    (P : Subgroup (Equiv.Perm (Fin 24)))
    (h5 : ∀ a b : Fin 5 → Fin 24,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hg : FiniteChecks.doubleThreeCycle ∈ P) :
    alternatingGroup (Fin 24) ≤ P := by
  classical
  obtain ⟨p, hp0, hp1, hp2, hp3, hp7⟩ :=
    FiveTransitive.Degree24Seven.exists_controlled_conjugator P h5
  let x : Fin 24 := (p : Equiv.Perm (Fin 24)) 4
  let y : Fin 24 := (p : Equiv.Perm (Fin 24)) 5
  have hx : 5 ≤ x.val := by
    apply FiveTransitive.Degree24Seven.five_le_image_of_controlled_conjugator
      (p : Equiv.Perm (Fin 24)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hy : 5 ≤ y.val := by
    apply FiveTransitive.Degree24Seven.five_le_image_of_controlled_conjugator
      (p : Equiv.Perm (Fin 24)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hxy : x ≠ y :=
    (p : Equiv.Perm (Fin 24)).injective.ne (by decide)
  let h : Equiv.Perm (Fin 24) :=
    (p : Equiv.Perm (Fin 24)) *
      FiniteChecks.doubleThreeCycle *
      (p : Equiv.Perm (Fin 24))⁻¹
  have hh : h = FiniteChecks.comparisonDoubleThreeCycle x y := by
    change
      (p : Equiv.Perm (Fin 24)) *
          FiniteChecks.doubleThreeCycle *
          (p : Equiv.Perm (Fin 24))⁻¹ =
        FiniteChecks.comparisonDoubleThreeCycle x y
    rw [← Equiv.permCongr_eq_mul,
      FiniteChecks.doubleThreeCycle, Equiv.permCongr_mul,
      Helpers.permCongr_formPerm, Helpers.permCongr_formPerm]
    simp [FiniteChecks.comparisonDoubleThreeCycle, x, y,
      hp0, hp1, hp2, hp3]
  let w :=
    FiniteChecks.doubleThreeCycle *
      (FiniteChecks.comparisonDoubleThreeCycle x y)⁻¹
  obtain ⟨hwNe, hwsupport⟩ :=
    FiniteChecks.doubleThreeCycle_difference_small
      x y hx hy hxy
  have hwP : w ∈ P := by
    apply P.mul_mem hg
    apply P.inv_mem
    rw [← hh]
    exact P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)
  exact Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
    (Fin 24) P h5 (by norm_num) hwP hwNe hwsupport

theorem alternatingGroup_le_of_prime_order_support_six
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    {g : Equiv.Perm X} (hg : g ∈ P)
    {q : ℕ} (hq : q.Prime) (hgorder : orderOf g = q)
    (hgsupport : g.support.card = 6) :
    alternatingGroup X ≤ P := by
  classical
  let e₀ : X ≃ Fin 24 := Fintype.equivFinOfCardEq hcard
  let g₁ : Equiv.Perm (Fin 24) := e₀.permCongr g
  have hg₁order : orderOf g₁ = q := by
    calc
      orderOf g₁ = orderOf g := e₀.permCongrHom.orderOf_eq g
      _ = q := hgorder
  have hg₁prime : (orderOf g₁).Prime := by
    rw [hg₁order]
    exact hq
  have hsupportMap :
      g₁.support = g.support.map e₀.toEmbedding := by
    ext y
    simp [g₁, Equiv.Perm.mem_support,
      Equiv.permCongr_apply]
    constructor
    · intro h h'
      apply h
      rw [h', e₀.apply_symm_apply]
    · intro h h'
      apply h
      apply e₀.injective
      simpa using h'
  have hg₁support : g₁.support.card = 6 := by
    rw [hsupportMap, Finset.card_map, hgsupport]
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order hg₁prime
  have hsum := g₁.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hg₁order, hg₁support] at hsum
  have hqle : q ≤ 6 := by
    nlinarith [Nat.zero_le m]
  interval_cases q
  all_goals norm_num at hq
  · have hm' : m + 1 = 3 := by omega
    have hcycle :
        g₁.cycleType =
          FiniteChecks.tripleSwap.cycleType := by
      rw [hm, hg₁order, hm',
        FiniteChecks.tripleSwap_cycleType]
      norm_num
    apply FiveTransitive.Degree24Seven.alternatingGroup_le_of_cycleType_eq
      X P hcard h5 hg FiniteChecks.tripleSwap
    · simpa [e₀, g₁] using hcycle
    · exact alternatingGroup_le_of_tripleSwap_mem
  · have hm' : m + 1 = 2 := by omega
    have hcycle :
        g₁.cycleType =
          FiniteChecks.doubleThreeCycle.cycleType := by
      rw [hm, hg₁order, hm',
        FiniteChecks.doubleThreeCycle_cycleType]
      norm_num
    apply FiveTransitive.Degree24Seven.alternatingGroup_le_of_cycleType_eq
      X P hcard h5 hg FiniteChecks.doubleThreeCycle
    · simpa [e₀, g₁] using hcycle
    · exact alternatingGroup_le_of_doubleThreeCycle_mem
  · omega

end FiveTransitive.Degree24

end CFSG
