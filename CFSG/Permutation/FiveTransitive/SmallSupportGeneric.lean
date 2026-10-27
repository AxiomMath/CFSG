module

public import CFSG.Permutation.FiveTransitive.Helpers
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG

namespace FiveTransitive.SmallSupportGeneric

open MulAction Subgroup
open Equiv

@[expose] def sourceTuple8 : Fin 5 → Fin 8 :=
  ![0, 1, 2, 3, 7]

@[expose] def targetTuple8 : Fin 5 → Fin 8 :=
  ![0, 1, 2, 3, 4]

theorem sourceTuple8_injective :
    Function.Injective sourceTuple8 := by
  decide

theorem targetTuple8_injective :
    Function.Injective targetTuple8 := by
  decide

theorem four_ne_sourceTuple8 (i : Fin 5) :
    (4 : Fin 8) ≠ sourceTuple8 i := by
  fin_cases i <;> decide

theorem five_ne_sourceTuple8 (i : Fin 5) :
    (5 : Fin 8) ≠ sourceTuple8 i := by
  fin_cases i <;> decide

private def tripleSwap8 : Perm (Fin 8) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] *
    List.formPerm [4, 5]

private def doubleThreeCycle8 : Perm (Fin 8) :=
  List.formPerm [0, 1, 2] *
    List.formPerm [3, 4, 5]

private theorem tripleSwap8_cycleType :
    tripleSwap8.cycleType = {2, 2, 2} := by
  unfold tripleSwap8
  rw [Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide)]
  rw [Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide)]
  rw [(List.isCycle_formPerm (by decide : ([0, 1] : List (Fin 8)).Nodup) (by norm_num)).cycleType,
    (List.isCycle_formPerm (by decide : ([2, 3] : List (Fin 8)).Nodup) (by norm_num)).cycleType,
    (List.isCycle_formPerm (by decide : ([4, 5] : List (Fin 8)).Nodup) (by norm_num)).cycleType]
  decide

private theorem doubleThreeCycle8_cycleType :
    doubleThreeCycle8.cycleType = {3, 3} := by
  unfold doubleThreeCycle8
  rw [Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide)]
  rw [(List.isCycle_formPerm (by decide : ([0, 1, 2] : List (Fin 8)).Nodup) (by norm_num)).cycleType,
    (List.isCycle_formPerm (by decide : ([3, 4, 5] : List (Fin 8)).Nodup) (by norm_num)).cycleType]
  decide

private def tripleSwap
    {X : Type} [DecidableEq X] (e : Fin 8 ↪ X) :
    Perm X :=
  List.formPerm [e 0, e 1] *
    List.formPerm [e 2, e 3] *
    List.formPerm [e 4, e 5]

private def doubleThreeCycle
    {X : Type} [DecidableEq X] (e : Fin 8 ↪ X) :
    Perm X :=
  List.formPerm [e 0, e 1, e 2] *
    List.formPerm [e 3, e 4, e 5]

private theorem tripleSwap_eq_viaEmbedding
    {X : Type} [Fintype X] [DecidableEq X]
    (e : Fin 8 ↪ X) :
    tripleSwap e = tripleSwap8.viaEmbedding e := by
  classical
  ext x
  by_cases hx : x ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hx
    fin_cases i <;>
      simp [tripleSwap, tripleSwap8,
        Equiv.Perm.viaEmbedding_apply,
        Equiv.swap_apply_def, e.injective.eq_iff]
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem
      tripleSwap8 e x hx]
    have hne (i : Fin 8) : x ≠ e i := by
      intro h
      exact hx ⟨i, h.symm⟩
    have hne0 := hne 0
    have hne1 := hne 1
    have hne2 := hne 2
    have hne3 := hne 3
    have hne4 := hne 4
    have hne5 := hne 5
    simp [tripleSwap, Equiv.swap_apply_def,
      hne0, hne1, hne2, hne3, hne4, hne5]

private theorem doubleThreeCycle_eq_viaEmbedding
    {X : Type} [Fintype X] [DecidableEq X]
    (e : Fin 8 ↪ X) :
    doubleThreeCycle e =
      doubleThreeCycle8.viaEmbedding e := by
  classical
  ext x
  by_cases hx : x ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hx
    fin_cases i <;>
      simp [doubleThreeCycle, doubleThreeCycle8,
        Equiv.Perm.viaEmbedding_apply,
        Equiv.swap_apply_def, e.injective.eq_iff]
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem
      doubleThreeCycle8 e x hx]
    have hne (i : Fin 8) : x ≠ e i := by
      intro h
      exact hx ⟨i, h.symm⟩
    have hne0 := hne 0
    have hne1 := hne 1
    have hne2 := hne 2
    have hne3 := hne 3
    have hne4 := hne 4
    have hne5 := hne 5
    simp [doubleThreeCycle, Equiv.swap_apply_def,
      hne0, hne1, hne2, hne3, hne4, hne5]

private theorem tripleSwap_cycleType
    {X : Type} [Fintype X] [DecidableEq X]
    (e : Fin 8 ↪ X) :
    (tripleSwap e).cycleType = {2, 2, 2} := by
  rw [tripleSwap_eq_viaEmbedding]
  simpa [Equiv.Perm.viaEmbedding] using
    tripleSwap8_cycleType

private theorem doubleThreeCycle_cycleType
    {X : Type} [Fintype X] [DecidableEq X]
    (e : Fin 8 ↪ X) :
    (doubleThreeCycle e).cycleType = {3, 3} := by
  rw [doubleThreeCycle_eq_viaEmbedding]
  simpa [Equiv.Perm.viaEmbedding] using
    doubleThreeCycle8_cycleType

theorem alternatingGroup_le_of_cycleType_eq
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    {g : Equiv.Perm X} (hg : g ∈ P)
    (c : Equiv.Perm X)
    (hcycleType : g.cycleType = c.cycleType)
    (hforce :
      ∀ Q : Subgroup (Equiv.Perm X),
        (∀ a b : Fin 5 → X,
          Function.Injective a → Function.Injective b →
          ∃ q : Q, ∀ i, q • a i = b i) →
        c ∈ Q → alternatingGroup X ≤ Q) :
    alternatingGroup X ≤ P := by
  classical
  obtain ⟨k, hk⟩ :=
    isConj_iff.mp
      (Equiv.Perm.isConj_of_cycleType_eq hcycleType)
  let Q : Subgroup (Equiv.Perm X) :=
    P.map (MulAut.conj k).toMonoidHom
  have hc : c ∈ Q := by
    rw [Subgroup.mem_map]
    exact ⟨g, hg, hk⟩
  have h5Q :
      ∀ a b : Fin 5 → X,
        Function.Injective a → Function.Injective b →
        ∃ q : Q, ∀ i, q • a i = b i := by
    intro a b ha hb
    have ha' :
        Function.Injective (fun i => k⁻¹ (a i)) :=
      k⁻¹.injective.comp ha
    have hb' :
        Function.Injective (fun i => k⁻¹ (b i)) :=
      k⁻¹.injective.comp hb
    obtain ⟨q, hq⟩ :=
      h5 (fun i => k⁻¹ (a i))
        (fun i => k⁻¹ (b i)) ha' hb'
    let q' : Equiv.Perm X :=
      MulAut.conj k (q : Equiv.Perm X)
    have hq'Q : q' ∈ Q :=
      Subgroup.mem_map_of_mem
        (MulAut.conj k).toMonoidHom q.prop
    refine ⟨⟨q', hq'Q⟩, ?_⟩
    intro i
    have hqi :
        (q : Equiv.Perm X) (k⁻¹ (a i)) =
          k⁻¹ (b i) := by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using
        hq i
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def, q',
      MulAut.conj_apply] using congrArg k hqi
  have hAltQ : alternatingGroup X ≤ Q :=
    hforce Q h5Q hc
  intro σ hσ
  let σ' : Equiv.Perm X :=
    MulAut.conj k σ
  have hσ' : σ' ∈ alternatingGroup X := by
    rw [Equiv.Perm.mem_alternatingGroup] at hσ ⊢
    simp only [σ', MulAut.conj_apply,
      Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, hσ,
      mul_one]
    exact Int.units_mul_self _
  have hmapped : σ' ∈ Q := hAltQ hσ'
  rw [Subgroup.mem_map] at hmapped
  obtain ⟨τ, hτ, hτσ⟩ := hmapped
  have hτeq : τ = σ :=
    (MulAut.conj k).injective (by
      simpa [σ'] using hτσ)
  rwa [← hτeq]

private def comparisonTripleSwap
    {X : Type} [DecidableEq X]
    (e : Fin 8 ↪ X) (x y : X) :
    Perm X :=
  List.formPerm [e 0, e 1] *
    List.formPerm [e 2, e 3] *
    List.formPerm [x, y]

private def comparisonDoubleThreeCycle
    {X : Type} [DecidableEq X]
    (e : Fin 8 ↪ X) (x y : X) :
    Perm X :=
  List.formPerm [e 0, e 1, e 2] *
    List.formPerm [e 3, x, y]

private theorem tripleSwap_difference_small
    {X : Type} [Fintype X] [DecidableEq X]
    (e : Fin 8 ↪ X) (x y : X)
    (hx : ∀ i : Fin 5, x ≠ e (targetTuple8 i))
    (hy : ∀ i : Fin 5, y ≠ e (targetTuple8 i))
    (hxy : x ≠ y) :
    let w :=
      tripleSwap e * (comparisonTripleSwap e x y)⁻¹
    w ≠ 1 ∧ w.support.card ≤ 5 := by
  classical
  let a : Perm X := List.formPerm [e 0, e 1]
  let b : Perm X := List.formPerm [e 2, e 3]
  let c : Perm X := List.formPerm [e 4, e 5]
  let d : Perm X := List.formPerm [x, y]
  let u : Perm X := a * b
  have hx0 : x ≠ e 0 := by simpa [targetTuple8] using hx 0
  have hx1 : x ≠ e 1 := by simpa [targetTuple8] using hx 1
  have hx2 : x ≠ e 2 := by simpa [targetTuple8] using hx 2
  have hx3 : x ≠ e 3 := by simpa [targetTuple8] using hx 3
  have hx4 : x ≠ e 4 := by simpa [targetTuple8] using hx 4
  have hy0 : y ≠ e 0 := by simpa [targetTuple8] using hy 0
  have hy1 : y ≠ e 1 := by simpa [targetTuple8] using hy 1
  have hy2 : y ≠ e 2 := by simpa [targetTuple8] using hy 2
  have hy3 : y ≠ e 3 := by simpa [targetTuple8] using hy 3
  have hy4 : y ≠ e 4 := by simpa [targetTuple8] using hy 4
  have hab : Equiv.Perm.Disjoint a b := by
    apply
      (List.formPerm_disjoint_iff
        (by simp [e.injective.eq_iff])
        (by simp [e.injective.eq_iff])
        (by norm_num) (by norm_num)).2
    simp [List.Disjoint, e.injective.eq_iff]
  have hac : Equiv.Perm.Disjoint a c := by
    apply
      (List.formPerm_disjoint_iff
        (by simp [e.injective.eq_iff])
        (by simp [e.injective.eq_iff])
        (by norm_num) (by norm_num)).2
    simp [List.Disjoint, e.injective.eq_iff]
  have hbc : Equiv.Perm.Disjoint b c := by
    apply
      (List.formPerm_disjoint_iff
        (by simp [e.injective.eq_iff])
        (by simp [e.injective.eq_iff])
        (by norm_num) (by norm_num)).2
    simp [List.Disjoint, e.injective.eq_iff]
  have had : Equiv.Perm.Disjoint a d := by
    apply
      (List.formPerm_disjoint_iff
        (by simp [e.injective.eq_iff])
        (by simp [hxy])
        (by norm_num) (by norm_num)).2
    simp [List.Disjoint, hx0.symm, hx1.symm,
      hy0.symm, hy1.symm]
  have hbd : Equiv.Perm.Disjoint b d := by
    apply
      (List.formPerm_disjoint_iff
        (by simp [e.injective.eq_iff])
        (by simp [hxy])
        (by norm_num) (by norm_num)).2
    simp [List.Disjoint, hx2.symm, hx3.symm,
      hy2.symm, hy3.symm]
  have huc : Commute u c :=
    (hac.mul_left hbc).commute
  have hud : Commute u d :=
    (had.mul_left hbd).commute
  have hwEq :
      tripleSwap e *
          (comparisonTripleSwap e x y)⁻¹ =
        c * d⁻¹ := by
    change u * c * (u * d)⁻¹ = c * d⁻¹
    rw [mul_inv_rev]
    calc
      u * c * (d⁻¹ * u⁻¹) =
          u * (c * d⁻¹) * u⁻¹ := by group
      _ = (c * d⁻¹) * u * u⁻¹ := by
        rw [(huc.mul_right hud.inv_right).eq]
      _ = c * d⁻¹ := by simp
  have hcCard : c.support.card = 2 := by
    dsimp only [c]
    rw [List.formPerm_pair,
      Equiv.Perm.card_support_swap
        (e.injective.ne (by decide))]
  have hdCard : d.support.card = 2 := by
    dsimp only [d]
    rw [List.formPerm_pair,
      Equiv.Perm.card_support_swap hxy]
  constructor
  · intro hwOne
    have hcdOne : c * d⁻¹ = 1 := by
      rw [← hwEq, hwOne]
    have hcd : c = d := by
      calc
        c = (c * d⁻¹) * d := by simp
        _ = d := by rw [hcdOne, one_mul]
    have he4c : e 4 ∈ c.support := by
      simp [c, e.injective.eq_iff]
    have he4d : e 4 ∉ d.support := by
      simp [d, Equiv.swap_apply_def,
        hx4.symm, hy4.symm]
    rw [hcd] at he4c
    exact he4d he4c
  · rw [hwEq]
    calc
      (c * d⁻¹).support.card ≤
          (c.support ∪ d⁻¹.support).card :=
        Finset.card_le_card
          (Equiv.Perm.support_mul_le c d⁻¹)
      _ ≤ c.support.card + d⁻¹.support.card :=
        Finset.card_union_le _ _
      _ = 4 := by
        rw [hcCard, Equiv.Perm.support_inv, hdCard]
      _ ≤ 5 := by norm_num

private theorem doubleThreeCycle_difference_small
    {X : Type} [Fintype X] [DecidableEq X]
    (e : Fin 8 ↪ X) (x y : X)
    (hx : ∀ i : Fin 5, x ≠ e (targetTuple8 i))
    (hy : ∀ i : Fin 5, y ≠ e (targetTuple8 i))
    (hxy : x ≠ y) :
    let w :=
      doubleThreeCycle e *
        (comparisonDoubleThreeCycle e x y)⁻¹
    w ≠ 1 ∧ w.support.card ≤ 5 := by
  classical
  let u : Perm X := List.formPerm [e 0, e 1, e 2]
  let c : Perm X := List.formPerm [e 3, e 4, e 5]
  let d : Perm X := List.formPerm [e 3, x, y]
  have hx0 : x ≠ e 0 := by simpa [targetTuple8] using hx 0
  have hx1 : x ≠ e 1 := by simpa [targetTuple8] using hx 1
  have hx2 : x ≠ e 2 := by simpa [targetTuple8] using hx 2
  have hx3 : x ≠ e 3 := by simpa [targetTuple8] using hx 3
  have hx4 : x ≠ e 4 := by simpa [targetTuple8] using hx 4
  have hy0 : y ≠ e 0 := by simpa [targetTuple8] using hy 0
  have hy1 : y ≠ e 1 := by simpa [targetTuple8] using hy 1
  have hy2 : y ≠ e 2 := by simpa [targetTuple8] using hy 2
  have hy3 : y ≠ e 3 := by simpa [targetTuple8] using hy 3
  have hy4 : y ≠ e 4 := by simpa [targetTuple8] using hy 4
  have huc : Commute u c := by
    exact
      ((List.formPerm_disjoint_iff
        (by simp [e.injective.eq_iff])
        (by simp [e.injective.eq_iff])
        (by norm_num) (by norm_num)).2 (by
          simp [List.Disjoint, e.injective.eq_iff])).commute
  have hud : Commute u d := by
    exact
      ((List.formPerm_disjoint_iff
        (by simp [e.injective.eq_iff])
        (by simp [hxy, hx3.symm, hy3.symm])
        (by norm_num) (by norm_num)).2 (by
          simp [List.Disjoint, hx0.symm, hx1.symm,
            hx2.symm, hy0.symm, hy1.symm,
            hy2.symm, e.injective.eq_iff])).commute
  have hwEq :
      doubleThreeCycle e *
          (comparisonDoubleThreeCycle e x y)⁻¹ =
        c * d⁻¹ := by
    change u * c * (u * d)⁻¹ = c * d⁻¹
    rw [mul_inv_rev]
    calc
      u * c * (d⁻¹ * u⁻¹) =
          u * (c * d⁻¹) * u⁻¹ := by group
      _ = (c * d⁻¹) * u * u⁻¹ := by
        rw [(huc.mul_right hud.inv_right).eq]
      _ = c * d⁻¹ := by simp
  have hcSupport :
      c.support ≤ [e 3, e 4, e 5].toFinset := by
    exact List.support_formPerm_le _
  have hdSupport :
      d.support ≤ [e 3, x, y].toFinset := by
    exact List.support_formPerm_le _
  constructor
  · intro hwOne
    have hcdOne : c * d⁻¹ = 1 := by
      rw [← hwEq, hwOne]
    have hcd : c = d := by
      calc
        c = (c * d⁻¹) * d := by simp
        _ = d := by rw [hcdOne, one_mul]
    have he4c : e 4 ∈ c.support := by
      dsimp only [c]
      rw [List.support_formPerm_of_nodup
        [e 3, e 4, e 5]
        (by simp [e.injective.eq_iff]) (by simp)]
      simp
    have he4d : e 4 ∉ d.support := by
      intro hmem
      have hlist := hdSupport hmem
      simp [hx4.symm, hy4.symm,
        e.injective.eq_iff] at hlist
    rw [hcd] at he4c
    exact he4d he4c
  · rw [hwEq]
    have hsupport :
        (c * d⁻¹).support ≤
          [e 3, e 4, e 5, x, y].toFinset := by
      intro z hz
      have hz' :=
        Equiv.Perm.support_mul_le c d⁻¹ hz
      rw [Equiv.Perm.support_inv] at hz'
      rcases Finset.mem_union.mp hz' with hzC | hzD
      · have := hcSupport hzC
        simp only [List.mem_toFinset, List.mem_cons] at this ⊢
        tauto
      · have := hdSupport hzD
        simp only [List.mem_toFinset, List.mem_cons] at this ⊢
        tauto
    calc
      (c * d⁻¹).support.card ≤
          [e 3, e 4, e 5, x, y].toFinset.card :=
        Finset.card_le_card hsupport
      _ ≤ [e 3, e 4, e 5, x, y].length :=
        List.toFinset_card_le _
      _ = 5 := by norm_num

private theorem alternatingGroup_le_of_tripleSwap_mem
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : 8 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (e : Fin 8 ↪ X)
    (hc : tripleSwap e ∈ P) :
    alternatingGroup X ≤ P := by
  classical
  let a : Fin 5 → X := fun i => e (sourceTuple8 i)
  let b : Fin 5 → X := fun i => e (targetTuple8 i)
  have ha : Function.Injective a :=
    e.injective.comp sourceTuple8_injective
  have hb : Function.Injective b :=
    e.injective.comp targetTuple8_injective
  obtain ⟨q, hq⟩ := h5 a b ha hb
  have hq0 : (q : Equiv.Perm X) (e 0) = e 0 := by
    simpa [a, b, sourceTuple8, targetTuple8,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hq 0
  have hq1 : (q : Equiv.Perm X) (e 1) = e 1 := by
    simpa [a, b, sourceTuple8, targetTuple8,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hq 1
  have hq2 : (q : Equiv.Perm X) (e 2) = e 2 := by
    simpa [a, b, sourceTuple8, targetTuple8,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hq 2
  have hq3 : (q : Equiv.Perm X) (e 3) = e 3 := by
    simpa [a, b, sourceTuple8, targetTuple8,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hq 3
  have hq7 : (q : Equiv.Perm X) (e 7) = e 4 := by
    simpa [a, b, sourceTuple8, targetTuple8,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hq 4
  let x : X := (q : Equiv.Perm X) (e 4)
  let y : X := (q : Equiv.Perm X) (e 5)
  have hx :
      ∀ i : Fin 5, x ≠ e (targetTuple8 i) := by
    intro i
    have hqi :
        (q : Equiv.Perm X) (e (sourceTuple8 i)) =
          e (targetTuple8 i) := by
      simpa [a, b, Subgroup.smul_def,
        Equiv.Perm.smul_def] using hq i
    rw [← hqi]
    exact
      (q : Equiv.Perm X).injective.ne
        (e.injective.ne (four_ne_sourceTuple8 i))
  have hy :
      ∀ i : Fin 5, y ≠ e (targetTuple8 i) := by
    intro i
    have hqi :
        (q : Equiv.Perm X) (e (sourceTuple8 i)) =
          e (targetTuple8 i) := by
      simpa [a, b, Subgroup.smul_def,
        Equiv.Perm.smul_def] using hq i
    rw [← hqi]
    exact
      (q : Equiv.Perm X).injective.ne
        (e.injective.ne (five_ne_sourceTuple8 i))
  have hxy : x ≠ y :=
    (q : Equiv.Perm X).injective.ne
      (e.injective.ne (by decide))
  let h : Equiv.Perm X :=
    (q : Equiv.Perm X) * tripleSwap e *
      (q : Equiv.Perm X)⁻¹
  have hh : h = comparisonTripleSwap e x y := by
    change
      (q : Equiv.Perm X) * tripleSwap e *
          (q : Equiv.Perm X)⁻¹ =
        comparisonTripleSwap e x y
    rw [← Equiv.permCongr_eq_mul, tripleSwap,
      Equiv.permCongr_mul, Equiv.permCongr_mul,
      Helpers.permCongr_formPerm,
      Helpers.permCongr_formPerm,
      Helpers.permCongr_formPerm]
    simp [comparisonTripleSwap, x, y,
      hq0, hq1, hq2, hq3]
  let w :=
    tripleSwap e *
      (comparisonTripleSwap e x y)⁻¹
  obtain ⟨hwNe, hwsupport⟩ :=
    tripleSwap_difference_small e x y hx hy hxy
  have hwP : w ∈ P := by
    apply P.mul_mem hc
    apply P.inv_mem
    rw [← hh]
    exact
      P.mul_mem (P.mul_mem q.prop hc)
        (P.inv_mem q.prop)
  exact
    Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
      X P h5 (by omega) hwP hwNe hwsupport

private theorem alternatingGroup_le_of_doubleThreeCycle_mem
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : 8 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (e : Fin 8 ↪ X)
    (hc : doubleThreeCycle e ∈ P) :
    alternatingGroup X ≤ P := by
  classical
  let a : Fin 5 → X := fun i => e (sourceTuple8 i)
  let b : Fin 5 → X := fun i => e (targetTuple8 i)
  have ha : Function.Injective a :=
    e.injective.comp sourceTuple8_injective
  have hb : Function.Injective b :=
    e.injective.comp targetTuple8_injective
  obtain ⟨q, hq⟩ := h5 a b ha hb
  have hq0 : (q : Equiv.Perm X) (e 0) = e 0 := by
    simpa [a, b, sourceTuple8, targetTuple8,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hq 0
  have hq1 : (q : Equiv.Perm X) (e 1) = e 1 := by
    simpa [a, b, sourceTuple8, targetTuple8,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hq 1
  have hq2 : (q : Equiv.Perm X) (e 2) = e 2 := by
    simpa [a, b, sourceTuple8, targetTuple8,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hq 2
  have hq3 : (q : Equiv.Perm X) (e 3) = e 3 := by
    simpa [a, b, sourceTuple8, targetTuple8,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hq 3
  have hq7 : (q : Equiv.Perm X) (e 7) = e 4 := by
    simpa [a, b, sourceTuple8, targetTuple8,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hq 4
  let x : X := (q : Equiv.Perm X) (e 4)
  let y : X := (q : Equiv.Perm X) (e 5)
  have hx :
      ∀ i : Fin 5, x ≠ e (targetTuple8 i) := by
    intro i
    have hqi :
        (q : Equiv.Perm X) (e (sourceTuple8 i)) =
          e (targetTuple8 i) := by
      simpa [a, b, Subgroup.smul_def,
        Equiv.Perm.smul_def] using hq i
    rw [← hqi]
    exact
      (q : Equiv.Perm X).injective.ne
        (e.injective.ne (four_ne_sourceTuple8 i))
  have hy :
      ∀ i : Fin 5, y ≠ e (targetTuple8 i) := by
    intro i
    have hqi :
        (q : Equiv.Perm X) (e (sourceTuple8 i)) =
          e (targetTuple8 i) := by
      simpa [a, b, Subgroup.smul_def,
        Equiv.Perm.smul_def] using hq i
    rw [← hqi]
    exact
      (q : Equiv.Perm X).injective.ne
        (e.injective.ne (five_ne_sourceTuple8 i))
  have hxy : x ≠ y :=
    (q : Equiv.Perm X).injective.ne
      (e.injective.ne (by decide))
  let h : Equiv.Perm X :=
    (q : Equiv.Perm X) * doubleThreeCycle e *
      (q : Equiv.Perm X)⁻¹
  have hh :
      h = comparisonDoubleThreeCycle e x y := by
    change
      (q : Equiv.Perm X) * doubleThreeCycle e *
          (q : Equiv.Perm X)⁻¹ =
        comparisonDoubleThreeCycle e x y
    rw [← Equiv.permCongr_eq_mul,
      doubleThreeCycle, Equiv.permCongr_mul,
      Helpers.permCongr_formPerm,
      Helpers.permCongr_formPerm]
    simp [comparisonDoubleThreeCycle, x, y,
      hq0, hq1, hq2, hq3]
  let w :=
    doubleThreeCycle e *
      (comparisonDoubleThreeCycle e x y)⁻¹
  obtain ⟨hwNe, hwsupport⟩ :=
    doubleThreeCycle_difference_small e x y hx hy hxy
  have hwP : w ∈ P := by
    apply P.mul_mem hc
    apply P.inv_mem
    rw [← hh]
    exact
      P.mul_mem (P.mul_mem q.prop hc)
        (P.inv_mem q.prop)
  exact
    Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
      X P h5 (by omega) hwP hwNe hwsupport

private theorem alternatingGroup_le_of_prime_order_support_six
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : 8 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    {g : Equiv.Perm X} (hg : g ∈ P)
    {p : ℕ} (hp : p.Prime) (hgorder : orderOf g = p)
    (hgsupport : g.support.card = 6) :
    alternatingGroup X ≤ P := by
  classical
  have heNonempty : Nonempty (Fin 8 ↪ X) := by
    rw [Function.Embedding.nonempty_iff_card_le,
      Fintype.card_fin]
    exact hcard
  let e : Fin 8 ↪ X := Classical.choice heNonempty
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    exact hp
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder, hgsupport] at hsum
  have hple : p ≤ 6 := by
    nlinarith [Nat.zero_le m]
  interval_cases p
  all_goals norm_num at hp
  · have hm' : m + 1 = 3 := by omega
    have hcycle :
        g.cycleType = (tripleSwap e).cycleType := by
      rw [hm, hgorder, hm', tripleSwap_cycleType]
      norm_num
    apply alternatingGroup_le_of_cycleType_eq
      P h5 hg (tripleSwap e) hcycle
    intro Q h5Q hcQ
    exact
      alternatingGroup_le_of_tripleSwap_mem
        Q hcard h5Q e hcQ
  · have hm' : m + 1 = 2 := by omega
    have hcycle :
        g.cycleType =
          (doubleThreeCycle e).cycleType := by
      rw [hm, hgorder, hm',
        doubleThreeCycle_cycleType]
      norm_num
    apply alternatingGroup_le_of_cycleType_eq
      P h5 hg (doubleThreeCycle e) hcycle
    intro Q h5Q hcQ
    exact
      alternatingGroup_le_of_doubleThreeCycle_mem
        Q hcard h5Q e hcQ
  · omega

theorem alternatingGroup_le_of_nontrivial_support_le_six
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : 8 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    {g : Equiv.Perm X} (hg : g ∈ P)
    (hgNe : g ≠ 1) (hgsupport : g.support.card ≤ 6) :
    alternatingGroup X ≤ P := by
  classical
  let Z : Subgroup (Equiv.Perm X) :=
    Subgroup.zpowers g
  have hZnontrivial : Nontrivial Z :=
    Z.nontrivial_iff_ne_bot.mpr
      (Subgroup.zpowers_ne_bot.mpr hgNe)
  have hZcard : 1 < Nat.card Z :=
    Finite.one_lt_card_iff_nontrivial.mpr hZnontrivial
  obtain ⟨p, hp, hpdiv⟩ :=
    Nat.exists_prime_and_dvd (n := Nat.card Z) (by omega)
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨v, hvorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := Z) p hpdiv
  obtain ⟨z, hz⟩ :=
    Subgroup.mem_zpowers_iff.mp v.prop
  let w : Equiv.Perm X := v
  have hwP : w ∈ P := by
    change (v : Equiv.Perm X) ∈ P
    rw [← hz]
    exact P.zpow_mem hg z
  have hworder : orderOf w = p := by
    calc
      orderOf w = orderOf v := Subgroup.orderOf_coe _
      _ = p := hvorder
  have hwNe : w ≠ 1 := by
    intro hw
    rw [hw, orderOf_one] at hworder
    exact hp.ne_one hworder.symm
  have hwsupport : w.support.card ≤ 6 := by
    calc
      w.support.card ≤ g.support.card := by
        change (v : Equiv.Perm X).support.card ≤
          g.support.card
        rw [← hz]
        exact Finset.card_le_card
          (Equiv.Perm.support_zpow_le g z)
      _ ≤ 6 := hgsupport
  by_cases hsmall : w.support.card ≤ 5
  · exact
      Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
        X P h5 (by omega) hwP hwNe hsmall
  · exact
      alternatingGroup_le_of_prime_order_support_six
        P hcard h5 hwP hp hworder (by omega)

end FiveTransitive.SmallSupportGeneric

end CFSG
