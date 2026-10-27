module

public import Mathlib.GroupTheory.Perm.Cycle.Concrete
import CFSG.Permutation.FiveTransitive.Helpers
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG

namespace FiveTransitive.Degree16FiniteChecks

open Equiv

@[expose] def sevenCycle : Perm (Fin 16) :=
  List.formPerm [0, 1, 2, 3, 4, 5, 6]

theorem sevenCycle_isCycle : sevenCycle.IsCycle := by
  apply List.isCycle_formPerm
  · decide
  · norm_num

theorem sevenCycle_card_support : sevenCycle.support.card = 7 := by
  decide

@[expose] def sourceTuple : Fin 5 → Fin 16 :=
  ![0, 1, 2, 3, 7]

@[expose] def targetTuple : Fin 5 → Fin 16 :=
  ![0, 1, 2, 3, 4]

theorem sourceTuple_injective : Function.Injective sourceTuple := by
  decide

theorem targetTuple_injective : Function.Injective targetTuple := by
  decide

theorem five_le_of_ne_zero_one_two_three_four (x : Fin 16)
    (h0 : x ≠ 0) (h1 : x ≠ 1) (h2 : x ≠ 2) (h3 : x ≠ 3) (h4 : x ≠ 4) :
    5 ≤ x.val := by
  omega

@[expose] def comparisonCycle (x y z : Fin 16) : Perm (Fin 16) :=
  List.formPerm [0, 1, 2, 3, x, y, z]

private def candidateWords (x y z : Fin 16) : List (Perm (Fin 16)) :=
  let g := sevenCycle
  let h := comparisonCycle x y z
  [g * h⁻¹, g ^ 2 * h⁻¹ ^ 2, g * h * g⁻¹ * h⁻¹, (g * h⁻¹) ^ 2]

private def HasSmallCandidate (x y z : Fin 16) : Prop :=
  ∃ w ∈ candidateWords x y z, w ≠ 1 ∧ w.support.card ≤ 5

private theorem smallCandidate_5_6_7 : HasSmallCandidate 5 6 7 := by
  refine ⟨sevenCycle * (comparisonCycle 5 6 7)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords]

private theorem smallCandidate_5_7_6 : HasSmallCandidate 5 7 6 := by
  refine ⟨sevenCycle * (comparisonCycle 5 7 6)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords]

private theorem smallCandidate_5_7_8 : HasSmallCandidate 5 7 8 := by
  refine ⟨(sevenCycle * (comparisonCycle 5 7 8)⁻¹) ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords]

private theorem smallCandidate_6_5_7 : HasSmallCandidate 6 5 7 := by
  refine ⟨sevenCycle ^ 2 * (comparisonCycle 6 5 7)⁻¹ ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords]

private theorem smallCandidate_6_7_5 : HasSmallCandidate 6 7 5 := by
  refine ⟨sevenCycle * (comparisonCycle 6 7 5)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords]

private theorem smallCandidate_6_7_8 : HasSmallCandidate 6 7 8 := by
  refine ⟨sevenCycle * comparisonCycle 6 7 8 * sevenCycle⁻¹ *
    (comparisonCycle 6 7 8)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords]

private theorem smallCandidate_7_5_6 : HasSmallCandidate 7 5 6 := by
  refine ⟨sevenCycle * (comparisonCycle 7 5 6)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords]

private theorem smallCandidate_7_5_8 : HasSmallCandidate 7 5 8 := by
  refine ⟨sevenCycle ^ 2 * (comparisonCycle 7 5 8)⁻¹ ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords]

private theorem smallCandidate_7_6_5 : HasSmallCandidate 7 6 5 := by
  refine ⟨sevenCycle * (comparisonCycle 7 6 5)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords]

private theorem smallCandidate_7_6_8 : HasSmallCandidate 7 6 8 := by
  refine ⟨(sevenCycle * (comparisonCycle 7 6 8)⁻¹) ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords]

private theorem smallCandidate_7_8_5 : HasSmallCandidate 7 8 5 := by
  refine ⟨(sevenCycle * (comparisonCycle 7 8 5)⁻¹) ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords]

private theorem smallCandidate_7_8_6 : HasSmallCandidate 7 8 6 := by
  refine ⟨sevenCycle * comparisonCycle 7 8 6 * sevenCycle⁻¹ *
    (comparisonCycle 7 8 6)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords]

private theorem smallCandidate_7_8_9 : HasSmallCandidate 7 8 9 := by
  refine ⟨sevenCycle * comparisonCycle 7 8 9 * sevenCycle⁻¹ *
    (comparisonCycle 7 8 9)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords]

private theorem candidates_mem_closure (x y z : Fin 16) :
    ∀ w ∈ candidateWords x y z,
      w ∈ Subgroup.closure
        ({sevenCycle, comparisonCycle x y z} : Set (Perm (Fin 16))) := by
  let K := Subgroup.closure
    ({sevenCycle, comparisonCycle x y z} : Set (Perm (Fin 16)))
  have hg : sevenCycle ∈ K :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hh : comparisonCycle x y z ∈ K :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  intro w hw
  simp only [candidateWords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact K.mul_mem hg (K.inv_mem hh)
  · exact K.mul_mem (K.pow_mem hg 2) (K.pow_mem (K.inv_mem hh) 2)
  · exact K.mul_mem (K.mul_mem (K.mul_mem hg hh) (K.inv_mem hg)) (K.inv_mem hh)
  · exact K.pow_mem (K.mul_mem hg (K.inv_mem hh)) 2

private def triple (x y z : Fin 16) : Fin 3 → Fin 16 :=
  ![x, y, z]

private def basePoint (i : Fin 7) : Fin 16 :=
  ⟨i.val, i.isLt.trans (by norm_num)⟩

private def baseAndExternal (x y z : Fin 16) :
    Sum (Fin 7) {i : Fin 3 // 7 ≤ (triple x y z i).val} → Fin 16
  | Sum.inl i => basePoint i
  | Sum.inr i => triple x y z i

private theorem baseAndExternal_injective
    (x y z : Fin 16) (hxyz : Function.Injective (triple x y z)) :
    Function.Injective (baseAndExternal x y z) := by
  intro a b hab
  rcases a with a | a <;> rcases b with b | b
  · apply congrArg Sum.inl
    apply Fin.ext
    simpa [baseAndExternal, basePoint] using congrArg Fin.val hab
  · have ha : (basePoint a).val < 7 := a.isLt
    have hb : 7 ≤ (triple x y z b).val := b.property
    simp only [baseAndExternal] at hab
    omega
  · have ha : 7 ≤ (triple x y z a).val := a.property
    have hb : (basePoint b).val < 7 := b.isLt
    simp only [baseAndExternal] at hab
    omega
  · apply congrArg Sum.inr
    apply Subtype.ext
    apply hxyz
    simpa [baseAndExternal] using hab

private theorem exists_relabel
    (x y z x' y' z' : Fin 16)
    (hsource : Function.Injective (triple x y z))
    (htarget : Function.Injective (triple x' y' z'))
    (hext : ∀ i, 7 ≤ (triple x y z i).val →
      7 ≤ (triple x' y' z' i).val)
    (hint : ∀ i, (triple x y z i).val < 7 →
      triple x' y' z' i = triple x y z i) :
    ∃ e : Perm (Fin 16),
      (∀ i : Fin 7, e (basePoint i) = basePoint i) ∧
      ∀ i : Fin 3, e (triple x y z i) = triple x' y' z' i := by
  let I := Sum (Fin 7) {i : Fin 3 // 7 ≤ (triple x y z i).val}
  let f : I → Fin 16 := baseAndExternal x y z
  let k : I → Fin 16
    | Sum.inl i => basePoint i
    | Sum.inr i => triple x' y' z' i
  have hf : Function.Injective f :=
    baseAndExternal_injective x y z hsource
  have hk : Function.Injective k := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · apply congrArg Sum.inl
      apply Fin.ext
      simpa [k, basePoint] using congrArg Fin.val hab
    · have ha : (basePoint a).val < 7 := a.isLt
      have hb : 7 ≤ (triple x' y' z' b).val := hext b b.property
      simp only [k] at hab
      omega
    · have ha : 7 ≤ (triple x' y' z' a).val := hext a a.property
      have hb : (basePoint b).val < 7 := b.isLt
      simp only [k] at hab
      omega
    · apply congrArg Sum.inr
      apply Subtype.ext
      apply htarget
      simpa [k] using hab
  obtain ⟨e, he⟩ := Perm.exists_extending_pair f k hf hk
  refine ⟨e, ?_, ?_⟩
  · intro i
    exact he (Sum.inl i)
  · intro i
    by_cases hi : 7 ≤ (triple x y z i).val
    · exact he (Sum.inr ⟨i, hi⟩)
    · have hilow : (triple x y z i).val < 7 := by omega
      let j : Fin 7 := ⟨(triple x y z i).val, hilow⟩
      calc
        e (triple x y z i) = e (basePoint j) := by
          congr
        _ = basePoint j := he (Sum.inl j)
        _ = triple x y z i := by
          rfl
        _ = triple x' y' z' i := (hint i hilow).symm

private theorem card_support_permCongr (e : Perm (Fin 16)) (w : Perm (Fin 16)) :
    (e.permCongr w).support.card = w.support.card := by
  have hsupport :
      (e.permCongr w).support = w.support.map e.toEmbedding := by
    ext a
    simp [Perm.mem_support]
  rw [hsupport, Finset.card_map]

private theorem smallCandidate_of_relabel
    (x y z x' y' z' : Fin 16)
    (he : ∃ e : Perm (Fin 16),
      (∀ i : Fin 7, e (basePoint i) = basePoint i) ∧
      ∀ i : Fin 3, e (triple x y z i) = triple x' y' z' i)
    (hsmall : HasSmallCandidate x' y' z') :
    HasSmallCandidate x y z := by
  obtain ⟨e, hbase, htriple⟩ := he
  have hseven : e.permCongr sevenCycle = sevenCycle := by
    have h0 := hbase (0 : Fin 7)
    have h1 := hbase (1 : Fin 7)
    have h2 := hbase (2 : Fin 7)
    have h3 := hbase (3 : Fin 7)
    have h4 := hbase (4 : Fin 7)
    have h5 := hbase (5 : Fin 7)
    have h6 := hbase (6 : Fin 7)
    rw [sevenCycle, FiveTransitive.Helpers.permCongr_formPerm]
    simp_all [basePoint]
  have hcomparison :
      e.permCongr (comparisonCycle x y z) = comparisonCycle x' y' z' := by
    rw [comparisonCycle, comparisonCycle,
      FiveTransitive.Helpers.permCongr_formPerm]
    have h0 := hbase (0 : Fin 7)
    have h1 := hbase (1 : Fin 7)
    have h2 := hbase (2 : Fin 7)
    have h3 := hbase (3 : Fin 7)
    have hx := htriple (0 : Fin 3)
    have hy := htriple (1 : Fin 3)
    have hz := htriple (2 : Fin 3)
    simpa [basePoint, triple] using congrArg List.formPerm
      (show ([e 0, e 1, e 2, e 3, e x, e y, e z] : List (Fin 16)) =
          [0, 1, 2, 3, x', y', z'] by
        simp_all [basePoint, triple])
  obtain ⟨w, hw, hwne, hwcard⟩ := hsmall
  let F : Perm (Fin 16) ≃* Perm (Fin 16) := e.symm.permCongrHom
  have hseven' : F sevenCycle = sevenCycle := by
    calc
      F sevenCycle = F (e.permCongr sevenCycle) := congrArg F hseven.symm
      _ = sevenCycle := e.permCongrHom.symm_apply_apply sevenCycle
  have hcomparison' :
      F (comparisonCycle x' y' z') = comparisonCycle x y z := by
    calc
      F (comparisonCycle x' y' z') =
          F (e.permCongr (comparisonCycle x y z)) :=
        congrArg F hcomparison.symm
      _ = comparisonCycle x y z :=
        e.permCongrHom.symm_apply_apply (comparisonCycle x y z)
  refine ⟨F w, ?_, ?_, ?_⟩
  · simp only [candidateWords, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with rfl | rfl | rfl | rfl
    · left
      simp only [map_mul, map_inv, hseven', hcomparison']
    · right
      left
      simp only [map_mul, map_pow, map_inv, hseven', hcomparison']
    · right
      right
      left
      simp only [map_mul, map_inv, hseven', hcomparison']
    · right
      right
      right
      simp only [map_pow, map_mul, map_inv, hseven', hcomparison']
  · intro hwone
    apply hwne
    apply F.injective
    simpa only [map_one] using hwone
  · change (e.symm.permCongr w).support.card ≤ 5
    rwa [card_support_permCongr]

private theorem triple_injective
    (x y z : Fin 16) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective (triple x y z) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [triple, eq_comm]

private theorem exists_small_candidate
    (x y z : Fin 16)
    (hx : 5 ≤ x.val) (hy : 5 ≤ y.val) (hz : 5 ≤ z.val)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    HasSmallCandidate x y z := by
  have hsource := triple_injective x y z hxy hxz hyz
  by_cases hx5 : x = 5
  · subst x
    by_cases hy6 : y = 6
    · subst y
      apply smallCandidate_of_relabel 5 6 z 5 6 7
        (exists_relabel 5 6 z 5 6 7 hsource (by decide) (by
          intro i hi
          fin_cases i <;> simp_all [triple]) (by
          intro i hi
          fin_cases i <;> simp_all [triple]
          all_goals omega))
        smallCandidate_5_6_7
    · by_cases hz6 : z = 6
      · subst z
        apply smallCandidate_of_relabel 5 y 6 5 7 6
          (exists_relabel 5 y 6 5 7 6 hsource (by decide) (by
            intro i hi
            fin_cases i <;> simp_all [triple]) (by
            intro i hi
            fin_cases i <;> simp_all [triple]
            all_goals omega))
          smallCandidate_5_7_6
      · apply smallCandidate_of_relabel 5 y z 5 7 8
          (exists_relabel 5 y z 5 7 8 hsource (by decide) (by
            intro i hi
            fin_cases i <;> simp_all [triple]) (by
            intro i hi
            fin_cases i <;> simp_all [triple]
            all_goals omega))
          smallCandidate_5_7_8
  · by_cases hx6 : x = 6
    · subst x
      by_cases hy5 : y = 5
      · subst y
        apply smallCandidate_of_relabel 6 5 z 6 5 7
          (exists_relabel 6 5 z 6 5 7 hsource (by decide) (by
            intro i hi
            fin_cases i <;> simp_all [triple]) (by
            intro i hi
            fin_cases i <;> simp_all [triple]
            all_goals omega))
          smallCandidate_6_5_7
      · by_cases hz5 : z = 5
        · subst z
          apply smallCandidate_of_relabel 6 y 5 6 7 5
            (exists_relabel 6 y 5 6 7 5 hsource (by decide) (by
              intro i hi
              fin_cases i <;> simp_all [triple]) (by
              intro i hi
              fin_cases i <;> simp_all [triple]
              all_goals omega))
            smallCandidate_6_7_5
        · apply smallCandidate_of_relabel 6 y z 6 7 8
            (exists_relabel 6 y z 6 7 8 hsource (by decide) (by
              intro i hi
              fin_cases i <;> simp_all [triple]) (by
              intro i hi
              fin_cases i <;> simp_all [triple]
              all_goals omega))
            smallCandidate_6_7_8
    · by_cases hy5 : y = 5
      · subst y
        by_cases hz6 : z = 6
        · subst z
          apply smallCandidate_of_relabel x 5 6 7 5 6
            (exists_relabel x 5 6 7 5 6 hsource (by decide) (by
              intro i hi
              fin_cases i <;> simp_all [triple]) (by
              intro i hi
              fin_cases i <;> simp_all [triple]
              all_goals omega))
            smallCandidate_7_5_6
        · apply smallCandidate_of_relabel x 5 z 7 5 8
            (exists_relabel x 5 z 7 5 8 hsource (by decide) (by
              intro i hi
              fin_cases i <;> simp_all [triple]) (by
              intro i hi
              fin_cases i <;> simp_all [triple]
              all_goals omega))
            smallCandidate_7_5_8
      · by_cases hy6 : y = 6
        · subst y
          by_cases hz5 : z = 5
          · subst z
            apply smallCandidate_of_relabel x 6 5 7 6 5
              (exists_relabel x 6 5 7 6 5 hsource (by decide) (by
                intro i hi
                fin_cases i <;> simp_all [triple]) (by
                intro i hi
                fin_cases i <;> simp_all [triple]
                all_goals omega))
              smallCandidate_7_6_5
          · apply smallCandidate_of_relabel x 6 z 7 6 8
              (exists_relabel x 6 z 7 6 8 hsource (by decide) (by
                intro i hi
                fin_cases i <;> simp_all [triple]) (by
                intro i hi
                fin_cases i <;> simp_all [triple]
                all_goals omega))
              smallCandidate_7_6_8
        · by_cases hz5 : z = 5
          · subst z
            apply smallCandidate_of_relabel x y 5 7 8 5
              (exists_relabel x y 5 7 8 5 hsource (by decide) (by
                intro i hi
                fin_cases i <;> simp_all [triple]) (by
                intro i hi
                fin_cases i <;> simp_all [triple]
                all_goals omega))
              smallCandidate_7_8_5
          · by_cases hz6 : z = 6
            · subst z
              apply smallCandidate_of_relabel x y 6 7 8 6
                (exists_relabel x y 6 7 8 6 hsource (by decide) (by
                  intro i hi
                  fin_cases i <;> simp_all [triple]) (by
                  intro i hi
                  fin_cases i <;> simp_all [triple]
                  all_goals omega))
                smallCandidate_7_8_6
            · apply smallCandidate_of_relabel x y z 7 8 9
                (exists_relabel x y z 7 8 9 hsource (by decide) (by
                  intro i hi
                  fin_cases i <;> simp_all [triple]) (by
                  intro i hi
                  fin_cases i <;> simp_all [triple]
                  all_goals omega))
                smallCandidate_7_8_9

theorem exists_small_mem_closure
    (x y z : Fin 16)
    (hx : 5 ≤ x.val) (hy : 5 ≤ y.val) (hz : 5 ≤ z.val)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ w ∈ Subgroup.closure
        ({sevenCycle, comparisonCycle x y z} : Set (Perm (Fin 16))),
      w ≠ 1 ∧ w.support.card ≤ 5 := by
  obtain ⟨w, hw, hsmall⟩ :=
    exists_small_candidate x y z hx hy hz hxy hxz hyz
  exact ⟨w, candidates_mem_closure x y z w hw, hsmall⟩

@[expose] def tripleSwap : Perm (Fin 16) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [4, 5]

@[expose] def comparisonTripleSwap (x y : Fin 16) : Perm (Fin 16) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [x, y]

theorem tripleSwap_cycleType :
    tripleSwap.cycleType = {2, 2, 2} := by
  unfold tripleSwap
  rw [Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide)]
  rw [Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide)]
  rw [(List.isCycle_formPerm (by decide : ([0, 1] : List (Fin 16)).Nodup) (by norm_num)).cycleType,
    (List.isCycle_formPerm (by decide : ([2, 3] : List (Fin 16)).Nodup) (by norm_num)).cycleType,
    (List.isCycle_formPerm (by decide : ([4, 5] : List (Fin 16)).Nodup) (by norm_num)).cycleType]
  decide

theorem tripleSwap_difference_small :
    ∀ x y : Fin 16, 5 ≤ x.val → 5 ≤ y.val → x ≠ y →
      let w := tripleSwap * (comparisonTripleSwap x y)⁻¹
      w ≠ 1 ∧ w.support.card ≤ 5 := by
  decide

@[expose] def doubleThreeCycle : Perm (Fin 16) :=
  List.formPerm [0, 1, 2] * List.formPerm [3, 4, 5]

@[expose] def comparisonDoubleThreeCycle (x y : Fin 16) : Perm (Fin 16) :=
  List.formPerm [0, 1, 2] * List.formPerm [3, x, y]

theorem doubleThreeCycle_cycleType :
    doubleThreeCycle.cycleType = {3, 3} := by
  unfold doubleThreeCycle
  rw [Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide)]
  rw [(List.isCycle_formPerm (by decide : ([0, 1, 2] : List (Fin 16)).Nodup) (by norm_num)).cycleType,
    (List.isCycle_formPerm (by decide : ([3, 4, 5] : List (Fin 16)).Nodup) (by norm_num)).cycleType]
  decide

theorem doubleThreeCycle_difference_small :
    ∀ x y : Fin 16, 5 ≤ x.val → 5 ≤ y.val → x ≠ y →
      let w := doubleThreeCycle *
        (comparisonDoubleThreeCycle x y)⁻¹
      w ≠ 1 ∧ w.support.card ≤ 5 := by
  decide

end FiveTransitive.Degree16FiniteChecks

end CFSG
