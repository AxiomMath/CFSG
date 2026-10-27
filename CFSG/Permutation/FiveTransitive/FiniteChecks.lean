module
public import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Cycle.Concrete

public section

namespace CFSG

namespace FiveTransitive.FiniteChecks

open Equiv

private theorem permCongr_formPerm
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (l : List α) :
    e.permCongr (List.formPerm l) = List.formPerm (l.map e) := by
  induction l with
  | nil =>
      exact e.permCongrHom.map_one
  | cons x l ih =>
      cases l with
      | nil =>
          exact e.permCongrHom.map_one
      | cons y l =>
          simp only [List.formPerm_cons_cons, List.map_cons, e.permCongr_mul, ih]
          congr 1
          ext z
          simp only [Equiv.permCongr_apply, Equiv.swap_apply_def]
          split_ifs <;>
            have hz := e.apply_symm_apply z <;>
            simp_all

@[expose] def sevenCycle : Perm (Fin 10) :=
  List.formPerm [0, 1, 2, 3, 4, 5, 6]

theorem sevenCycle_isCycle : sevenCycle.IsCycle := by
  apply List.isCycle_formPerm
  · decide
  · norm_num

theorem sevenCycle_card_support : sevenCycle.support.card = 7 := by
  decide

@[expose] def sourceTuple : Fin 5 → Fin 10 :=
  ![0, 1, 2, 3, 7]

@[expose] def targetTuple : Fin 5 → Fin 10 :=
  ![0, 1, 2, 3, 4]

theorem sourceTuple_injective : Function.Injective sourceTuple := by
  decide

theorem targetTuple_injective : Function.Injective targetTuple := by
  decide

theorem five_le_of_ne_zero_one_two_three_four (x : Fin 10)
    (h0 : x ≠ 0) (h1 : x ≠ 1) (h2 : x ≠ 2) (h3 : x ≠ 3) (h4 : x ≠ 4) :
    5 ≤ x.val := by
  omega

@[expose] def comparisonCycle (x y z : Fin 10) : Perm (Fin 10) :=
  List.formPerm [0, 1, 2, 3, x, y, z]

private def candidateWords (x y z : Fin 10) : List (Perm (Fin 10)) :=
  let g := sevenCycle
  let h := comparisonCycle x y z
  [g * h⁻¹, g ^ 2 * h⁻¹ ^ 2, g * h * g⁻¹ * h⁻¹, (g * h⁻¹) ^ 2]

namespace NormalForm10

private def HasSmallCandidate (x y z : Fin 10) : Prop :=
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

private def triple (x y z : Fin 10) : Fin 3 → Fin 10 :=
  ![x, y, z]

private def basePoint (i : Fin 7) : Fin 10 :=
  ⟨i.val, i.isLt.trans (by norm_num)⟩

private def baseAndExternal (x y z : Fin 10) :
    Sum (Fin 7) {i : Fin 3 // 7 ≤ (triple x y z i).val} → Fin 10
  | Sum.inl i => basePoint i
  | Sum.inr i => triple x y z i

private theorem baseAndExternal_injective
    (x y z : Fin 10) (hxyz : Function.Injective (triple x y z)) :
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
    (x y z x' y' z' : Fin 10)
    (hsource : Function.Injective (triple x y z))
    (htarget : Function.Injective (triple x' y' z'))
    (hext : ∀ i, 7 ≤ (triple x y z i).val →
      7 ≤ (triple x' y' z' i).val)
    (hint : ∀ i, (triple x y z i).val < 7 →
      triple x' y' z' i = triple x y z i) :
    ∃ e : Perm (Fin 10),
      (∀ i : Fin 7, e (basePoint i) = basePoint i) ∧
      ∀ i : Fin 3, e (triple x y z i) = triple x' y' z' i := by
  let I := Sum (Fin 7) {i : Fin 3 // 7 ≤ (triple x y z i).val}
  let f : I → Fin 10 := baseAndExternal x y z
  let k : I → Fin 10
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

private theorem card_support_permCongr (e : Perm (Fin 10)) (w : Perm (Fin 10)) :
    (e.permCongr w).support.card = w.support.card := by
  have hsupport :
      (e.permCongr w).support = w.support.map e.toEmbedding := by
    ext a
    simp [Perm.mem_support]
  rw [hsupport, Finset.card_map]

private theorem smallCandidate_of_relabel
    (x y z x' y' z' : Fin 10)
    (he : ∃ e : Perm (Fin 10),
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
    rw [sevenCycle, permCongr_formPerm]
    simp_all [basePoint]
  have hcomparison :
      e.permCongr (comparisonCycle x y z) = comparisonCycle x' y' z' := by
    rw [comparisonCycle, comparisonCycle,
      permCongr_formPerm]
    have h0 := hbase (0 : Fin 7)
    have h1 := hbase (1 : Fin 7)
    have h2 := hbase (2 : Fin 7)
    have h3 := hbase (3 : Fin 7)
    have hx := htriple (0 : Fin 3)
    have hy := htriple (1 : Fin 3)
    have hz := htriple (2 : Fin 3)
    simpa [basePoint, triple] using congrArg List.formPerm
      (show ([e 0, e 1, e 2, e 3, e x, e y, e z] : List (Fin 10)) =
          [0, 1, 2, 3, x', y', z'] by
        simp_all [basePoint, triple])
  obtain ⟨w, hw, hwne, hwcard⟩ := hsmall
  let F : Perm (Fin 10) ≃* Perm (Fin 10) := e.symm.permCongrHom
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
    (x y z : Fin 10) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective (triple x y z) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [triple, eq_comm]

private theorem exists_small_candidate
    (x y z : Fin 10)
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

end NormalForm10

private theorem exists_small_candidate :
    ∀ x y z : Fin 10,
      5 ≤ x.val → 5 ≤ y.val → 5 ≤ z.val →
      x ≠ y → x ≠ z → y ≠ z →
      ∃ w ∈ candidateWords x y z, w ≠ 1 ∧ w.support.card ≤ 5 := by
  intro x y z hx hy hz hxy hxz hyz
  exact NormalForm10.exists_small_candidate x y z hx hy hz hxy hxz hyz

private theorem candidates_mem_closure (x y z : Fin 10) :
    ∀ w ∈ candidateWords x y z,
      w ∈ Subgroup.closure
        ({sevenCycle, comparisonCycle x y z} : Set (Perm (Fin 10))) := by
  let K := Subgroup.closure
    ({sevenCycle, comparisonCycle x y z} : Set (Perm (Fin 10)))
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

theorem exists_small_mem_closure
    (x y z : Fin 10)
    (hx : 5 ≤ x.val) (hy : 5 ≤ y.val) (hz : 5 ≤ z.val)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ w ∈ Subgroup.closure
        ({sevenCycle, comparisonCycle x y z} : Set (Perm (Fin 10))),
      w ≠ 1 ∧ w.support.card ≤ 5 := by
  obtain ⟨w, hw, hsmall⟩ :=
    exists_small_candidate x y z hx hy hz hxy hxz hyz
  exact ⟨w, candidates_mem_closure x y z w hw, hsmall⟩

@[expose] def sevenCycle11 : Perm (Fin 11) :=
  List.formPerm [0, 1, 2, 3, 4, 5, 6]

theorem sevenCycle11_isCycle : sevenCycle11.IsCycle := by
  apply List.isCycle_formPerm
  · decide
  · norm_num

theorem sevenCycle11_card_support : sevenCycle11.support.card = 7 := by
  decide

@[expose] def sourceTuple11 : Fin 5 → Fin 11 :=
  ![0, 1, 2, 3, 7]

@[expose] def targetTuple11 : Fin 5 → Fin 11 :=
  ![0, 1, 2, 3, 4]

theorem sourceTuple11_injective : Function.Injective sourceTuple11 := by
  decide

theorem targetTuple11_injective : Function.Injective targetTuple11 := by
  decide

theorem five_le_of_ne_zero_one_two_three_four11 (x : Fin 11)
    (h0 : x ≠ 0) (h1 : x ≠ 1) (h2 : x ≠ 2) (h3 : x ≠ 3) (h4 : x ≠ 4) :
    5 ≤ x.val := by
  omega

@[expose] def comparisonCycle11 (x y z : Fin 11) : Perm (Fin 11) :=
  List.formPerm [0, 1, 2, 3, x, y, z]

private def candidateWords11 (x y z : Fin 11) : List (Perm (Fin 11)) :=
  let g := sevenCycle11
  let h := comparisonCycle11 x y z
  [g * h⁻¹, g ^ 2 * h⁻¹ ^ 2, g * h * g⁻¹ * h⁻¹, (g * h⁻¹) ^ 2]

namespace NormalForm11

private def HasSmallCandidate (x y z : Fin 11) : Prop :=
  ∃ w ∈ candidateWords11 x y z, w ≠ 1 ∧ w.support.card ≤ 5

private theorem smallCandidate_5_6_7 : HasSmallCandidate 5 6 7 := by
  refine ⟨sevenCycle11 * (comparisonCycle11 5 6 7)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords11]

private theorem smallCandidate_5_7_6 : HasSmallCandidate 5 7 6 := by
  refine ⟨sevenCycle11 * (comparisonCycle11 5 7 6)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords11]

private theorem smallCandidate_5_7_8 : HasSmallCandidate 5 7 8 := by
  refine ⟨(sevenCycle11 * (comparisonCycle11 5 7 8)⁻¹) ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords11]

private theorem smallCandidate_6_5_7 : HasSmallCandidate 6 5 7 := by
  refine ⟨sevenCycle11 ^ 2 * (comparisonCycle11 6 5 7)⁻¹ ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords11]

private theorem smallCandidate_6_7_5 : HasSmallCandidate 6 7 5 := by
  refine ⟨sevenCycle11 * (comparisonCycle11 6 7 5)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords11]

private theorem smallCandidate_6_7_8 : HasSmallCandidate 6 7 8 := by
  refine ⟨sevenCycle11 * comparisonCycle11 6 7 8 * sevenCycle11⁻¹ *
    (comparisonCycle11 6 7 8)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords11]

private theorem smallCandidate_7_5_6 : HasSmallCandidate 7 5 6 := by
  refine ⟨sevenCycle11 * (comparisonCycle11 7 5 6)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords11]

private theorem smallCandidate_7_5_8 : HasSmallCandidate 7 5 8 := by
  refine ⟨sevenCycle11 ^ 2 * (comparisonCycle11 7 5 8)⁻¹ ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords11]

private theorem smallCandidate_7_6_5 : HasSmallCandidate 7 6 5 := by
  refine ⟨sevenCycle11 * (comparisonCycle11 7 6 5)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords11]

private theorem smallCandidate_7_6_8 : HasSmallCandidate 7 6 8 := by
  refine ⟨(sevenCycle11 * (comparisonCycle11 7 6 8)⁻¹) ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords11]

private theorem smallCandidate_7_8_5 : HasSmallCandidate 7 8 5 := by
  refine ⟨(sevenCycle11 * (comparisonCycle11 7 8 5)⁻¹) ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords11]

private theorem smallCandidate_7_8_6 : HasSmallCandidate 7 8 6 := by
  refine ⟨sevenCycle11 * comparisonCycle11 7 8 6 * sevenCycle11⁻¹ *
    (comparisonCycle11 7 8 6)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords11]

private theorem smallCandidate_7_8_9 : HasSmallCandidate 7 8 9 := by
  refine ⟨sevenCycle11 * comparisonCycle11 7 8 9 * sevenCycle11⁻¹ *
    (comparisonCycle11 7 8 9)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords11]

private def triple (x y z : Fin 11) : Fin 3 → Fin 11 :=
  ![x, y, z]

private def basePoint (i : Fin 7) : Fin 11 :=
  ⟨i.val, i.isLt.trans (by norm_num)⟩

private def baseAndExternal (x y z : Fin 11) :
    Sum (Fin 7) {i : Fin 3 // 7 ≤ (triple x y z i).val} → Fin 11
  | Sum.inl i => basePoint i
  | Sum.inr i => triple x y z i

private theorem baseAndExternal_injective
    (x y z : Fin 11) (hxyz : Function.Injective (triple x y z)) :
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
    (x y z x' y' z' : Fin 11)
    (hsource : Function.Injective (triple x y z))
    (htarget : Function.Injective (triple x' y' z'))
    (hext : ∀ i, 7 ≤ (triple x y z i).val →
      7 ≤ (triple x' y' z' i).val)
    (hint : ∀ i, (triple x y z i).val < 7 →
      triple x' y' z' i = triple x y z i) :
    ∃ e : Perm (Fin 11),
      (∀ i : Fin 7, e (basePoint i) = basePoint i) ∧
      ∀ i : Fin 3, e (triple x y z i) = triple x' y' z' i := by
  let I := Sum (Fin 7) {i : Fin 3 // 7 ≤ (triple x y z i).val}
  let f : I → Fin 11 := baseAndExternal x y z
  let k : I → Fin 11
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

private theorem card_support_permCongr (e : Perm (Fin 11)) (w : Perm (Fin 11)) :
    (e.permCongr w).support.card = w.support.card := by
  have hsupport :
      (e.permCongr w).support = w.support.map e.toEmbedding := by
    ext a
    simp [Perm.mem_support]
  rw [hsupport, Finset.card_map]

private theorem smallCandidate_of_relabel
    (x y z x' y' z' : Fin 11)
    (he : ∃ e : Perm (Fin 11),
      (∀ i : Fin 7, e (basePoint i) = basePoint i) ∧
      ∀ i : Fin 3, e (triple x y z i) = triple x' y' z' i)
    (hsmall : HasSmallCandidate x' y' z') :
    HasSmallCandidate x y z := by
  obtain ⟨e, hbase, htriple⟩ := he
  have hseven : e.permCongr sevenCycle11 = sevenCycle11 := by
    have h0 := hbase (0 : Fin 7)
    have h1 := hbase (1 : Fin 7)
    have h2 := hbase (2 : Fin 7)
    have h3 := hbase (3 : Fin 7)
    have h4 := hbase (4 : Fin 7)
    have h5 := hbase (5 : Fin 7)
    have h6 := hbase (6 : Fin 7)
    rw [sevenCycle11, permCongr_formPerm]
    simp_all [basePoint]
  have hcomparison :
      e.permCongr (comparisonCycle11 x y z) = comparisonCycle11 x' y' z' := by
    rw [comparisonCycle11, comparisonCycle11,
      permCongr_formPerm]
    have h0 := hbase (0 : Fin 7)
    have h1 := hbase (1 : Fin 7)
    have h2 := hbase (2 : Fin 7)
    have h3 := hbase (3 : Fin 7)
    have hx := htriple (0 : Fin 3)
    have hy := htriple (1 : Fin 3)
    have hz := htriple (2 : Fin 3)
    simpa [basePoint, triple] using congrArg List.formPerm
      (show ([e 0, e 1, e 2, e 3, e x, e y, e z] : List (Fin 11)) =
          [0, 1, 2, 3, x', y', z'] by
        simp_all [basePoint, triple])
  obtain ⟨w, hw, hwne, hwcard⟩ := hsmall
  let F : Perm (Fin 11) ≃* Perm (Fin 11) := e.symm.permCongrHom
  have hseven' : F sevenCycle11 = sevenCycle11 := by
    calc
      F sevenCycle11 = F (e.permCongr sevenCycle11) := congrArg F hseven.symm
      _ = sevenCycle11 := e.permCongrHom.symm_apply_apply sevenCycle11
  have hcomparison' :
      F (comparisonCycle11 x' y' z') = comparisonCycle11 x y z := by
    calc
      F (comparisonCycle11 x' y' z') =
          F (e.permCongr (comparisonCycle11 x y z)) :=
        congrArg F hcomparison.symm
      _ = comparisonCycle11 x y z :=
        e.permCongrHom.symm_apply_apply (comparisonCycle11 x y z)
  refine ⟨F w, ?_, ?_, ?_⟩
  · simp only [candidateWords11, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
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
    (x y z : Fin 11) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective (triple x y z) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [triple, eq_comm]

private theorem exists_small_candidate
    (x y z : Fin 11)
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

end NormalForm11

private theorem exists_small_candidate11 :
    ∀ x y z : Fin 11,
      5 ≤ x.val → 5 ≤ y.val → 5 ≤ z.val →
      x ≠ y → x ≠ z → y ≠ z →
      ∃ w ∈ candidateWords11 x y z, w ≠ 1 ∧ w.support.card ≤ 5 := by
  intro x y z hx hy hz hxy hxz hyz
  exact NormalForm11.exists_small_candidate x y z hx hy hz hxy hxz hyz

private theorem candidates11_mem_closure (x y z : Fin 11) :
    ∀ w ∈ candidateWords11 x y z,
      w ∈ Subgroup.closure
        ({sevenCycle11, comparisonCycle11 x y z} : Set (Perm (Fin 11))) := by
  let K := Subgroup.closure
    ({sevenCycle11, comparisonCycle11 x y z} : Set (Perm (Fin 11)))
  have hg : sevenCycle11 ∈ K :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hh : comparisonCycle11 x y z ∈ K :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  intro w hw
  simp only [candidateWords11, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact K.mul_mem hg (K.inv_mem hh)
  · exact K.mul_mem (K.pow_mem hg 2) (K.pow_mem (K.inv_mem hh) 2)
  · exact K.mul_mem (K.mul_mem (K.mul_mem hg hh) (K.inv_mem hg)) (K.inv_mem hh)
  · exact K.pow_mem (K.mul_mem hg (K.inv_mem hh)) 2

theorem exists_small_mem_closure11
    (x y z : Fin 11)
    (hx : 5 ≤ x.val) (hy : 5 ≤ y.val) (hz : 5 ≤ z.val)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ w ∈ Subgroup.closure
        ({sevenCycle11, comparisonCycle11 x y z} : Set (Perm (Fin 11))),
      w ≠ 1 ∧ w.support.card ≤ 5 := by
  obtain ⟨w, hw, hsmall⟩ :=
    exists_small_candidate11 x y z hx hy hz hxy hxz hyz
  exact ⟨w, candidates11_mem_closure x y z w hw, hsmall⟩

@[expose] def sevenCycle12 : Perm (Fin 12) :=
  List.formPerm [0, 1, 2, 3, 4, 5, 6]

theorem sevenCycle12_isCycle : sevenCycle12.IsCycle := by
  apply List.isCycle_formPerm
  · decide
  · norm_num

theorem sevenCycle12_card_support : sevenCycle12.support.card = 7 := by
  decide

@[expose] def sourceTuple12 : Fin 5 → Fin 12 :=
  ![0, 1, 2, 3, 7]

@[expose] def targetTuple12 : Fin 5 → Fin 12 :=
  ![0, 1, 2, 3, 4]

theorem sourceTuple12_injective : Function.Injective sourceTuple12 := by
  decide

theorem targetTuple12_injective : Function.Injective targetTuple12 := by
  decide

theorem five_le_of_ne_zero_one_two_three_four12 (x : Fin 12)
    (h0 : x ≠ 0) (h1 : x ≠ 1) (h2 : x ≠ 2) (h3 : x ≠ 3) (h4 : x ≠ 4) :
    5 ≤ x.val := by
  omega

@[expose] def comparisonCycle12 (x y z : Fin 12) : Perm (Fin 12) :=
  List.formPerm [0, 1, 2, 3, x, y, z]

private def candidateWords12 (x y z : Fin 12) : List (Perm (Fin 12)) :=
  let g := sevenCycle12
  let h := comparisonCycle12 x y z
  [g * h⁻¹, g ^ 2 * h⁻¹ ^ 2, g * h * g⁻¹ * h⁻¹, (g * h⁻¹) ^ 2]

namespace NormalForm12

private def HasSmallCandidate (x y z : Fin 12) : Prop :=
  ∃ w ∈ candidateWords12 x y z, w ≠ 1 ∧ w.support.card ≤ 5

private theorem smallCandidate_5_6_7 : HasSmallCandidate 5 6 7 := by
  refine ⟨sevenCycle12 * (comparisonCycle12 5 6 7)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords12]

private theorem smallCandidate_5_7_6 : HasSmallCandidate 5 7 6 := by
  refine ⟨sevenCycle12 * (comparisonCycle12 5 7 6)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords12]

private theorem smallCandidate_5_7_8 : HasSmallCandidate 5 7 8 := by
  refine ⟨(sevenCycle12 * (comparisonCycle12 5 7 8)⁻¹) ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords12]

private theorem smallCandidate_6_5_7 : HasSmallCandidate 6 5 7 := by
  refine ⟨sevenCycle12 ^ 2 * (comparisonCycle12 6 5 7)⁻¹ ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords12]

private theorem smallCandidate_6_7_5 : HasSmallCandidate 6 7 5 := by
  refine ⟨sevenCycle12 * (comparisonCycle12 6 7 5)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords12]

private theorem smallCandidate_6_7_8 : HasSmallCandidate 6 7 8 := by
  refine ⟨sevenCycle12 * comparisonCycle12 6 7 8 * sevenCycle12⁻¹ *
    (comparisonCycle12 6 7 8)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords12]

private theorem smallCandidate_7_5_6 : HasSmallCandidate 7 5 6 := by
  refine ⟨sevenCycle12 * (comparisonCycle12 7 5 6)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords12]

private theorem smallCandidate_7_5_8 : HasSmallCandidate 7 5 8 := by
  refine ⟨sevenCycle12 ^ 2 * (comparisonCycle12 7 5 8)⁻¹ ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords12]

private theorem smallCandidate_7_6_5 : HasSmallCandidate 7 6 5 := by
  refine ⟨sevenCycle12 * (comparisonCycle12 7 6 5)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords12]

private theorem smallCandidate_7_6_8 : HasSmallCandidate 7 6 8 := by
  refine ⟨(sevenCycle12 * (comparisonCycle12 7 6 8)⁻¹) ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords12]

private theorem smallCandidate_7_8_5 : HasSmallCandidate 7 8 5 := by
  refine ⟨(sevenCycle12 * (comparisonCycle12 7 8 5)⁻¹) ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords12]

private theorem smallCandidate_7_8_6 : HasSmallCandidate 7 8 6 := by
  refine ⟨sevenCycle12 * comparisonCycle12 7 8 6 * sevenCycle12⁻¹ *
    (comparisonCycle12 7 8 6)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords12]

private theorem smallCandidate_7_8_9 : HasSmallCandidate 7 8 9 := by
  refine ⟨sevenCycle12 * comparisonCycle12 7 8 9 * sevenCycle12⁻¹ *
    (comparisonCycle12 7 8 9)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords12]

private def triple (x y z : Fin 12) : Fin 3 → Fin 12 :=
  ![x, y, z]

private def basePoint (i : Fin 7) : Fin 12 :=
  ⟨i.val, i.isLt.trans (by norm_num)⟩

private def baseAndExternal (x y z : Fin 12) :
    Sum (Fin 7) {i : Fin 3 // 7 ≤ (triple x y z i).val} → Fin 12
  | Sum.inl i => basePoint i
  | Sum.inr i => triple x y z i

private theorem baseAndExternal_injective
    (x y z : Fin 12) (hxyz : Function.Injective (triple x y z)) :
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
    (x y z x' y' z' : Fin 12)
    (hsource : Function.Injective (triple x y z))
    (htarget : Function.Injective (triple x' y' z'))
    (hext : ∀ i, 7 ≤ (triple x y z i).val →
      7 ≤ (triple x' y' z' i).val)
    (hint : ∀ i, (triple x y z i).val < 7 →
      triple x' y' z' i = triple x y z i) :
    ∃ e : Perm (Fin 12),
      (∀ i : Fin 7, e (basePoint i) = basePoint i) ∧
      ∀ i : Fin 3, e (triple x y z i) = triple x' y' z' i := by
  let I := Sum (Fin 7) {i : Fin 3 // 7 ≤ (triple x y z i).val}
  let f : I → Fin 12 := baseAndExternal x y z
  let k : I → Fin 12
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

private theorem card_support_permCongr (e : Perm (Fin 12)) (w : Perm (Fin 12)) :
    (e.permCongr w).support.card = w.support.card := by
  have hsupport :
      (e.permCongr w).support = w.support.map e.toEmbedding := by
    ext a
    simp [Perm.mem_support]
  rw [hsupport, Finset.card_map]

private theorem smallCandidate_of_relabel
    (x y z x' y' z' : Fin 12)
    (he : ∃ e : Perm (Fin 12),
      (∀ i : Fin 7, e (basePoint i) = basePoint i) ∧
      ∀ i : Fin 3, e (triple x y z i) = triple x' y' z' i)
    (hsmall : HasSmallCandidate x' y' z') :
    HasSmallCandidate x y z := by
  obtain ⟨e, hbase, htriple⟩ := he
  have hseven : e.permCongr sevenCycle12 = sevenCycle12 := by
    have h0 := hbase (0 : Fin 7)
    have h1 := hbase (1 : Fin 7)
    have h2 := hbase (2 : Fin 7)
    have h3 := hbase (3 : Fin 7)
    have h4 := hbase (4 : Fin 7)
    have h5 := hbase (5 : Fin 7)
    have h6 := hbase (6 : Fin 7)
    rw [sevenCycle12, permCongr_formPerm]
    simp_all [basePoint]
  have hcomparison :
      e.permCongr (comparisonCycle12 x y z) = comparisonCycle12 x' y' z' := by
    rw [comparisonCycle12, comparisonCycle12,
      permCongr_formPerm]
    have h0 := hbase (0 : Fin 7)
    have h1 := hbase (1 : Fin 7)
    have h2 := hbase (2 : Fin 7)
    have h3 := hbase (3 : Fin 7)
    have hx := htriple (0 : Fin 3)
    have hy := htriple (1 : Fin 3)
    have hz := htriple (2 : Fin 3)
    simpa [basePoint, triple] using congrArg List.formPerm
      (show ([e 0, e 1, e 2, e 3, e x, e y, e z] : List (Fin 12)) =
          [0, 1, 2, 3, x', y', z'] by
        simp_all [basePoint, triple])
  obtain ⟨w, hw, hwne, hwcard⟩ := hsmall
  let F : Perm (Fin 12) ≃* Perm (Fin 12) := e.symm.permCongrHom
  have hseven' : F sevenCycle12 = sevenCycle12 := by
    calc
      F sevenCycle12 = F (e.permCongr sevenCycle12) := congrArg F hseven.symm
      _ = sevenCycle12 := e.permCongrHom.symm_apply_apply sevenCycle12
  have hcomparison' :
      F (comparisonCycle12 x' y' z') = comparisonCycle12 x y z := by
    calc
      F (comparisonCycle12 x' y' z') =
          F (e.permCongr (comparisonCycle12 x y z)) :=
        congrArg F hcomparison.symm
      _ = comparisonCycle12 x y z :=
        e.permCongrHom.symm_apply_apply (comparisonCycle12 x y z)
  refine ⟨F w, ?_, ?_, ?_⟩
  · simp only [candidateWords12, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
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
    (x y z : Fin 12) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective (triple x y z) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [triple, eq_comm]

private theorem exists_small_candidate
    (x y z : Fin 12)
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

end NormalForm12

private theorem exists_small_candidate12 :
    ∀ x y z : Fin 12,
      5 ≤ x.val → 5 ≤ y.val → 5 ≤ z.val →
      x ≠ y → x ≠ z → y ≠ z →
      ∃ w ∈ candidateWords12 x y z, w ≠ 1 ∧ w.support.card ≤ 5 := by
  intro x y z hx hy hz hxy hxz hyz
  exact NormalForm12.exists_small_candidate x y z hx hy hz hxy hxz hyz

private theorem candidates12_mem_closure (x y z : Fin 12) :
    ∀ w ∈ candidateWords12 x y z,
      w ∈ Subgroup.closure
        ({sevenCycle12, comparisonCycle12 x y z} : Set (Perm (Fin 12))) := by
  let K := Subgroup.closure
    ({sevenCycle12, comparisonCycle12 x y z} : Set (Perm (Fin 12)))
  have hg : sevenCycle12 ∈ K :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hh : comparisonCycle12 x y z ∈ K :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  intro w hw
  simp only [candidateWords12, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact K.mul_mem hg (K.inv_mem hh)
  · exact K.mul_mem (K.pow_mem hg 2) (K.pow_mem (K.inv_mem hh) 2)
  · exact K.mul_mem (K.mul_mem (K.mul_mem hg hh) (K.inv_mem hg)) (K.inv_mem hh)
  · exact K.pow_mem (K.mul_mem hg (K.inv_mem hh)) 2

theorem exists_small_mem_closure12
    (x y z : Fin 12)
    (hx : 5 ≤ x.val) (hy : 5 ≤ y.val) (hz : 5 ≤ z.val)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ w ∈ Subgroup.closure
        ({sevenCycle12, comparisonCycle12 x y z} : Set (Perm (Fin 12))),
      w ≠ 1 ∧ w.support.card ≤ 5 := by
  obtain ⟨w, hw, hsmall⟩ :=
    exists_small_candidate12 x y z hx hy hz hxy hxz hyz
  exact ⟨w, candidates12_mem_closure x y z w hw, hsmall⟩

@[expose] def tripleSwap12 : Perm (Fin 12) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [4, 5]

@[expose] def comparisonTripleSwap12 (x y : Fin 12) : Perm (Fin 12) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [x, y]

theorem tripleSwap12_cycleType :
    tripleSwap12.cycleType = {2, 2, 2} := by
  unfold tripleSwap12
  rw [Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide),
    Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide)]
  rw [(List.isCycle_formPerm (by decide : ([0, 1] : List (Fin 12)).Nodup) (by norm_num)).cycleType,
    (List.isCycle_formPerm (by decide : ([2, 3] : List (Fin 12)).Nodup) (by norm_num)).cycleType,
    (List.isCycle_formPerm (by decide : ([4, 5] : List (Fin 12)).Nodup) (by norm_num)).cycleType]
  decide

theorem tripleSwap12_difference_small :
    ∀ x y : Fin 12, 5 ≤ x.val → 5 ≤ y.val → x ≠ y →
      let w := tripleSwap12 * (comparisonTripleSwap12 x y)⁻¹
      w ≠ 1 ∧ w.support.card ≤ 5 := by
  decide

@[expose] def doubleThreeCycle12 : Perm (Fin 12) :=
  List.formPerm [0, 1, 2] * List.formPerm [3, 4, 5]

@[expose] def comparisonDoubleThreeCycle12 (x y : Fin 12) : Perm (Fin 12) :=
  List.formPerm [0, 1, 2] * List.formPerm [3, x, y]

theorem doubleThreeCycle12_cycleType :
    doubleThreeCycle12.cycleType = {3, 3} := by
  unfold doubleThreeCycle12
  rw [Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide)]
  rw [(List.isCycle_formPerm (by decide : ([0, 1, 2] : List (Fin 12)).Nodup) (by norm_num)).cycleType,
    (List.isCycle_formPerm (by decide : ([3, 4, 5] : List (Fin 12)).Nodup) (by norm_num)).cycleType]
  decide

theorem doubleThreeCycle12_difference_small :
    ∀ x y : Fin 12, 5 ≤ x.val → 5 ≤ y.val → x ≠ y →
      let w := doubleThreeCycle12 * (comparisonDoubleThreeCycle12 x y)⁻¹
      w ≠ 1 ∧ w.support.card ≤ 5 := by
  decide

@[expose] def sevenCycle13 : Perm (Fin 13) :=
  List.formPerm [0, 1, 2, 3, 4, 5, 6]

theorem sevenCycle13_isCycle : sevenCycle13.IsCycle := by
  apply List.isCycle_formPerm
  · decide
  · norm_num

theorem sevenCycle13_card_support : sevenCycle13.support.card = 7 := by
  decide

@[expose] def sourceTuple13 : Fin 5 → Fin 13 :=
  ![0, 1, 2, 3, 7]

@[expose] def targetTuple13 : Fin 5 → Fin 13 :=
  ![0, 1, 2, 3, 4]

theorem sourceTuple13_injective : Function.Injective sourceTuple13 := by
  decide

theorem targetTuple13_injective : Function.Injective targetTuple13 := by
  decide

theorem five_le_of_ne_zero_one_two_three_four13 (x : Fin 13)
    (h0 : x ≠ 0) (h1 : x ≠ 1) (h2 : x ≠ 2) (h3 : x ≠ 3) (h4 : x ≠ 4) :
    5 ≤ x.val := by
  omega

@[expose] def comparisonCycle13 (x y z : Fin 13) : Perm (Fin 13) :=
  List.formPerm [0, 1, 2, 3, x, y, z]

private def candidateWords13 (x y z : Fin 13) : List (Perm (Fin 13)) :=
  let g := sevenCycle13
  let h := comparisonCycle13 x y z
  [g * h⁻¹, g ^ 2 * h⁻¹ ^ 2, g * h * g⁻¹ * h⁻¹, (g * h⁻¹) ^ 2]

namespace NormalForm13

private def HasSmallCandidate (x y z : Fin 13) : Prop :=
  ∃ w ∈ candidateWords13 x y z, w ≠ 1 ∧ w.support.card ≤ 5

private theorem smallCandidate_5_6_7 : HasSmallCandidate 5 6 7 := by
  refine ⟨sevenCycle13 * (comparisonCycle13 5 6 7)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords13]

private theorem smallCandidate_5_7_6 : HasSmallCandidate 5 7 6 := by
  refine ⟨sevenCycle13 * (comparisonCycle13 5 7 6)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords13]

private theorem smallCandidate_5_7_8 : HasSmallCandidate 5 7 8 := by
  refine ⟨(sevenCycle13 * (comparisonCycle13 5 7 8)⁻¹) ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords13]

private theorem smallCandidate_6_5_7 : HasSmallCandidate 6 5 7 := by
  refine ⟨sevenCycle13 ^ 2 * (comparisonCycle13 6 5 7)⁻¹ ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords13]

private theorem smallCandidate_6_7_5 : HasSmallCandidate 6 7 5 := by
  refine ⟨sevenCycle13 * (comparisonCycle13 6 7 5)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords13]

private theorem smallCandidate_6_7_8 : HasSmallCandidate 6 7 8 := by
  refine ⟨sevenCycle13 * comparisonCycle13 6 7 8 * sevenCycle13⁻¹ *
    (comparisonCycle13 6 7 8)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords13]

private theorem smallCandidate_7_5_6 : HasSmallCandidate 7 5 6 := by
  refine ⟨sevenCycle13 * (comparisonCycle13 7 5 6)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords13]

private theorem smallCandidate_7_5_8 : HasSmallCandidate 7 5 8 := by
  refine ⟨sevenCycle13 ^ 2 * (comparisonCycle13 7 5 8)⁻¹ ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords13]

private theorem smallCandidate_7_6_5 : HasSmallCandidate 7 6 5 := by
  refine ⟨sevenCycle13 * (comparisonCycle13 7 6 5)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords13]

private theorem smallCandidate_7_6_8 : HasSmallCandidate 7 6 8 := by
  refine ⟨(sevenCycle13 * (comparisonCycle13 7 6 8)⁻¹) ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords13]

private theorem smallCandidate_7_8_5 : HasSmallCandidate 7 8 5 := by
  refine ⟨(sevenCycle13 * (comparisonCycle13 7 8 5)⁻¹) ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords13]

private theorem smallCandidate_7_8_6 : HasSmallCandidate 7 8 6 := by
  refine ⟨sevenCycle13 * comparisonCycle13 7 8 6 * sevenCycle13⁻¹ *
    (comparisonCycle13 7 8 6)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords13]

private theorem smallCandidate_7_8_9 : HasSmallCandidate 7 8 9 := by
  refine ⟨sevenCycle13 * comparisonCycle13 7 8 9 * sevenCycle13⁻¹ *
    (comparisonCycle13 7 8 9)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords13]

private def triple (x y z : Fin 13) : Fin 3 → Fin 13 :=
  ![x, y, z]

private def basePoint (i : Fin 7) : Fin 13 :=
  ⟨i.val, i.isLt.trans (by norm_num)⟩

private def baseAndExternal (x y z : Fin 13) :
    Sum (Fin 7) {i : Fin 3 // 7 ≤ (triple x y z i).val} → Fin 13
  | Sum.inl i => basePoint i
  | Sum.inr i => triple x y z i

private theorem baseAndExternal_injective
    (x y z : Fin 13) (hxyz : Function.Injective (triple x y z)) :
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
    (x y z x' y' z' : Fin 13)
    (hsource : Function.Injective (triple x y z))
    (htarget : Function.Injective (triple x' y' z'))
    (hext : ∀ i, 7 ≤ (triple x y z i).val →
      7 ≤ (triple x' y' z' i).val)
    (hint : ∀ i, (triple x y z i).val < 7 →
      triple x' y' z' i = triple x y z i) :
    ∃ e : Perm (Fin 13),
      (∀ i : Fin 7, e (basePoint i) = basePoint i) ∧
      ∀ i : Fin 3, e (triple x y z i) = triple x' y' z' i := by
  let I := Sum (Fin 7) {i : Fin 3 // 7 ≤ (triple x y z i).val}
  let f : I → Fin 13 := baseAndExternal x y z
  let k : I → Fin 13
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

private theorem card_support_permCongr (e : Perm (Fin 13)) (w : Perm (Fin 13)) :
    (e.permCongr w).support.card = w.support.card := by
  have hsupport :
      (e.permCongr w).support = w.support.map e.toEmbedding := by
    ext a
    simp [Perm.mem_support]
  rw [hsupport, Finset.card_map]

private theorem smallCandidate_of_relabel
    (x y z x' y' z' : Fin 13)
    (he : ∃ e : Perm (Fin 13),
      (∀ i : Fin 7, e (basePoint i) = basePoint i) ∧
      ∀ i : Fin 3, e (triple x y z i) = triple x' y' z' i)
    (hsmall : HasSmallCandidate x' y' z') :
    HasSmallCandidate x y z := by
  obtain ⟨e, hbase, htriple⟩ := he
  have hseven : e.permCongr sevenCycle13 = sevenCycle13 := by
    have h0 := hbase (0 : Fin 7)
    have h1 := hbase (1 : Fin 7)
    have h2 := hbase (2 : Fin 7)
    have h3 := hbase (3 : Fin 7)
    have h4 := hbase (4 : Fin 7)
    have h5 := hbase (5 : Fin 7)
    have h6 := hbase (6 : Fin 7)
    rw [sevenCycle13, permCongr_formPerm]
    simp_all [basePoint]
  have hcomparison :
      e.permCongr (comparisonCycle13 x y z) = comparisonCycle13 x' y' z' := by
    rw [comparisonCycle13, comparisonCycle13,
      permCongr_formPerm]
    have h0 := hbase (0 : Fin 7)
    have h1 := hbase (1 : Fin 7)
    have h2 := hbase (2 : Fin 7)
    have h3 := hbase (3 : Fin 7)
    have hx := htriple (0 : Fin 3)
    have hy := htriple (1 : Fin 3)
    have hz := htriple (2 : Fin 3)
    simpa [basePoint, triple] using congrArg List.formPerm
      (show ([e 0, e 1, e 2, e 3, e x, e y, e z] : List (Fin 13)) =
          [0, 1, 2, 3, x', y', z'] by
        simp_all [basePoint, triple])
  obtain ⟨w, hw, hwne, hwcard⟩ := hsmall
  let F : Perm (Fin 13) ≃* Perm (Fin 13) := e.symm.permCongrHom
  have hseven' : F sevenCycle13 = sevenCycle13 := by
    calc
      F sevenCycle13 = F (e.permCongr sevenCycle13) := congrArg F hseven.symm
      _ = sevenCycle13 := e.permCongrHom.symm_apply_apply sevenCycle13
  have hcomparison' :
      F (comparisonCycle13 x' y' z') = comparisonCycle13 x y z := by
    calc
      F (comparisonCycle13 x' y' z') =
          F (e.permCongr (comparisonCycle13 x y z)) :=
        congrArg F hcomparison.symm
      _ = comparisonCycle13 x y z :=
        e.permCongrHom.symm_apply_apply (comparisonCycle13 x y z)
  refine ⟨F w, ?_, ?_, ?_⟩
  · simp only [candidateWords13, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
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
    (x y z : Fin 13) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective (triple x y z) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [triple, eq_comm]

private theorem exists_small_candidate
    (x y z : Fin 13)
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

end NormalForm13

private theorem exists_small_candidate13 :
    ∀ x y z : Fin 13,
      5 ≤ x.val → 5 ≤ y.val → 5 ≤ z.val →
      x ≠ y → x ≠ z → y ≠ z →
      ∃ w ∈ candidateWords13 x y z, w ≠ 1 ∧ w.support.card ≤ 5 := by
  intro x y z hx hy hz hxy hxz hyz
  exact NormalForm13.exists_small_candidate x y z hx hy hz hxy hxz hyz

private theorem candidates13_mem_closure (x y z : Fin 13) :
    ∀ w ∈ candidateWords13 x y z,
      w ∈ Subgroup.closure
        ({sevenCycle13, comparisonCycle13 x y z} : Set (Perm (Fin 13))) := by
  let K := Subgroup.closure
    ({sevenCycle13, comparisonCycle13 x y z} : Set (Perm (Fin 13)))
  have hg : sevenCycle13 ∈ K :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hh : comparisonCycle13 x y z ∈ K :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  intro w hw
  simp only [candidateWords13, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact K.mul_mem hg (K.inv_mem hh)
  · exact K.mul_mem (K.pow_mem hg 2) (K.pow_mem (K.inv_mem hh) 2)
  · exact K.mul_mem (K.mul_mem (K.mul_mem hg hh) (K.inv_mem hg)) (K.inv_mem hh)
  · exact K.pow_mem (K.mul_mem hg (K.inv_mem hh)) 2

theorem exists_small_mem_closure13
    (x y z : Fin 13)
    (hx : 5 ≤ x.val) (hy : 5 ≤ y.val) (hz : 5 ≤ z.val)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ w ∈ Subgroup.closure
        ({sevenCycle13, comparisonCycle13 x y z} : Set (Perm (Fin 13))),
      w ≠ 1 ∧ w.support.card ≤ 5 := by
  obtain ⟨w, hw, hsmall⟩ :=
    exists_small_candidate13 x y z hx hy hz hxy hxz hyz
  exact ⟨w, candidates13_mem_closure x y z w hw, hsmall⟩

@[expose] def tripleSwap13 : Perm (Fin 13) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [4, 5]

@[expose] def comparisonTripleSwap13 (x y : Fin 13) : Perm (Fin 13) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [x, y]

theorem tripleSwap13_cycleType :
    tripleSwap13.cycleType = {2, 2, 2} := by
  unfold tripleSwap13
  rw [Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide),
    Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide)]
  rw [(List.isCycle_formPerm (by decide : ([0, 1] : List (Fin 13)).Nodup) (by norm_num)).cycleType,
    (List.isCycle_formPerm (by decide : ([2, 3] : List (Fin 13)).Nodup) (by norm_num)).cycleType,
    (List.isCycle_formPerm (by decide : ([4, 5] : List (Fin 13)).Nodup) (by norm_num)).cycleType]
  decide

theorem tripleSwap13_difference_small :
    ∀ x y : Fin 13, 5 ≤ x.val → 5 ≤ y.val → x ≠ y →
      let w := tripleSwap13 * (comparisonTripleSwap13 x y)⁻¹
      w ≠ 1 ∧ w.support.card ≤ 5 := by
  decide

@[expose] def doubleThreeCycle13 : Perm (Fin 13) :=
  List.formPerm [0, 1, 2] * List.formPerm [3, 4, 5]

@[expose] def comparisonDoubleThreeCycle13 (x y : Fin 13) : Perm (Fin 13) :=
  List.formPerm [0, 1, 2] * List.formPerm [3, x, y]

theorem doubleThreeCycle13_cycleType :
    doubleThreeCycle13.cycleType = {3, 3} := by
  unfold doubleThreeCycle13
  rw [Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide)]
  rw [(List.isCycle_formPerm (by decide : ([0, 1, 2] : List (Fin 13)).Nodup) (by norm_num)).cycleType,
    (List.isCycle_formPerm (by decide : ([3, 4, 5] : List (Fin 13)).Nodup) (by norm_num)).cycleType]
  decide

theorem doubleThreeCycle13_difference_small :
    ∀ x y : Fin 13, 5 ≤ x.val → 5 ≤ y.val → x ≠ y →
      let w := doubleThreeCycle13 * (comparisonDoubleThreeCycle13 x y)⁻¹
      w ≠ 1 ∧ w.support.card ≤ 5 := by
  decide

@[expose] def sevenCycle14 : Perm (Fin 14) :=
  List.formPerm [0, 1, 2, 3, 4, 5, 6]

theorem sevenCycle14_isCycle : sevenCycle14.IsCycle := by
  apply List.isCycle_formPerm
  · decide
  · norm_num

theorem sevenCycle14_card_support : sevenCycle14.support.card = 7 := by
  decide

@[expose] def sourceTuple14 : Fin 5 → Fin 14 :=
  ![0, 1, 2, 3, 7]

@[expose] def targetTuple14 : Fin 5 → Fin 14 :=
  ![0, 1, 2, 3, 4]

theorem sourceTuple14_injective : Function.Injective sourceTuple14 := by
  decide

theorem targetTuple14_injective : Function.Injective targetTuple14 := by
  decide

theorem five_le_of_ne_zero_one_two_three_four14 (x : Fin 14)
    (h0 : x ≠ 0) (h1 : x ≠ 1) (h2 : x ≠ 2) (h3 : x ≠ 3) (h4 : x ≠ 4) :
    5 ≤ x.val := by
  omega

@[expose] def comparisonCycle14 (x y z : Fin 14) : Perm (Fin 14) :=
  List.formPerm [0, 1, 2, 3, x, y, z]

private def candidateWords14 (x y z : Fin 14) : List (Perm (Fin 14)) :=
  let g := sevenCycle14
  let h := comparisonCycle14 x y z
  [g * h⁻¹, g ^ 2 * h⁻¹ ^ 2, g * h * g⁻¹ * h⁻¹, (g * h⁻¹) ^ 2]

namespace NormalForm14

private def HasSmallCandidate (x y z : Fin 14) : Prop :=
  ∃ w ∈ candidateWords14 x y z, w ≠ 1 ∧ w.support.card ≤ 5

private theorem smallCandidate_5_6_7 : HasSmallCandidate 5 6 7 := by
  refine ⟨sevenCycle14 * (comparisonCycle14 5 6 7)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords14]

private theorem smallCandidate_5_7_6 : HasSmallCandidate 5 7 6 := by
  refine ⟨sevenCycle14 * (comparisonCycle14 5 7 6)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords14]

private theorem smallCandidate_5_7_8 : HasSmallCandidate 5 7 8 := by
  refine ⟨(sevenCycle14 * (comparisonCycle14 5 7 8)⁻¹) ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords14]

private theorem smallCandidate_6_5_7 : HasSmallCandidate 6 5 7 := by
  refine ⟨sevenCycle14 ^ 2 * (comparisonCycle14 6 5 7)⁻¹ ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords14]

private theorem smallCandidate_6_7_5 : HasSmallCandidate 6 7 5 := by
  refine ⟨sevenCycle14 * (comparisonCycle14 6 7 5)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords14]

private theorem smallCandidate_6_7_8 : HasSmallCandidate 6 7 8 := by
  refine ⟨sevenCycle14 * comparisonCycle14 6 7 8 * sevenCycle14⁻¹ *
    (comparisonCycle14 6 7 8)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords14]

private theorem smallCandidate_7_5_6 : HasSmallCandidate 7 5 6 := by
  refine ⟨sevenCycle14 * (comparisonCycle14 7 5 6)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords14]

private theorem smallCandidate_7_5_8 : HasSmallCandidate 7 5 8 := by
  refine ⟨sevenCycle14 ^ 2 * (comparisonCycle14 7 5 8)⁻¹ ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords14]

private theorem smallCandidate_7_6_5 : HasSmallCandidate 7 6 5 := by
  refine ⟨sevenCycle14 * (comparisonCycle14 7 6 5)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords14]

private theorem smallCandidate_7_6_8 : HasSmallCandidate 7 6 8 := by
  refine ⟨(sevenCycle14 * (comparisonCycle14 7 6 8)⁻¹) ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords14]

private theorem smallCandidate_7_8_5 : HasSmallCandidate 7 8 5 := by
  refine ⟨(sevenCycle14 * (comparisonCycle14 7 8 5)⁻¹) ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords14]

private theorem smallCandidate_7_8_6 : HasSmallCandidate 7 8 6 := by
  refine ⟨sevenCycle14 * comparisonCycle14 7 8 6 * sevenCycle14⁻¹ *
    (comparisonCycle14 7 8 6)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords14]

private theorem smallCandidate_7_8_9 : HasSmallCandidate 7 8 9 := by
  refine ⟨sevenCycle14 * comparisonCycle14 7 8 9 * sevenCycle14⁻¹ *
    (comparisonCycle14 7 8 9)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords14]

private def triple (x y z : Fin 14) : Fin 3 → Fin 14 :=
  ![x, y, z]

private def basePoint (i : Fin 7) : Fin 14 :=
  ⟨i.val, i.isLt.trans (by norm_num)⟩

private def baseAndExternal (x y z : Fin 14) :
    Sum (Fin 7) {i : Fin 3 // 7 ≤ (triple x y z i).val} → Fin 14
  | Sum.inl i => basePoint i
  | Sum.inr i => triple x y z i

private theorem baseAndExternal_injective
    (x y z : Fin 14) (hxyz : Function.Injective (triple x y z)) :
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
    (x y z x' y' z' : Fin 14)
    (hsource : Function.Injective (triple x y z))
    (htarget : Function.Injective (triple x' y' z'))
    (hext : ∀ i, 7 ≤ (triple x y z i).val →
      7 ≤ (triple x' y' z' i).val)
    (hint : ∀ i, (triple x y z i).val < 7 →
      triple x' y' z' i = triple x y z i) :
    ∃ e : Perm (Fin 14),
      (∀ i : Fin 7, e (basePoint i) = basePoint i) ∧
      ∀ i : Fin 3, e (triple x y z i) = triple x' y' z' i := by
  let I := Sum (Fin 7) {i : Fin 3 // 7 ≤ (triple x y z i).val}
  let f : I → Fin 14 := baseAndExternal x y z
  let k : I → Fin 14
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

private theorem card_support_permCongr (e : Perm (Fin 14)) (w : Perm (Fin 14)) :
    (e.permCongr w).support.card = w.support.card := by
  have hsupport :
      (e.permCongr w).support = w.support.map e.toEmbedding := by
    ext a
    simp [Perm.mem_support]
  rw [hsupport, Finset.card_map]

private theorem smallCandidate_of_relabel
    (x y z x' y' z' : Fin 14)
    (he : ∃ e : Perm (Fin 14),
      (∀ i : Fin 7, e (basePoint i) = basePoint i) ∧
      ∀ i : Fin 3, e (triple x y z i) = triple x' y' z' i)
    (hsmall : HasSmallCandidate x' y' z') :
    HasSmallCandidate x y z := by
  obtain ⟨e, hbase, htriple⟩ := he
  have hseven : e.permCongr sevenCycle14 = sevenCycle14 := by
    have h0 := hbase (0 : Fin 7)
    have h1 := hbase (1 : Fin 7)
    have h2 := hbase (2 : Fin 7)
    have h3 := hbase (3 : Fin 7)
    have h4 := hbase (4 : Fin 7)
    have h5 := hbase (5 : Fin 7)
    have h6 := hbase (6 : Fin 7)
    rw [sevenCycle14, permCongr_formPerm]
    simp_all [basePoint]
  have hcomparison :
      e.permCongr (comparisonCycle14 x y z) = comparisonCycle14 x' y' z' := by
    rw [comparisonCycle14, comparisonCycle14,
      permCongr_formPerm]
    have h0 := hbase (0 : Fin 7)
    have h1 := hbase (1 : Fin 7)
    have h2 := hbase (2 : Fin 7)
    have h3 := hbase (3 : Fin 7)
    have hx := htriple (0 : Fin 3)
    have hy := htriple (1 : Fin 3)
    have hz := htriple (2 : Fin 3)
    simpa [basePoint, triple] using congrArg List.formPerm
      (show ([e 0, e 1, e 2, e 3, e x, e y, e z] : List (Fin 14)) =
          [0, 1, 2, 3, x', y', z'] by
        simp_all [basePoint, triple])
  obtain ⟨w, hw, hwne, hwcard⟩ := hsmall
  let F : Perm (Fin 14) ≃* Perm (Fin 14) := e.symm.permCongrHom
  have hseven' : F sevenCycle14 = sevenCycle14 := by
    calc
      F sevenCycle14 = F (e.permCongr sevenCycle14) := congrArg F hseven.symm
      _ = sevenCycle14 := e.permCongrHom.symm_apply_apply sevenCycle14
  have hcomparison' :
      F (comparisonCycle14 x' y' z') = comparisonCycle14 x y z := by
    calc
      F (comparisonCycle14 x' y' z') =
          F (e.permCongr (comparisonCycle14 x y z)) :=
        congrArg F hcomparison.symm
      _ = comparisonCycle14 x y z :=
        e.permCongrHom.symm_apply_apply (comparisonCycle14 x y z)
  refine ⟨F w, ?_, ?_, ?_⟩
  · simp only [candidateWords14, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
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
    (x y z : Fin 14) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective (triple x y z) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [triple, eq_comm]

private theorem exists_small_candidate
    (x y z : Fin 14)
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

end NormalForm14

private theorem exists_small_candidate14 :
    ∀ x y z : Fin 14,
      5 ≤ x.val → 5 ≤ y.val → 5 ≤ z.val →
      x ≠ y → x ≠ z → y ≠ z →
      ∃ w ∈ candidateWords14 x y z, w ≠ 1 ∧ w.support.card ≤ 5 := by
  intro x y z hx hy hz hxy hxz hyz
  exact NormalForm14.exists_small_candidate x y z hx hy hz hxy hxz hyz

private theorem candidates14_mem_closure (x y z : Fin 14) :
    ∀ w ∈ candidateWords14 x y z,
      w ∈ Subgroup.closure
        ({sevenCycle14, comparisonCycle14 x y z} : Set (Perm (Fin 14))) := by
  let K := Subgroup.closure
    ({sevenCycle14, comparisonCycle14 x y z} : Set (Perm (Fin 14)))
  have hg : sevenCycle14 ∈ K :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hh : comparisonCycle14 x y z ∈ K :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  intro w hw
  simp only [candidateWords14, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact K.mul_mem hg (K.inv_mem hh)
  · exact K.mul_mem (K.pow_mem hg 2) (K.pow_mem (K.inv_mem hh) 2)
  · exact K.mul_mem (K.mul_mem (K.mul_mem hg hh) (K.inv_mem hg)) (K.inv_mem hh)
  · exact K.pow_mem (K.mul_mem hg (K.inv_mem hh)) 2

theorem exists_small_mem_closure14
    (x y z : Fin 14)
    (hx : 5 ≤ x.val) (hy : 5 ≤ y.val) (hz : 5 ≤ z.val)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ w ∈ Subgroup.closure
        ({sevenCycle14, comparisonCycle14 x y z} : Set (Perm (Fin 14))),
      w ≠ 1 ∧ w.support.card ≤ 5 := by
  obtain ⟨w, hw, hsmall⟩ :=
    exists_small_candidate14 x y z hx hy hz hxy hxz hyz
  exact ⟨w, candidates14_mem_closure x y z w hw, hsmall⟩

@[expose] def tripleSwap14 : Perm (Fin 14) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [4, 5]

@[expose] def comparisonTripleSwap14 (x y : Fin 14) : Perm (Fin 14) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [x, y]

theorem tripleSwap14_cycleType :
    tripleSwap14.cycleType = {2, 2, 2} := by
  unfold tripleSwap14
  rw [Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide),
    Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide)]
  rw [(List.isCycle_formPerm (by decide : ([0, 1] : List (Fin 14)).Nodup) (by norm_num)).cycleType,
    (List.isCycle_formPerm (by decide : ([2, 3] : List (Fin 14)).Nodup) (by norm_num)).cycleType,
    (List.isCycle_formPerm (by decide : ([4, 5] : List (Fin 14)).Nodup) (by norm_num)).cycleType]
  decide

theorem tripleSwap14_difference_small :
    ∀ x y : Fin 14, 5 ≤ x.val → 5 ≤ y.val → x ≠ y →
      let w := tripleSwap14 * (comparisonTripleSwap14 x y)⁻¹
      w ≠ 1 ∧ w.support.card ≤ 5 := by
  decide

@[expose] def doubleThreeCycle14 : Perm (Fin 14) :=
  List.formPerm [0, 1, 2] * List.formPerm [3, 4, 5]

@[expose] def comparisonDoubleThreeCycle14 (x y : Fin 14) : Perm (Fin 14) :=
  List.formPerm [0, 1, 2] * List.formPerm [3, x, y]

theorem doubleThreeCycle14_cycleType :
    doubleThreeCycle14.cycleType = {3, 3} := by
  unfold doubleThreeCycle14
  rw [Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide)]
  rw [(List.isCycle_formPerm (by decide : ([0, 1, 2] : List (Fin 14)).Nodup) (by norm_num)).cycleType,
    (List.isCycle_formPerm (by decide : ([3, 4, 5] : List (Fin 14)).Nodup) (by norm_num)).cycleType]
  decide

theorem doubleThreeCycle14_difference_small :
    ∀ x y : Fin 14, 5 ≤ x.val → 5 ≤ y.val → x ≠ y →
      let w := doubleThreeCycle14 *
        (comparisonDoubleThreeCycle14 x y)⁻¹
      w ≠ 1 ∧ w.support.card ≤ 5 := by
  decide

@[expose] def sevenCycle15 : Perm (Fin 15) :=
  List.formPerm [0, 1, 2, 3, 4, 5, 6]

theorem sevenCycle15_isCycle : sevenCycle15.IsCycle := by
  apply List.isCycle_formPerm
  · decide
  · norm_num

theorem sevenCycle15_card_support : sevenCycle15.support.card = 7 := by
  decide

@[expose] def sourceTuple15 : Fin 5 → Fin 15 :=
  ![0, 1, 2, 3, 7]

@[expose] def targetTuple15 : Fin 5 → Fin 15 :=
  ![0, 1, 2, 3, 4]

theorem sourceTuple15_injective : Function.Injective sourceTuple15 := by
  decide

theorem targetTuple15_injective : Function.Injective targetTuple15 := by
  decide

theorem five_le_of_ne_zero_one_two_three_four15 (x : Fin 15)
    (h0 : x ≠ 0) (h1 : x ≠ 1) (h2 : x ≠ 2) (h3 : x ≠ 3) (h4 : x ≠ 4) :
    5 ≤ x.val := by
  omega

@[expose] def comparisonCycle15 (x y z : Fin 15) : Perm (Fin 15) :=
  List.formPerm [0, 1, 2, 3, x, y, z]

private def candidateWords15 (x y z : Fin 15) : List (Perm (Fin 15)) :=
  let g := sevenCycle15
  let h := comparisonCycle15 x y z
  [g * h⁻¹, g ^ 2 * h⁻¹ ^ 2, g * h * g⁻¹ * h⁻¹, (g * h⁻¹) ^ 2]

namespace NormalForm15

private def HasSmallCandidate (x y z : Fin 15) : Prop :=
  ∃ w ∈ candidateWords15 x y z, w ≠ 1 ∧ w.support.card ≤ 5

private theorem smallCandidate_5_6_7 : HasSmallCandidate 5 6 7 := by
  refine ⟨sevenCycle15 * (comparisonCycle15 5 6 7)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords15]

private theorem smallCandidate_5_7_6 : HasSmallCandidate 5 7 6 := by
  refine ⟨sevenCycle15 * (comparisonCycle15 5 7 6)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords15]

private theorem smallCandidate_5_7_8 : HasSmallCandidate 5 7 8 := by
  refine ⟨(sevenCycle15 * (comparisonCycle15 5 7 8)⁻¹) ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords15]

private theorem smallCandidate_6_5_7 : HasSmallCandidate 6 5 7 := by
  refine ⟨sevenCycle15 ^ 2 * (comparisonCycle15 6 5 7)⁻¹ ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords15]

private theorem smallCandidate_6_7_5 : HasSmallCandidate 6 7 5 := by
  refine ⟨sevenCycle15 * (comparisonCycle15 6 7 5)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords15]

private theorem smallCandidate_6_7_8 : HasSmallCandidate 6 7 8 := by
  refine ⟨sevenCycle15 * comparisonCycle15 6 7 8 * sevenCycle15⁻¹ *
    (comparisonCycle15 6 7 8)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords15]

private theorem smallCandidate_7_5_6 : HasSmallCandidate 7 5 6 := by
  refine ⟨sevenCycle15 * (comparisonCycle15 7 5 6)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords15]

private theorem smallCandidate_7_5_8 : HasSmallCandidate 7 5 8 := by
  refine ⟨sevenCycle15 ^ 2 * (comparisonCycle15 7 5 8)⁻¹ ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords15]

private theorem smallCandidate_7_6_5 : HasSmallCandidate 7 6 5 := by
  refine ⟨sevenCycle15 * (comparisonCycle15 7 6 5)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords15]

private theorem smallCandidate_7_6_8 : HasSmallCandidate 7 6 8 := by
  refine ⟨(sevenCycle15 * (comparisonCycle15 7 6 8)⁻¹) ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords15]

private theorem smallCandidate_7_8_5 : HasSmallCandidate 7 8 5 := by
  refine ⟨(sevenCycle15 * (comparisonCycle15 7 8 5)⁻¹) ^ 2,
    ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords15]

private theorem smallCandidate_7_8_6 : HasSmallCandidate 7 8 6 := by
  refine ⟨sevenCycle15 * comparisonCycle15 7 8 6 * sevenCycle15⁻¹ *
    (comparisonCycle15 7 8 6)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords15]

private theorem smallCandidate_7_8_9 : HasSmallCandidate 7 8 9 := by
  refine ⟨sevenCycle15 * comparisonCycle15 7 8 9 * sevenCycle15⁻¹ *
    (comparisonCycle15 7 8 9)⁻¹, ?_, by decide +kernel, by decide +kernel⟩
  simp [candidateWords15]

private def triple (x y z : Fin 15) : Fin 3 → Fin 15 :=
  ![x, y, z]

private def basePoint (i : Fin 7) : Fin 15 :=
  ⟨i.val, i.isLt.trans (by norm_num)⟩

private def baseAndExternal (x y z : Fin 15) :
    Sum (Fin 7) {i : Fin 3 // 7 ≤ (triple x y z i).val} → Fin 15
  | Sum.inl i => basePoint i
  | Sum.inr i => triple x y z i

private theorem baseAndExternal_injective
    (x y z : Fin 15) (hxyz : Function.Injective (triple x y z)) :
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
    (x y z x' y' z' : Fin 15)
    (hsource : Function.Injective (triple x y z))
    (htarget : Function.Injective (triple x' y' z'))
    (hext : ∀ i, 7 ≤ (triple x y z i).val →
      7 ≤ (triple x' y' z' i).val)
    (hint : ∀ i, (triple x y z i).val < 7 →
      triple x' y' z' i = triple x y z i) :
    ∃ e : Perm (Fin 15),
      (∀ i : Fin 7, e (basePoint i) = basePoint i) ∧
      ∀ i : Fin 3, e (triple x y z i) = triple x' y' z' i := by
  let I := Sum (Fin 7) {i : Fin 3 // 7 ≤ (triple x y z i).val}
  let f : I → Fin 15 := baseAndExternal x y z
  let k : I → Fin 15
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

private theorem card_support_permCongr (e : Perm (Fin 15)) (w : Perm (Fin 15)) :
    (e.permCongr w).support.card = w.support.card := by
  have hsupport :
      (e.permCongr w).support = w.support.map e.toEmbedding := by
    ext a
    simp [Perm.mem_support]
  rw [hsupport, Finset.card_map]

private theorem smallCandidate_of_relabel
    (x y z x' y' z' : Fin 15)
    (he : ∃ e : Perm (Fin 15),
      (∀ i : Fin 7, e (basePoint i) = basePoint i) ∧
      ∀ i : Fin 3, e (triple x y z i) = triple x' y' z' i)
    (hsmall : HasSmallCandidate x' y' z') :
    HasSmallCandidate x y z := by
  obtain ⟨e, hbase, htriple⟩ := he
  have hseven : e.permCongr sevenCycle15 = sevenCycle15 := by
    have h0 := hbase (0 : Fin 7)
    have h1 := hbase (1 : Fin 7)
    have h2 := hbase (2 : Fin 7)
    have h3 := hbase (3 : Fin 7)
    have h4 := hbase (4 : Fin 7)
    have h5 := hbase (5 : Fin 7)
    have h6 := hbase (6 : Fin 7)
    rw [sevenCycle15, permCongr_formPerm]
    simp_all [basePoint]
  have hcomparison :
      e.permCongr (comparisonCycle15 x y z) = comparisonCycle15 x' y' z' := by
    rw [comparisonCycle15, comparisonCycle15,
      permCongr_formPerm]
    have h0 := hbase (0 : Fin 7)
    have h1 := hbase (1 : Fin 7)
    have h2 := hbase (2 : Fin 7)
    have h3 := hbase (3 : Fin 7)
    have hx := htriple (0 : Fin 3)
    have hy := htriple (1 : Fin 3)
    have hz := htriple (2 : Fin 3)
    simpa [basePoint, triple] using congrArg List.formPerm
      (show ([e 0, e 1, e 2, e 3, e x, e y, e z] : List (Fin 15)) =
          [0, 1, 2, 3, x', y', z'] by
        simp_all [basePoint, triple])
  obtain ⟨w, hw, hwne, hwcard⟩ := hsmall
  let F : Perm (Fin 15) ≃* Perm (Fin 15) := e.symm.permCongrHom
  have hseven' : F sevenCycle15 = sevenCycle15 := by
    calc
      F sevenCycle15 = F (e.permCongr sevenCycle15) := congrArg F hseven.symm
      _ = sevenCycle15 := e.permCongrHom.symm_apply_apply sevenCycle15
  have hcomparison' :
      F (comparisonCycle15 x' y' z') = comparisonCycle15 x y z := by
    calc
      F (comparisonCycle15 x' y' z') =
          F (e.permCongr (comparisonCycle15 x y z)) :=
        congrArg F hcomparison.symm
      _ = comparisonCycle15 x y z :=
        e.permCongrHom.symm_apply_apply (comparisonCycle15 x y z)
  refine ⟨F w, ?_, ?_, ?_⟩
  · simp only [candidateWords15, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
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
    (x y z : Fin 15) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective (triple x y z) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [triple, eq_comm]

private theorem exists_small_candidate
    (x y z : Fin 15)
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

end NormalForm15

private theorem exists_small_candidate15 :
    ∀ x y z : Fin 15,
      5 ≤ x.val → 5 ≤ y.val → 5 ≤ z.val →
      x ≠ y → x ≠ z → y ≠ z →
      ∃ w ∈ candidateWords15 x y z, w ≠ 1 ∧ w.support.card ≤ 5 := by
  intro x y z hx hy hz hxy hxz hyz
  exact NormalForm15.exists_small_candidate x y z hx hy hz hxy hxz hyz

private theorem candidates15_mem_closure (x y z : Fin 15) :
    ∀ w ∈ candidateWords15 x y z,
      w ∈ Subgroup.closure
        ({sevenCycle15, comparisonCycle15 x y z} : Set (Perm (Fin 15))) := by
  let K := Subgroup.closure
    ({sevenCycle15, comparisonCycle15 x y z} : Set (Perm (Fin 15)))
  have hg : sevenCycle15 ∈ K :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hh : comparisonCycle15 x y z ∈ K :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  intro w hw
  simp only [candidateWords15, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact K.mul_mem hg (K.inv_mem hh)
  · exact K.mul_mem (K.pow_mem hg 2) (K.pow_mem (K.inv_mem hh) 2)
  · exact K.mul_mem (K.mul_mem (K.mul_mem hg hh) (K.inv_mem hg)) (K.inv_mem hh)
  · exact K.pow_mem (K.mul_mem hg (K.inv_mem hh)) 2

theorem exists_small_mem_closure15
    (x y z : Fin 15)
    (hx : 5 ≤ x.val) (hy : 5 ≤ y.val) (hz : 5 ≤ z.val)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ w ∈ Subgroup.closure
        ({sevenCycle15, comparisonCycle15 x y z} : Set (Perm (Fin 15))),
      w ≠ 1 ∧ w.support.card ≤ 5 := by
  obtain ⟨w, hw, hsmall⟩ :=
    exists_small_candidate15 x y z hx hy hz hxy hxz hyz
  exact ⟨w, candidates15_mem_closure x y z w hw, hsmall⟩

@[expose] def tripleSwap15 : Perm (Fin 15) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [4, 5]

@[expose] def comparisonTripleSwap15 (x y : Fin 15) : Perm (Fin 15) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [x, y]

theorem tripleSwap15_cycleType :
    tripleSwap15.cycleType = {2, 2, 2} := by
  unfold tripleSwap15
  rw [Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide),
    Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide)]
  rw [(List.isCycle_formPerm (by decide : ([0, 1] : List (Fin 15)).Nodup) (by norm_num)).cycleType,
    (List.isCycle_formPerm (by decide : ([2, 3] : List (Fin 15)).Nodup) (by norm_num)).cycleType,
    (List.isCycle_formPerm (by decide : ([4, 5] : List (Fin 15)).Nodup) (by norm_num)).cycleType]
  decide

theorem tripleSwap15_difference_small :
    ∀ x y : Fin 15, 5 ≤ x.val → 5 ≤ y.val → x ≠ y →
      let w := tripleSwap15 * (comparisonTripleSwap15 x y)⁻¹
      w ≠ 1 ∧ w.support.card ≤ 5 := by
  decide

@[expose] def doubleThreeCycle15 : Perm (Fin 15) :=
  List.formPerm [0, 1, 2] * List.formPerm [3, 4, 5]

@[expose] def comparisonDoubleThreeCycle15 (x y : Fin 15) : Perm (Fin 15) :=
  List.formPerm [0, 1, 2] * List.formPerm [3, x, y]

theorem doubleThreeCycle15_cycleType :
    doubleThreeCycle15.cycleType = {3, 3} := by
  unfold doubleThreeCycle15
  rw [Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide)]
  rw [(List.isCycle_formPerm (by decide : ([0, 1, 2] : List (Fin 15)).Nodup) (by norm_num)).cycleType,
    (List.isCycle_formPerm (by decide : ([3, 4, 5] : List (Fin 15)).Nodup) (by norm_num)).cycleType]
  decide

theorem doubleThreeCycle15_difference_small :
    ∀ x y : Fin 15, 5 ≤ x.val → 5 ≤ y.val → x ≠ y →
      let w := doubleThreeCycle15 *
        (comparisonDoubleThreeCycle15 x y)⁻¹
      w ≠ 1 ∧ w.support.card ≤ 5 := by
  decide

end FiveTransitive.FiniteChecks

