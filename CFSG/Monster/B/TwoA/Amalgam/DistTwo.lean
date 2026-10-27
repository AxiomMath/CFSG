module

public import CFSG.Monster.B.TwoA.Amalgam.DistTwoCore
public import CFSG.Monster.B.TwoA.Amalgam.DistTwoInst
public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphValency

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA

theorem native_coset_graph_two_distance_two_orbits :
    {O : Set (CVert × CVert × CVert) | ∃ t, IsDistTwoPath t ∧ O = tripleOrbit t}.ncard = 2 ∧
    (∀ t t' : CVert × CVert × CVert, IsDistTwoPath t → IsDistTwoPath t' →
      (t' ∈ tripleOrbit t ↔ (LabelThree t.1 t.2.2 ↔ LabelThree t'.1 t'.2.2))) ∧
    (∀ v : CVert, {w | cgraph.dist v w = 2} = sphereThree v ∪ sphereFour v ∧
      Disjoint (sphereThree v) (sphereFour v) ∧
      {O | ∃ w, cgraph.dist v w = 2 ∧ O = vStabOrbit v w} = {sphereThree v, sphereFour v} ∧
      sphereThree v ≠ sphereFour v) ∧
    (∀ v w : CVert, cgraph.dist v w = 2 → ∀ u ∈ cgraph.commonNeighbors v w,
      ∀ u' ∈ cgraph.commonNeighbors v w,
        ∃ s : Shat, cvMul v s = v ∧ cvMul w s = w ∧ cvMul u s = u') ∧
    ∃ μ₃ μ₄ : ℕ, 0 < μ₃ ∧ 0 < μ₄ ∧
      (∀ v w : CVert, w ∈ sphereThree v → (cgraph.commonNeighbors v w).ncard = μ₃) ∧
      (∀ v w : CVert, w ∈ sphereFour v → (cgraph.commonNeighbors v w).ncard = μ₄) ∧
      ∀ v : CVert, (sphereThree v).ncard * μ₃ = 3968055 * 2097152 ∧
        (sphereFour v).ncard * μ₄ = 3968055 * 1824768 := by
  have hM := exists_rootModel
  obtain ⟨t₃, ht₃, h₃⟩ := exists_path_labelThree hM
  obtain ⟨t₄, ht₄, h₄⟩ := exists_path_labelFour hM
  have hμ₃ : ∀ v w : CVert, w ∈ sphereThree v →
      (cgraph.commonNeighbors v w).ncard = (cgraph.commonNeighbors t₃.1 t₃.2.2).ncard :=
    fun _ _ hw => ncard_commonNeighbors_eq hM hw.1 ht₃.2.2 (iff_of_true hw.2 h₃)
  have hμ₄ : ∀ v w : CVert, w ∈ sphereFour v →
      (cgraph.commonNeighbors v w).ncard = (cgraph.commonNeighbors t₄.1 t₄.2.2).ncard :=
    fun _ _ hw => ncard_commonNeighbors_eq hM hw.1 ht₄.2.2
      (iff_of_false ((labelFour_iff_not_labelThree hM hw.1).1 hw.2) h₄)
  exact ⟨ncard_setOf_tripleOrbit hM, fun _ _ ht ht' => mem_tripleOrbit_iff hM ht ht',
    fun v => ⟨setOf_dist_eq_two_eq_union hM v, disjoint_sphereThree_sphereFour hM v,
      setOf_vStabOrbit_eq hM v, sphereThree_ne_sphereFour hM v⟩,
    fun _ _ hd _ hu _ hu' => exists_smul_eq_commonNeighbor hM hd hu hu', _, _,
    ncard_commonNeighbors_pos ht₃.2.2, ncard_commonNeighbors_pos ht₄.2.2, hμ₃, hμ₄,
    fun v => ⟨ncard_sphereThree_mul hM natCard_neighborSet_cv0_eq v (hμ₃ v),
      ncard_sphereFour_mul hM natCard_neighborSet_cv0_eq v (hμ₄ v)⟩⟩

end CFSG.Monster.B.TwoA.Amalgam
