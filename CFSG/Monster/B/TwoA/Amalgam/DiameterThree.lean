module

public import CFSG.Monster.B.TwoA.Amalgam.DiameterThreeCore
public import CFSG.Monster.B.TwoA.Amalgam.Exact3510

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA

theorem lblOrd_ne_one_of_dist_two
    {v w : CVert} (h : cgraph.dist v w = 2) :
    clabel v ≠ clabel w := by
  intro he
  have hsq : clabel w * clabel w = 1 := by
    rw [← sq, ← orderOf_clabel w, pow_orderOf_eq_one]
  rcases labelThree_or_labelFour_of_dist exists_rootModel h with h3 | h4
  · rcases h3.1 with h | h <;>
    · rw [lblOrd, he, hsq, orderOf_one] at h
      omega
  · rcases h4.1 with h | h <;>
    · rw [lblOrd, he, hsq, orderOf_one] at h
      omega

theorem clabel_injective_of
    (hdiam : ∀ v w : CVert, cgraph.dist v w ≤ 3)
    (hlab : ∀ v u : CVert, cgraph.dist v u = 3 → clabel v ≠ clabel u) :
    Function.Injective clabel := by
  intro v w he
  by_contra hne
  have hpos : 0 < cgraph.dist v w :=
    cgraph_connected.pos_dist_of_ne hne
  have hle := hdiam v w
  rcases (show cgraph.dist v w = 1 ∨ cgraph.dist v w = 2 ∨ cgraph.dist v w = 3 by omega) with
    h1 | h2 | h3
  · exact (clabel_adj (SimpleGraph.dist_eq_one_iff_adj.1 h1)).1 he
  · exact lblOrd_ne_one_of_dist_two h2 he
  · exact hlab v w h3 he

theorem commute_clabel_iff_of_injective
    (hinj : Function.Injective clabel) (v : CVert)
    (s : Shat) : (s : Dfull) * clabel v = clabel v * s ↔ cvMul v s = v := by
  constructor
  · intro h
    apply hinj
    rw [clabel_cvMul]
    calc ((s : Dfull))⁻¹ * clabel v * s = (s : Dfull)⁻¹ * (clabel v * s) := by group
      _ = (s : Dfull)⁻¹ * ((s : Dfull) * clabel v) := by rw [h]
      _ = clabel v := by group
  · intro h
    have h' := clabel_cvMul v s
    rw [h] at h'
    calc (s : Dfull) * clabel v = (s : Dfull) * ((s : Dfull)⁻¹ * clabel v * s) := by
          rw [← h']
      _ = clabel v * s := by group

theorem ncard_neighborSet
    (v : CVert) : (cgraph.neighborSet v).ncard = 3968055 := by
  obtain ⟨s, hs⟩ := cvMul_transitive cv0 v
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr (nbrShift hs), natCard_neighborSet_cv0_eq]

theorem ncard_sphereThree
    (v : CVert) : (sphereThree v).ncard = 2370830336 := by
  obtain ⟨w, hw⟩ := sphereThree_nonempty exists_rootModel v
  exact (native_order_three_common_neighbors_exact_3510.1 v w hw).2.2.2.1

theorem ncard_sphereFour
    (v : CVert) : (sphereFour v).ncard = 11174042880 :=
  native_coset_graph_order_four_common_neighbors.2.1 v

theorem vStabOrbit_eq_neighborSet
    {v w : CVert} (hw : w ∈ cgraph.neighborSet v) :
    vStabOrbit v w = cgraph.neighborSet v := by
  ext w'
  constructor
  · rintro ⟨s, hsv, rfl⟩
    have h := (cgraph_adj_cvMul v w s).2 hw
    rwa [hsv] at h
  · intro hw'
    obtain ⟨s, hs1, hs2⟩ := cvMul_edge_transitive hw hw'
    exact ⟨s, hs1, hs2⟩

theorem vStabOrbit_eq_sphereDistThree
    (htr : ∀ v u u' : CVert, u ∈ sphereDistThree v → u' ∈ sphereDistThree v →
      ∃ s : Shat, cvMul v s = v ∧ cvMul u s = u')
    {v u : CVert} (hu : u ∈ sphereDistThree v) : vStabOrbit v u = sphereDistThree v := by
  ext u'
  constructor
  · rintro ⟨s, hsv, rfl⟩
    have h := sphereDistThree_cvMul hu s
    rwa [hsv] at h
  · intro hu'
    exact htr v u u' hu hu'

theorem diameter_three_rank_five_of
    (hloc : DistThreeLocalOrbits)
    (hno : ∀ v w u : CVert, w ∈ sphereThree v → cgraph.Adj w u → cgraph.dist v u ≠ 3)
    (hne : ∀ v : CVert, (sphereDistThree v).Nonempty)
    (htr : ∀ v u u' : CVert, u ∈ sphereDistThree v → u' ∈ sphereDistThree v →
      ∃ s : Shat, cvMul v s = v ∧ cvMul u s = u')
    (hcard : ∀ v : CVert, (sphereDistThree v).ncard = 23113728) :
    (∀ v w : CVert, cgraph.dist v w ≤ 3) ∧ (∀ v : CVert, ∃ u, cgraph.dist v u = 3) ∧
    Nat.card CVert = 13571955000 ∧
    (∀ v : CVert,
      (∀ w : CVert, w = v ∨ w ∈ cgraph.neighborSet v ∨ w ∈ sphereThree v ∨ w ∈ sphereFour v ∨
        w ∈ sphereDistThree v) ∧
      (cgraph.neighborSet v).ncard = 3968055 ∧ (sphereThree v).ncard = 2370830336 ∧
      (sphereFour v).ncard = 11174042880 ∧ (sphereDistThree v).ncard = 23113728 ∧
      (∀ w ∈ cgraph.neighborSet v, vStabOrbit v w = cgraph.neighborSet v) ∧
      (∀ w ∈ sphereThree v, vStabOrbit v w = sphereThree v) ∧
      (∀ w ∈ sphereFour v, vStabOrbit v w = sphereFour v) ∧
      (∀ w ∈ sphereDistThree v, vStabOrbit v w = sphereDistThree v)) ∧
    ∀ v u : CVert, cgraph.dist v u = 3 →
      (cgraph.neighborSet u ∩ sphereFour v).ncard = 3898440 ∧
      (cgraph.neighborSet u ∩ sphereDistThree v).ncard = 69615 := by
  have hD := dist_le_three hloc hno
  have hcases : ∀ v w : CVert, w = v ∨ w ∈ cgraph.neighborSet v ∨ w ∈ sphereThree v ∨
      w ∈ sphereFour v ∨ w ∈ sphereDistThree v := by
    intro v w
    have hle := hD v w
    rcases (show cgraph.dist v w = 0 ∨ cgraph.dist v w = 1 ∨ cgraph.dist v w = 2 ∨
      cgraph.dist v w = 3 by omega) with h0 | h1 | h2 | h3
    · left
      by_contra hne'
      exact absurd h0 (cgraph_connected.pos_dist_of_ne (Ne.symm hne')).ne'
    · exact Or.inr (Or.inl (SimpleGraph.dist_eq_one_iff_adj.1 h1))
    · rcases labelThree_or_labelFour_of_dist exists_rootModel h2 with h | h
      · exact Or.inr (Or.inr (Or.inl ⟨h2, h.1⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h.1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h3)))
  have hfin : Finite CVert := short_F4_involution_coset_graph_data.1
  have hcard_univ : Nat.card CVert = 13571955000 := by
    obtain ⟨v⟩ : Nonempty CVert := ⟨cv0⟩
    have huniv : (Set.univ : Set CVert) =
        {v} ∪ cgraph.neighborSet v ∪ sphereThree v ∪ sphereFour v ∪ sphereDistThree v := by
      ext w
      simp only [Set.mem_univ, Set.mem_union, Set.mem_singleton_iff, true_iff]
      rcases hcases v w with h | h | h | h | h <;> tauto
    have hd1 : Disjoint ({v} : Set CVert) (cgraph.neighborSet v) := by
      rw [Set.disjoint_singleton_left]
      exact cgraph.irrefl
    have hd2 : Disjoint ({v} ∪ cgraph.neighborSet v) (sphereThree v) := by
      rw [Set.disjoint_union_left]
      refine ⟨Set.disjoint_singleton_left.2 fun h => ?_, Set.disjoint_left.2 fun w h1 h3 => ?_⟩
      · have := h.1
        rw [SimpleGraph.dist_self] at this
        omega
      · have := h3.1
        rw [SimpleGraph.dist_eq_one_iff_adj.2 h1] at this
        omega
    have hd3 : Disjoint ({v} ∪ cgraph.neighborSet v ∪ sphereThree v) (sphereFour v) := by
      rw [Set.disjoint_union_left, Set.disjoint_union_left]
      refine ⟨⟨Set.disjoint_singleton_left.2 fun h => ?_, Set.disjoint_left.2 fun w h1 h4 => ?_⟩,
        disjoint_sphereThree_sphereFour exists_rootModel v⟩
      · have := h.1
        rw [SimpleGraph.dist_self] at this
        omega
      · have := h4.1
        rw [SimpleGraph.dist_eq_one_iff_adj.2 h1] at this
        omega
    have hd4 : Disjoint ({v} ∪ cgraph.neighborSet v ∪ sphereThree v ∪ sphereFour v)
        (sphereDistThree v) := by
      rw [Set.disjoint_right]
      intro w hw hmem
      have h3 : cgraph.dist v w = 3 := hw
      rcases hmem with ((h | h) | h) | h
      · rw [Set.mem_singleton_iff.1 h, SimpleGraph.dist_self] at h3
        omega
      · rw [SimpleGraph.dist_eq_one_iff_adj.2 h] at h3
        omega
      · rw [h.1] at h3
        omega
      · rw [h.1] at h3
        omega
    rw [← Set.ncard_univ, huniv, Set.ncard_union_eq hd4 (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq hd3 (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq hd2 (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq hd1 (Set.toFinite _) (Set.toFinite _), Set.ncard_singleton,
      ncard_neighborSet, ncard_sphereThree, ncard_sphereFour, hcard]
  refine ⟨hD, fun v => hne v, hcard_univ, fun v => ⟨hcases v, ncard_neighborSet v,
    ncard_sphereThree v, ncard_sphereFour v, hcard v, fun w hw => vStabOrbit_eq_neighborSet hw,
    fun w hw => vStabOrbit_eq_sphereThree exists_rootModel hw,
    fun w hw => vStabOrbit_eq_sphereFour exists_rootModel hw,
    fun w hw => vStabOrbit_eq_sphereDistThree htr hw⟩, fun v u hvu => ?_⟩
  obtain ⟨-, -, -, -, hX, hY⟩ := hloc v u hvu
  refine ⟨hX, ?_⟩
  have heq : cgraph.neighborSet u ∩ sphereDistThree v = cgraph.neighborSet u \ sphereFour v := by
    ext y
    constructor
    · rintro ⟨hy, hy3⟩
      refine ⟨hy, fun h4 => ?_⟩
      have := h4.1
      rw [show cgraph.dist v y = 3 from hy3] at this
      omega
    · rintro ⟨hy, hy4⟩
      exact ⟨hy, (dist_of_adj_of_dist_three hloc hno hvu hy).2 hy4⟩
  rw [heq, hY]

theorem global_label_of
    (hdiam : ∀ v w : CVert, cgraph.dist v w ≤ 3)
    (hlab : ∀ v u : CVert, cgraph.dist v u = 3 → clabel v ≠ clabel u) :
    Function.Injective clabel ∧
    Set.range clabel = {x : Dfull | ∃ s : Shat, x = (s : Dfull)⁻¹ * Sp8.cQ * s} ∧
    (∀ (v : CVert) (s : Shat), clabel (cvMul v s) = (s : Dfull)⁻¹ * clabel v * s) ∧
    ∀ (v : CVert) (s : Shat), (s : Dfull) * clabel v = clabel v * s ↔ cvMul v s = v := by
  have hinj := clabel_injective_of hdiam hlab
  refine ⟨hinj, ?_, clabel_cvMul, commute_clabel_iff_of_injective hinj⟩
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨s, hs⟩ := cvMul_transitive cv0 v
    exact ⟨s, by rw [← hs, clabel_cvMul, clabel_cv0]⟩
  · rintro ⟨s, rfl⟩
    exact ⟨cvMul cv0 s, by rw [clabel_cvMul, clabel_cv0]⟩

end CFSG.Monster.B.TwoA.Amalgam
