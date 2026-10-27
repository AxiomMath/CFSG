module

public import CFSG.Monster.B.TwoA.Amalgam.NativeChain

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA

@[expose] def rankFiveOrbit
    (v : CVert) : Fin 5 → Set CVert :=
  ![{v}, cgraph.neighborSet v, sphereThree v, sphereFour v, sphereDistThree v]

@[expose] def rankFiveMatrix : Matrix (Fin 5) (Fin 5) ℕ :=
  !![0, 3968055, 0, 0, 0; 1, 46134, 2097152, 1824768, 0; 0, 3510, 837135, 3127410, 0;
    0, 648, 663552, 3295791, 8064; 0, 0, 0, 3898440, 69615]

theorem dist_of_mem_rankFiveOrbit
    {v w : CVert} {i : Fin 5} (hw : w ∈ rankFiveOrbit v i) :
    cgraph.dist v w = (![0, 1, 2, 2, 3] : Fin 5 → ℕ) i := by
  fin_cases i
  · have hwv : w = v := hw
    exact show cgraph.dist v w = 0 by rw [hwv, SimpleGraph.dist_self]
  · exact SimpleGraph.dist_eq_one_iff_adj.2 hw
  · exact (show w ∈ sphereThree v from hw).1
  · exact (show w ∈ sphereFour v from hw).1
  · exact (show w ∈ sphereDistThree v from hw)

theorem existsUnique_mem_rankFiveOrbit
    (hD : ∀ v w : CVert, cgraph.dist v w ≤ 3) (v w : CVert) :
    ∃! i, w ∈ rankFiveOrbit v i := by
  have hex : ∃ i, w ∈ rankFiveOrbit v i := by
    have hle := hD v w
    rcases (show cgraph.dist v w = 0 ∨ cgraph.dist v w = 1 ∨ cgraph.dist v w = 2 ∨
      cgraph.dist v w = 3 by omega) with h | h | h | h
    · exact ⟨0, show w = v from ((cgraph_connected.preconnected v w).dist_eq_zero_iff.1 h).symm⟩
    · exact ⟨1, SimpleGraph.dist_eq_one_iff_adj.1 h⟩
    · rcases labelThree_or_labelFour_of_dist exists_rootModel h with h' | h'
      · exact ⟨2, show w ∈ sphereThree v from ⟨h, h'.1⟩⟩
      · exact ⟨3, show w ∈ sphereFour v from ⟨h, h'.1⟩⟩
    · exact ⟨4, show w ∈ sphereDistThree v from h⟩
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, hi, fun j hj => ?_⟩
  have key : ∀ i j : Fin 5, (![0, 1, 2, 2, 3] : Fin 5 → ℕ) i = ![0, 1, 2, 2, 3] j →
      i = j ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) := by decide
  have h34 := disjoint_sphereThree_sphereFour exists_rootModel v
  rcases key j i ((dist_of_mem_rankFiveOrbit hj).symm.trans (dist_of_mem_rankFiveOrbit hi))
    with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h
  · exact absurd hi (Set.disjoint_left.1 h34 hj)
  · exact absurd hj (Set.disjoint_left.1 h34 hi)

theorem vStabOrbit_eq_rankFiveOrbit
    (htr : ∀ v u u' : CVert, u ∈ sphereDistThree v → u' ∈ sphereDistThree v →
      ∃ s : Shat, cvMul v s = v ∧ cvMul u s = u')
    {v w : CVert} {i : Fin 5} (hw : w ∈ rankFiveOrbit v i) :
    vStabOrbit v w = rankFiveOrbit v i := by
  fin_cases i
  · have hwv : w = v := hw
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [hwv]
      exact hs
    · intro hx
      have hxv : x = v := hx
      exact ⟨1, cvMul_one v, by rw [cvMul_one, hwv, hxv]⟩
  · exact vStabOrbit_eq_neighborSet hw
  · exact vStabOrbit_eq_sphereThree exists_rootModel hw
  · exact vStabOrbit_eq_sphereFour exists_rootModel hw
  · exact vStabOrbit_eq_sphereDistThree htr hw

private theorem ncard_eq_sum_ncard_inter {α : Type*} [Finite α] {n : ℕ} {O : Fin n → Set α}
    (hO : ∀ x, ∃! i, x ∈ O i) (s : Set α) : s.ncard = ∑ i, (s ∩ O i).ncard := by
  have hs : s = ⋃ i, s ∩ O i := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun hx => (hO x).exists.imp fun _ hi => ⟨hx, hi⟩, fun ⟨_, hx, _⟩ => hx⟩
  have hd : Pairwise (Function.onFun Disjoint fun i => s ∩ O i) := fun i j hij =>
    Set.disjoint_left.2 fun x hi hj => hij ((hO x).unique hi.2 hj.2)
  calc s.ncard = (⋃ i, s ∩ O i).ncard := by rw [← hs]
    _ = ∑ i, (s ∩ O i).ncard := by
      rw [Set.ncard_iUnion_of_finite (fun _ => Set.toFinite _) hd, finsum_eq_sum_of_fintype]

theorem sum_ncard_inter_rankFiveOrbit
    (hD : ∀ v w : CVert, cgraph.dist v w ≤ 3) (v w : CVert) :
    (cgraph.neighborSet w ∩ {v}).ncard + (cgraph.neighborSet w ∩ cgraph.neighborSet v).ncard +
      (cgraph.neighborSet w ∩ sphereThree v).ncard +
      (cgraph.neighborSet w ∩ sphereFour v).ncard +
      (cgraph.neighborSet w ∩ sphereDistThree v).ncard = 3968055 := by
  have : Finite CVert := short_F4_involution_coset_graph_data.1
  have h := ncard_eq_sum_ncard_inter (existsUnique_mem_rankFiveOrbit hD v) (cgraph.neighborSet w)
  rw [Fin.sum_univ_five, ncard_neighborSet] at h
  exact h.symm

private theorem ncard_inter_eq_zero
    {s t : Set CVert} (h : ∀ z ∈ s, z ∈ t → False) :
    (s ∩ t).ncard = 0 := by
  have : Finite CVert := short_F4_involution_coset_graph_data.1
  exact (Set.ncard_eq_zero (Set.toFinite _)).2
    (Set.eq_empty_of_subset_empty fun z hz => h z hz.1 hz.2)

private theorem dist_le_of_adj
    {v w z : CVert} (h : cgraph.Adj w z) :
    cgraph.dist v z ≤ cgraph.dist v w + 1 ∧ cgraph.dist v w ≤ cgraph.dist v z + 1 := by
  have h1 := cgraph_connected.dist_triangle (u := v) (v := w) (w := z)
  have h2 := cgraph_connected.dist_triangle (u := v) (v := z) (w := w)
  rw [SimpleGraph.dist_eq_one_iff_adj.2 h] at h1
  rw [SimpleGraph.dist_eq_one_iff_adj.2 h.symm] at h2
  exact ⟨h1, h2⟩

theorem rankFive_row_zero
    (v : CVert) :
    (cgraph.neighborSet v ∩ {v}).ncard = 0 ∧
      (cgraph.neighborSet v ∩ cgraph.neighborSet v).ncard = 3968055 ∧
      (cgraph.neighborSet v ∩ sphereThree v).ncard = 0 ∧
      (cgraph.neighborSet v ∩ sphereFour v).ncard = 0 ∧
      (cgraph.neighborSet v ∩ sphereDistThree v).ncard = 0 := by
  have hd : ∀ z ∈ cgraph.neighborSet v, cgraph.dist v z = 1 := fun z hz =>
    SimpleGraph.dist_eq_one_iff_adj.2 hz
  refine ⟨ncard_inter_eq_zero fun z hz hzv => ?_, by rw [Set.inter_self, ncard_neighborSet],
    ncard_inter_eq_zero fun z hz h => ?_, ncard_inter_eq_zero fun z hz h => ?_,
    ncard_inter_eq_zero fun z hz h => ?_⟩
  · have hzv' : z = v := hzv
    rw [hzv'] at hz
    exact cgraph.irrefl hz
  · have := (show z ∈ sphereThree v from h).1
    have := hd z hz
    omega
  · have := (show z ∈ sphereFour v from h).1
    have := hd z hz
    omega
  · have : cgraph.dist v z = 3 := h
    have := hd z hz
    omega

theorem rankFive_row_one
    (hD : ∀ v w : CVert, cgraph.dist v w ≤ 3) {v w : CVert}
    (hw : w ∈ cgraph.neighborSet v) :
    (cgraph.neighborSet w ∩ {v}).ncard = 1 ∧
      (cgraph.neighborSet w ∩ cgraph.neighborSet v).ncard = 46134 ∧
      (cgraph.neighborSet w ∩ sphereThree v).ncard = 2097152 ∧
      (cgraph.neighborSet w ∩ sphereFour v).ncard = 1824768 ∧
      (cgraph.neighborSet w ∩ sphereDistThree v).ncard = 0 := by
  have h0 : (cgraph.neighborSet w ∩ {v}).ncard = 1 := by
    have hv : v ∈ cgraph.neighborSet w := cgraph.adj_symm hw
    rw [Set.inter_eq_right.2 (Set.singleton_subset_iff.2 hv), Set.ncard_singleton]
  have h2 : (cgraph.neighborSet w ∩ sphereThree v).ncard = 2097152 := by
    rw [← Nat.card_coe_set_eq]
    exact natCard_adj_sphereThree exists_rootModel hw
  have h3 : (cgraph.neighborSet w ∩ sphereFour v).ncard = 1824768 := by
    rw [← Nat.card_coe_set_eq]
    exact natCard_adj_sphereFour exists_rootModel hw
  have h4 : (cgraph.neighborSet w ∩ sphereDistThree v).ncard = 0 :=
    ncard_inter_eq_zero fun z hz h => by
      have := (dist_le_of_adj (v := v) hz).1
      have : cgraph.dist v w = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hw
      have : cgraph.dist v z = 3 := h
      omega
  have := sum_ncard_inter_rankFiveOrbit hD v w
  exact ⟨h0, by omega, h2, h3, h4⟩

theorem rankFive_row_two
    (hamb : AmbientRootOrbitsHyp) {v w : CVert} (hw : w ∈ sphereThree v) :
    (cgraph.neighborSet w ∩ {v}).ncard = 0 ∧
      (cgraph.neighborSet w ∩ cgraph.neighborSet v).ncard = 3510 ∧
      (cgraph.neighborSet w ∩ sphereThree v).ncard = 837135 ∧
      (cgraph.neighborSet w ∩ sphereFour v).ncard = 3127410 ∧
      (cgraph.neighborSet w ∩ sphereDistThree v).ncard = 0 := by
  obtain ⟨hU, -, -, -, -, hcard, -, -, -, -, -, hno⟩ :=
    type_three_neighborhood_global_distance_bound_of hamb hw
  obtain ⟨h23, h4⟩ :=
    (fischer_remaining_orbit_global_types_of hamb native_maximal_clique_ncard).1 v w hw
  have h34 := disjoint_sphereThree_sphereFour exists_rootModel v
  have h0 : (cgraph.neighborSet w ∩ {v}).ncard = 0 := ncard_inter_eq_zero fun z hz hzv => by
    have hzv' : z = v := hzv
    rw [hzv'] at hz
    have h := hw.1
    rw [SimpleGraph.dist_eq_one_iff_adj.2 (cgraph.adj_symm hz)] at h
    omega
  have h1 : (cgraph.neighborSet w ∩ cgraph.neighborSet v).ncard = 3510 := by
    rw [Set.inter_comm]
    exact (native_order_three_common_neighbors_exact_3510.1 v w hw).2.2.1
  have h3 : (cgraph.neighborSet w ∩ sphereFour v).ncard = 3127410 := by
    have e : cgraph.neighborSet w ∩ sphereFour v = outerOrbit v w 3127410 := by
      ext z
      constructor
      · rintro ⟨hz, hz4⟩
        have hzM : z ∉ cgraph.commonNeighbors v w := fun hm => by
          have h := hz4.1
          rw [SimpleGraph.dist_eq_one_iff_adj.2 hm.1] at h
          omega
        have hz' : z ∈ cgraph.neighborSet w \ cgraph.commonNeighbors v w := ⟨hz, hzM⟩
        rw [hU] at hz'
        rcases hz' with h | h
        · exact absurd hz4 (Set.disjoint_left.1 h34 (h23 h))
        · exact h
      · intro hz
        have hz' : z ∈ cgraph.neighborSet w \ cgraph.commonNeighbors v w := by
          rw [hU]
          exact Or.inr hz
        exact ⟨hz'.1, h4 hz⟩
    rw [e, hcard]
  have h5 : (cgraph.neighborSet w ∩ sphereDistThree v).ncard = 0 :=
    ncard_inter_eq_zero fun z hz h => hno z hz h
  have := sum_ncard_inter_rankFiveOrbit (diameter_three_rank_five_of_ambient hamb).1 v w
  exact ⟨h0, h1, by omega, h3, h5⟩

theorem rankFive_row_three
    (hamb : AmbientRootOrbitsHyp) {v w : CVert} (hw : w ∈ sphereFour v) :
    (cgraph.neighborSet w ∩ {v}).ncard = 0 ∧
      (cgraph.neighborSet w ∩ cgraph.neighborSet v).ncard = 648 ∧
      (cgraph.neighborSet w ∩ sphereThree v).ncard = 663552 ∧
      (cgraph.neighborSet w ∩ sphereFour v).ncard = 3295791 ∧
      (cgraph.neighborSet w ∩ sphereDistThree v).ncard = 8064 := by
  have h0 : (cgraph.neighborSet w ∩ {v}).ncard = 0 := ncard_inter_eq_zero fun z hz hzv => by
    have hzv' : z = v := hzv
    rw [hzv'] at hz
    have h := hw.1
    rw [SimpleGraph.dist_eq_one_iff_adj.2 (cgraph.adj_symm hz)] at h
    omega
  have h1 : (cgraph.neighborSet w ∩ cgraph.neighborSet v).ncard = 648 := by
    rw [Set.inter_comm]
    exact (native_coset_graph_order_four_common_neighbors.1 v w hw).2.1
  have h2 : (cgraph.neighborSet w ∩ sphereThree v).ncard = 663552 := by
    have hv : v ∈ sphereFour w := mem_sphereFour_comm.1 hw
    obtain ⟨-, Ω, -, -, -, -, -, -, -, hsub, hpart, horb, hcard, -⟩ :=
      native_type_four_pair_eight_neighborhood_orbits w v hv
    rw [(fischer_remaining_orbit_global_types_of hamb native_maximal_clique_ncard).2 w v hv Ω
      hsub hpart horb hcard, hcard 2]
    rfl
  have h4 := ((distThreePaths_of_ambient hamb).2.1 v w hw).1
  have := sum_ncard_inter_rankFiveOrbit (diameter_three_rank_five_of_ambient hamb).1 v w
  exact ⟨h0, h1, h2, by omega, h4⟩

theorem rankFive_row_four
    (hamb : AmbientRootOrbitsHyp) {v u : CVert}
    (hu : u ∈ sphereDistThree v) :
    (cgraph.neighborSet u ∩ {v}).ncard = 0 ∧
      (cgraph.neighborSet u ∩ cgraph.neighborSet v).ncard = 0 ∧
      (cgraph.neighborSet u ∩ sphereThree v).ncard = 0 ∧
      (cgraph.neighborSet u ∩ sphereFour v).ncard = 3898440 ∧
      (cgraph.neighborSet u ∩ sphereDistThree v).ncard = 69615 := by
  have hu3 : cgraph.dist v u = 3 := hu
  have h0 : (cgraph.neighborSet u ∩ {v}).ncard = 0 := ncard_inter_eq_zero fun z hz hzv => by
    have hzv' : z = v := hzv
    rw [hzv'] at hz
    rw [SimpleGraph.dist_eq_one_iff_adj.2 (cgraph.adj_symm hz)] at hu3
    omega
  have h1 : (cgraph.neighborSet u ∩ cgraph.neighborSet v).ncard = 0 :=
    ncard_inter_eq_zero fun z hz h => by
      have := (dist_le_of_adj (v := v) (cgraph.adj_symm hz)).1
      have : cgraph.dist v z = 1 := SimpleGraph.dist_eq_one_iff_adj.2 h
      omega
  have h2 : (cgraph.neighborSet u ∩ sphereThree v).ncard = 0 :=
    ncard_inter_eq_zero fun z hz h => GSide.hno_of_ambient hamb v z u h (cgraph.adj_symm hz) hu3
  obtain ⟨h3, h4⟩ := (diameter_three_rank_five_of_ambient hamb).2.2.2.2 v u hu3
  exact ⟨h0, h1, h2, h3, h4⟩

theorem native_rank_five_exact_neighbor_matrix_of_ambient
    (hamb : AmbientRootOrbitsHyp) :
    (∀ v w : CVert, ∃! i, w ∈ rankFiveOrbit v i) ∧
    (∀ (v : CVert) (i : Fin 5), ∀ w ∈ rankFiveOrbit v i, vStabOrbit v w = rankFiveOrbit v i) ∧
    ∀ (v : CVert) (i j : Fin 5), ∀ w ∈ rankFiveOrbit v i,
      (cgraph.neighborSet w ∩ rankFiveOrbit v j).ncard = rankFiveMatrix i j := by
  have hD := (diameter_three_rank_five_of_ambient hamb).1
  refine ⟨existsUnique_mem_rankFiveOrbit hD,
    fun v i w hw => vStabOrbit_eq_rankFiveOrbit (distThreePaths_of_ambient hamb).1 hw,
    fun v i j w hw => ?_⟩
  fin_cases i
  · have hwv : w = v := hw
    rw [hwv]
    obtain ⟨a, b, c, d, e⟩ := rankFive_row_zero v
    fin_cases j
    exacts [a, b, c, d, e]
  · obtain ⟨a, b, c, d, e⟩ := rankFive_row_one hD hw
    fin_cases j
    exacts [a, b, c, d, e]
  · obtain ⟨a, b, c, d, e⟩ := rankFive_row_two hamb hw
    fin_cases j
    exacts [a, b, c, d, e]
  · obtain ⟨a, b, c, d, e⟩ := rankFive_row_three hamb hw
    fin_cases j
    exacts [a, b, c, d, e]
  · obtain ⟨a, b, c, d, e⟩ := rankFive_row_four hamb hw
    fin_cases j
    exacts [a, b, c, d, e]

end CFSG.Monster.B.TwoA.Amalgam
