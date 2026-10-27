module

public import CFSG.Monster.B.Generic.RankFourSpectralData
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeDefs
public import CFSG.Monster.B.TwoA.Amalgam.GlobalTypeCore
public import CFSG.Monster.B.TwoA.Amalgam.EightOrbits
public import CFSG.Monster.B.TwoA.Amalgam.Exact3510

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.Generic

private theorem exists_adj_dist_pred
    {v y : CVert} {n : ℕ} (h : cgraph.dist v y = n + 1) :
    ∃ y', cgraph.Adj y' y ∧ cgraph.dist v y' = n := by
  obtain ⟨p, hp⟩ := cgraph_connected.exists_walk_length_eq_dist y v
  rw [SimpleGraph.dist_comm, h] at hp
  cases p with
  | nil => simp at hp
  | @cons _ z _ hyz q =>
    refine ⟨z, hyz.symm, le_antisymm ?_ ?_⟩
    · rw [SimpleGraph.Walk.length_cons] at hp
      rw [SimpleGraph.dist_comm]
      have := SimpleGraph.dist_le q
      omega
    · have h2 := cgraph_connected.dist_triangle (u := v) (v := z) (w := y)
      rw [h, SimpleGraph.dist_eq_one_iff_adj.2 hyz.symm] at h2
      omega

private theorem exists_dist_eq_three
    {v y : CVert} (h : 3 ≤ cgraph.dist v y) :
    ∃ z, cgraph.dist v z = 3 := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le h
  induction n generalizing y with
  | zero => exact ⟨y, hn⟩
  | succ n ih =>
    obtain ⟨y', -, hy'⟩ := exists_adj_dist_pred (v := v) (y := y) (n := 3 + n) (by omega)
    exact ih (by omega) hy'

private theorem mem_sphereFour_symm
    {v w : CVert} : w ∈ sphereFour v ↔ v ∈ sphereFour w := by
  have hord : ∀ a b : CVert, LabelFour a b → LabelFour b a := by
    intro a b h
    have e : lblOrd b a = lblOrd a b := by
      rw [lblOrd, lblOrd, ← MulEquiv.orderOf_eq (MulAut.conj (clabel a)) (clabel b * clabel a),
        MulAut.conj_apply]
      congr 1
      group
    rw [LabelFour, e]
    exact h
  exact ⟨fun h => ⟨SimpleGraph.dist_comm.trans h.1, hord v w h.2⟩,
    fun h => ⟨SimpleGraph.dist_comm.trans h.1, hord w v h.2⟩⟩

private theorem ncard_neighborSet_eq_valency
    (y : CVert) :
    (cgraph.neighborSet y).ncard = 3968055 := by
  rw [← Nat.card_coe_set_eq, natCard_neighborSet_eq, natCard_neighborSet_cv0_eq]

private theorem ncard_eq_of_four {α : Type*} [Finite α] {s a b c d : Set α}
    (hs : s = a ∪ b ∪ c ∪ d) (hab : Disjoint a b) (hac : Disjoint a c) (had : Disjoint a d)
    (hbc : Disjoint b c) (hbd : Disjoint b d) (hcd : Disjoint c d) :
    s.ncard = a.ncard + b.ncard + c.ncard + d.ncard := by
  rw [hs, Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨Set.disjoint_union_left.2 ⟨had, hbd⟩,
      hcd⟩) (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨hac, hbc⟩) (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq hab (Set.toFinite _) (Set.toFinite _)]

private theorem sum_ncard_adj_cells
    {v : CVert}
    (hcase : ∀ y, y = v ∨ y ∈ cgraph.neighborSet v ∨ y ∈ sphereThree v ∨ y ∈ sphereFour v)
    (y : CVert) :
    {z | cgraph.Adj y z ∧ z ∈ ({v} : Set CVert)}.ncard +
      {z | cgraph.Adj y z ∧ z ∈ cgraph.neighborSet v}.ncard +
      {z | cgraph.Adj y z ∧ z ∈ sphereThree v}.ncard +
      {z | cgraph.Adj y z ∧ z ∈ sphereFour v}.ncard = 3968055 := by
  have : Finite CVert := short_F4_involution_coset_graph_data.1
  have h34 := disjoint_sphereThree_sphereFour exists_rootModel v
  rw [← ncard_neighborSet_eq_valency y]
  refine (ncard_eq_of_four ?_ ?_ ?_ ?_ ?_ ?_ ?_).symm
  · ext z
    refine ⟨fun hz => ?_, ?_⟩
    · rcases hcase z with h | h | h | h
      · exact Or.inl (Or.inl (Or.inl ⟨hz, h⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨hz, h⟩))
      · exact Or.inl (Or.inr ⟨hz, h⟩)
      · exact Or.inr ⟨hz, h⟩
    · rintro (((h | h) | h) | h) <;> exact h.1
  · refine Set.disjoint_left.2 fun z h1 h2 => ?_
    have h1' : z = v := h1.2
    subst h1'
    exact cgraph.irrefl h2.2
  · refine Set.disjoint_left.2 fun z h1 h2 => ?_
    have h1' : z = v := h1.2
    subst h1'
    have h := h2.2.1
    rw [SimpleGraph.dist_self] at h
    omega
  · refine Set.disjoint_left.2 fun z h1 h2 => ?_
    have h1' : z = v := h1.2
    subst h1'
    have h := h2.2.1
    rw [SimpleGraph.dist_self] at h
    omega
  · refine Set.disjoint_left.2 fun z h1 h2 => ?_
    have h := h2.2.1
    rw [SimpleGraph.dist_eq_one_iff_adj.2 h1.2] at h
    omega
  · refine Set.disjoint_left.2 fun z h1 h2 => ?_
    have h := h2.2.1
    rw [SimpleGraph.dist_eq_one_iff_adj.2 h1.2] at h
    omega
  · exact Set.disjoint_left.2 fun z h1 h2 => Set.disjoint_left.1 h34 h1.2 h2.2

theorem native_graph_distance_three_exists_spectral_obstruction_of
    (hout : ∀ v w : CVert, w ∈ sphereThree v →
      cgraph.neighborSet w \ cgraph.commonNeighbors v w =
          outerOrbit v w 142155 ∪ outerOrbit v w 694980 ∪ outerOrbit v w 3127410 ∧
        (outerOrbit v w 142155).ncard = 142155 ∧ (outerOrbit v w 694980).ncard = 694980 ∧
        (outerOrbit v w 3127410).ncard = 3127410)
    (hglob : (∀ v w : CVert, w ∈ sphereThree v →
        outerOrbit v w 142155 ∪ outerOrbit v w 694980 ⊆ sphereThree v ∧
          outerOrbit v w 3127410 ⊆ sphereFour v) ∧
      ∀ v w : CVert, w ∈ sphereFour v → ∀ Ω : Fin 8 → Set CVert,
        (∀ i, Ω i ⊆ cgraph.neighborSet v) → (∀ u ∈ cgraph.neighborSet v, ∃! i, u ∈ Ω i) →
        (∀ i, ∀ u ∈ Ω i, {x | ∃ y ∈ vStab v ⊓ vStab w, cvMul u y = x} = Ω i) →
        (∀ i, (Ω i).ncard = ![648, 8064, 663552, 1, 1134, 36288, 1161216, 2097152] i) →
        cgraph.neighborSet v ∩ sphereThree w = Ω 2) :
    (∀ v : CVert, (sphereDistThree v).Nonempty) ∧ 3 ≤ cgraph.diam := by
  have hfin : Finite CVert := short_F4_involution_coset_graph_data.1
  have hmain : ∀ v : CVert, (sphereDistThree v).Nonempty := by
    intro v
    by_contra hemp
    have hno : ∀ z, cgraph.dist v z ≠ 3 := fun z hz => hemp ⟨z, hz⟩
    have h34 := disjoint_sphereThree_sphereFour exists_rootModel v
    have hcase : ∀ y, y = v ∨ y ∈ cgraph.neighborSet v ∨ y ∈ sphereThree v ∨
        y ∈ sphereFour v := by
      intro y
      have hle : cgraph.dist v y ≤ 2 := by
        by_contra h
        obtain ⟨z, hz⟩ := exists_dist_eq_three (v := v) (y := y) (by omega)
        exact hno z hz
      rcases (show cgraph.dist v y = 0 ∨ cgraph.dist v y = 1 ∨ cgraph.dist v y = 2 by omega)
        with h | h | h
      · exact Or.inl ((cgraph_connected.preconnected v y).dist_eq_zero_iff.1 h).symm
      · exact Or.inr (Or.inl (SimpleGraph.dist_eq_one_iff_adj.1 h))
      · rcases labelThree_or_labelFour_of_dist exists_rootModel h with h' | h'
        · exact Or.inr (Or.inr (Or.inl ⟨h, h'.1⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨h, h'.1⟩))
    have hsum := sum_ncard_adj_cells hcase
    have hzero : ∀ {s : Set CVert}, (∀ z, z ∉ s) → s.ncard = 0 := fun h =>
      (Set.ncard_eq_zero (Set.toFinite _)).2 (Set.eq_empty_of_subset_empty fun z hz => h z hz)
    have hrow0 : {z | cgraph.Adj v z ∧ z ∈ ({v} : Set CVert)}.ncard = 0 ∧
        {z | cgraph.Adj v z ∧ z ∈ cgraph.neighborSet v}.ncard = 3968055 ∧
        {z | cgraph.Adj v z ∧ z ∈ sphereThree v}.ncard = 0 ∧
        {z | cgraph.Adj v z ∧ z ∈ sphereFour v}.ncard = 0 := by
      have h0 : {z | cgraph.Adj v z ∧ z ∈ ({v} : Set CVert)}.ncard = 0 := hzero fun z hz => by
        have hzv : z = v := hz.2
        subst hzv
        exact cgraph.irrefl hz.1
      have h2 : {z | cgraph.Adj v z ∧ z ∈ sphereThree v}.ncard = 0 := hzero fun z hz => by
        have h := hz.2.1
        rw [SimpleGraph.dist_eq_one_iff_adj.2 hz.1] at h
        omega
      have h3 : {z | cgraph.Adj v z ∧ z ∈ sphereFour v}.ncard = 0 := hzero fun z hz => by
        have h := hz.2.1
        rw [SimpleGraph.dist_eq_one_iff_adj.2 hz.1] at h
        omega
      have := hsum v
      exact ⟨h0, by omega, h2, h3⟩
    have hrow1 : ∀ y ∈ cgraph.neighborSet v,
        {z | cgraph.Adj y z ∧ z ∈ ({v} : Set CVert)}.ncard = 1 ∧
        {z | cgraph.Adj y z ∧ z ∈ cgraph.neighborSet v}.ncard = 46134 ∧
        {z | cgraph.Adj y z ∧ z ∈ sphereThree v}.ncard = 2097152 ∧
        {z | cgraph.Adj y z ∧ z ∈ sphereFour v}.ncard = 1824768 := by
      intro y hy
      have h0 : {z | cgraph.Adj y z ∧ z ∈ ({v} : Set CVert)}.ncard = 1 := by
        have e : {z | cgraph.Adj y z ∧ z ∈ ({v} : Set CVert)} = {v} := by
          ext z
          refine ⟨fun hz => hz.2, fun hz => ?_⟩
          have hzv : z = v := hz
          subst hzv
          exact ⟨cgraph.adj_symm hy, rfl⟩
        rw [e, Set.ncard_singleton]
      have h2 : {z | cgraph.Adj y z ∧ z ∈ sphereThree v}.ncard = 2097152 := by
        rw [← Nat.card_coe_set_eq]
        exact natCard_adj_sphereThree exists_rootModel hy
      have h3 : {z | cgraph.Adj y z ∧ z ∈ sphereFour v}.ncard = 1824768 := by
        rw [← Nat.card_coe_set_eq]
        exact natCard_adj_sphereFour exists_rootModel hy
      have := hsum y
      exact ⟨h0, by omega, h2, h3⟩
    have hrow2 : ∀ y ∈ sphereThree v,
        {z | cgraph.Adj y z ∧ z ∈ ({v} : Set CVert)}.ncard = 0 ∧
        {z | cgraph.Adj y z ∧ z ∈ cgraph.neighborSet v}.ncard = 3510 ∧
        {z | cgraph.Adj y z ∧ z ∈ sphereThree v}.ncard = 837135 ∧
        {z | cgraph.Adj y z ∧ z ∈ sphereFour v}.ncard = 3127410 := by
      intro y hy
      have h0 : {z | cgraph.Adj y z ∧ z ∈ ({v} : Set CVert)}.ncard = 0 := hzero fun z hz => by
        have hzv : z = v := hz.2
        subst hzv
        have h := hy.1
        rw [SimpleGraph.dist_eq_one_iff_adj.2 (cgraph.adj_symm hz.1)] at h
        omega
      have h1 : {z | cgraph.Adj y z ∧ z ∈ cgraph.neighborSet v}.ncard = 3510 := by
        have e : {z | cgraph.Adj y z ∧ z ∈ cgraph.neighborSet v} =
            cgraph.commonNeighbors v y := by
          ext z
          rw [SimpleGraph.mem_commonNeighbors]
          exact and_comm
        rw [e]
        exact (native_order_three_common_neighbors_exact_3510.1 v y hy).2.2.1
      have h3 : {z | cgraph.Adj y z ∧ z ∈ sphereFour v}.ncard = 3127410 := by
        obtain ⟨hU, -, -, hcard⟩ := hout v y hy
        obtain ⟨h23, h4⟩ := hglob.1 v y hy
        have e : {z | cgraph.Adj y z ∧ z ∈ sphereFour v} = outerOrbit v y 3127410 := by
          ext z
          constructor
          · rintro ⟨hz, hz4⟩
            have hzM : z ∉ cgraph.commonNeighbors v y := fun hm => by
              have h := hz4.1
              rw [SimpleGraph.dist_eq_one_iff_adj.2 hm.1] at h
              omega
            have hz' : z ∈ cgraph.neighborSet y \ cgraph.commonNeighbors v y := ⟨hz, hzM⟩
            rw [hU] at hz'
            rcases hz' with h | h
            · exact absurd hz4 (Set.disjoint_left.1 h34 (h23 h))
            · exact h
          · intro hz
            have hz' : z ∈ cgraph.neighborSet y \ cgraph.commonNeighbors v y := by
              rw [hU]
              exact Or.inr hz
            exact ⟨hz'.1, h4 hz⟩
        rw [e, hcard]
      have := hsum y
      exact ⟨h0, h1, by omega, h3⟩
    have hrow3 : ∀ y ∈ sphereFour v,
        {z | cgraph.Adj y z ∧ z ∈ ({v} : Set CVert)}.ncard = 0 ∧
        {z | cgraph.Adj y z ∧ z ∈ cgraph.neighborSet v}.ncard = 648 ∧
        {z | cgraph.Adj y z ∧ z ∈ sphereThree v}.ncard = 663552 ∧
        {z | cgraph.Adj y z ∧ z ∈ sphereFour v}.ncard = 3303855 := by
      intro y hy
      have h0 : {z | cgraph.Adj y z ∧ z ∈ ({v} : Set CVert)}.ncard = 0 := hzero fun z hz => by
        have hzv : z = v := hz.2
        subst hzv
        have h := hy.1
        rw [SimpleGraph.dist_eq_one_iff_adj.2 (cgraph.adj_symm hz.1)] at h
        omega
      have h1 : {z | cgraph.Adj y z ∧ z ∈ cgraph.neighborSet v}.ncard = 648 := by
        have e : {z | cgraph.Adj y z ∧ z ∈ cgraph.neighborSet v} =
            cgraph.commonNeighbors v y := by
          ext z
          rw [SimpleGraph.mem_commonNeighbors]
          exact and_comm
        rw [e]
        exact (native_coset_graph_order_four_common_neighbors.1 v y hy).2.1
      have h2 : {z | cgraph.Adj y z ∧ z ∈ sphereThree v}.ncard = 663552 := by
        have hv : v ∈ sphereFour y := mem_sphereFour_symm.1 hy
        obtain ⟨-, Ω, -, -, -, -, -, -, -, hsub, hpart, horb, hcard, -⟩ :=
          native_type_four_pair_eight_neighborhood_orbits y v hv
        have e : {z | cgraph.Adj y z ∧ z ∈ sphereThree v} = Ω 2 :=
          hglob.2 y v hv Ω hsub hpart horb hcard
        rw [e, hcard 2]
        rfl
      have := hsum y
      exact ⟨h0, h1, h2, by omega⟩
    classical
    have : Fintype CVert := Fintype.ofFinite CVert
    let O : Fin 4 → Set CVert := ![{v}, cgraph.neighborSet v, sphereThree v, sphereFour v]
    have hd0 : ∀ {y}, y ∈ O 0 → y ∉ O 1 ∧ y ∉ O 2 ∧ y ∉ O 3 := by
      intro y hy
      have hyv : y = v := hy
      subst hyv
      refine ⟨cgraph.irrefl, fun h => ?_, fun h => ?_⟩
      · have h' := h.1
        rw [SimpleGraph.dist_self] at h'
        omega
      · have h' := h.1
        rw [SimpleGraph.dist_self] at h'
        omega
    have hd1 : ∀ {y}, y ∈ O 1 → y ∉ O 2 ∧ y ∉ O 3 := by
      intro y hy
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have h' := h.1
        rw [SimpleGraph.dist_eq_one_iff_adj.2 hy] at h'
        omega
      · have h' := h.1
        rw [SimpleGraph.dist_eq_one_iff_adj.2 hy] at h'
        omega
    have hd2 : ∀ {y}, y ∈ O 2 → y ∉ O 3 := fun hy h => Set.disjoint_left.1 h34 hy h
    have hO : ∀ y, ∃! i, y ∈ O i := by
      intro y
      have hex : ∃ i, y ∈ O i := by
        rcases hcase y with h | h | h | h
        exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩]
      obtain ⟨i, hi⟩ := hex
      refine ⟨i, hi, fun j hj => ?_⟩
      fin_cases i <;> fin_cases j <;> first
        | rfl
        | exact absurd hj (hd0 hi).1 | exact absurd hj (hd0 hi).2.1
        | exact absurd hj (hd0 hi).2.2 | exact absurd hi (hd0 hj).1
        | exact absurd hi (hd0 hj).2.1 | exact absurd hi (hd0 hj).2.2
        | exact absurd hj (hd1 hi).1 | exact absurd hj (hd1 hi).2
        | exact absurd hi (hd1 hj).1 | exact absurd hi (hd1 hj).2
        | exact absurd hj (hd2 hi) | exact absurd hi (hd2 hj)
    have hQ : ∀ i j, ∀ y ∈ O i, {z | cgraph.Adj y z ∧ z ∈ O j}.ncard = spectralQ i j := by
      intro i j y hy
      fin_cases i
      · have hyv : y = v := hy
        subst hyv
        obtain ⟨a, b, c, d⟩ := hrow0
        fin_cases j
        exacts [a, b, c, d]
      · obtain ⟨a, b, c, d⟩ := hrow1 y hy
        fin_cases j
        exacts [a, b, c, d]
      · obtain ⟨a, b, c, d⟩ := hrow2 y hy
        fin_cases j
        exacts [a, b, c, d]
      · obtain ⟨a, b, c, d⟩ := hrow3 y hy
        fin_cases j
        exacts [a, b, c, d]
    obtain ⟨cell, hcell, hcQ⟩ := exists_cell_of_partition cgraph v O hO 0 rfl spectralQ hQ
    obtain ⟨cell', hcell', hQ'⟩ := exists_equitable_of_vertexTransitive cgraph v
      (fun x => ⟨cvIso (cvMul_transitive v x).choose, (cvMul_transitive v x).choose_spec⟩)
      cell 0 hcell spectralQ fun y j => (hcQ y 0).2 j
    exact not_equitable_spectralQ cgraph cgraph_connected cell' hcell' hQ'
  refine ⟨hmain, ?_⟩
  have : Nonempty CVert := ⟨cv0⟩
  obtain ⟨u, hu⟩ := hmain cv0
  calc 3 = cgraph.dist cv0 u := hu.symm
    _ ≤ cgraph.diam := SimpleGraph.dist_le_diam
        (SimpleGraph.connected_iff_ediam_ne_top.1 cgraph_connected)

end CFSG.Monster.B.TwoA.Amalgam
