module

public import CFSG.Monster.B.TwoA.Amalgam.GlobalTypeOrbit
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeDefs
public import CFSG.Monster.B.TwoA.Amalgam.Exact3510
public import CFSG.Monster.B.E6.FixedE6RootVector

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.E6 CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Overlap

theorem natCard_vStab_eq
    (v : CVert) : Nat.card (vStab v) = 306129918735099415756800 := by
  obtain ⟨ρ, -, hsurj, hker, hfix, hord, -⟩ := native_local_label_root v
  have hS : ∀ g ∈ Subgroup.zpowers (clabel v), g ∈ Shat := fun g hg =>
    (Subgroup.zpowers_le.2 (clabel_mem_Shat v)) hg
  have hV : ∀ (g : Dfull) (hg : g ∈ Subgroup.zpowers (clabel v)),
      (⟨g, hS g hg⟩ : Shat) ∈ vStab v := fun g hg =>
    mem_vStab.2 ((hfix ⟨g, hS g hg⟩).2 hg).1
  let e : ρ.ker ≃ Subgroup.zpowers (clabel v) :=
    { toFun := fun y => ⟨((y.1 : Shat) : Dfull), (hker y.1).1 (MonoidHom.mem_ker.1 y.2)⟩
      invFun := fun g => ⟨⟨⟨g.1, hS g.1 g.2⟩, hV g.1 g.2⟩, MonoidHom.mem_ker.2 ((hker _).2 g.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hsurj).toEquiv, card_GStar,
    Nat.card_congr e, Nat.card_zpowers, hord]

theorem natCard_vStab_inf_inf_mul
    (v w u : CVert) :
    Nat.card (vStab v ⊓ vStab w : Subgroup Shat) = (pairStabOrbit v w u).ncard *
      Nat.card (vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat) := by
  have h := natCard_stab_eq_mul v w u
  have e1 : Nat.card {s : Shat // cvMul v s = v ∧ cvMul w s = w} =
      Nat.card (vStab v ⊓ vStab w : Subgroup Shat) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun s =>
      ⟨fun h => ⟨mem_vStab.2 h.1, mem_vStab.2 h.2⟩, fun h => ⟨mem_vStab.1 h.1, mem_vStab.1 h.2⟩⟩)
  have e2 : Nat.card {s : Shat // cvMul v s = v ∧ cvMul w s = w ∧ cvMul u s = u} =
      Nat.card (vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun s =>
      ⟨fun h => ⟨⟨mem_vStab.2 h.1, mem_vStab.2 h.2.1⟩, mem_vStab.2 h.2.2⟩,
        fun h => ⟨mem_vStab.1 h.1.1, mem_vStab.1 h.1.2, mem_vStab.1 h.2⟩⟩)
  rw [← e1, ← e2]
  exact h

theorem natCard_vStab_inf_of_sphereFour
    {v w : CVert} (hw : w ∈ sphereFour v) :
    Nat.card (vStab v ⊓ vStab w : Subgroup Shat) = 27396522639360 := by
  have h := natCard_stab_eq_mul v v w
  have e1 : Nat.card {s : Shat // cvMul v s = v ∧ cvMul v s = v} = Nat.card (vStab v) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun s =>
      ⟨fun h => mem_vStab.2 h.1, fun h => ⟨mem_vStab.1 h, mem_vStab.1 h⟩⟩)
  have e2 : Nat.card {s : Shat // cvMul v s = v ∧ cvMul v s = v ∧ cvMul w s = w} =
      Nat.card (vStab v ⊓ vStab w : Subgroup Shat) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun s =>
      ⟨fun h => ⟨mem_vStab.2 h.1, mem_vStab.2 h.2.2⟩,
        fun h => ⟨mem_vStab.1 h.1, mem_vStab.1 h.1, mem_vStab.1 h.2⟩⟩)
  have e3 : pairStabOrbit v v w = sphereFour v := by
    rw [← vStabOrbit_eq_sphereFour exists_rootModel hw]
    ext x
    exact exists_congr fun s => ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1, h.2⟩⟩
  rw [e1, e2, e3, natCard_vStab_eq, native_coset_graph_order_four_common_neighbors.2.1 v] at h
  omega

theorem mem_sphereFour_comm
    {v w : CVert} : w ∈ sphereFour v ↔ v ∈ sphereFour w := by
  have h : ∀ a b : CVert, lblOrd b a = lblOrd a b := fun a b => by
    have e1 : clabel b * clabel a = MulAut.conj (clabel a)⁻¹ (clabel a * clabel b) := by
      rw [MulAut.conj_apply, inv_inv]
      group
    rw [lblOrd, lblOrd, e1, MulEquiv.orderOf_eq]
  refine ⟨fun hw => ⟨SimpleGraph.dist_comm.trans hw.1, ?_⟩,
    fun hv => ⟨SimpleGraph.dist_comm.trans hv.1, ?_⟩⟩
  · show lblOrd w v = 4 ∨ lblOrd w v = 8
    rw [h]
    exact hw.2
  · show lblOrd v w = 4 ∨ lblOrd v w = 8
    rw [h]
    exact hv.2

theorem exists_cvMul_eq_of_sphereThree
    {a b v w : CVert} (hb : b ∈ sphereThree a)
    (hw : w ∈ sphereThree v) : ∃ s : Shat, cvMul a s = v ∧ cvMul b s = w := by
  obtain ⟨s₁, hs₁⟩ := cvMul_transitive a v
  have h := sphereThree_cvMul hb s₁
  rw [hs₁] at h
  have hw' : w ∈ vStabOrbit v (cvMul b s₁) := by
    rw [vStabOrbit_eq_sphereThree exists_rootModel h]
    exact hw
  obtain ⟨s₂, hs₂v, hs₂⟩ := hw'
  exact ⟨s₁ * s₂, by rw [cvMul_mul, hs₁, hs₂v], by rw [cvMul_mul, hs₂]⟩

theorem exists_cvMul_eq_of_sphereFour
    {a b v w : CVert} (hb : b ∈ sphereFour a)
    (hw : w ∈ sphereFour v) : ∃ s : Shat, cvMul a s = v ∧ cvMul b s = w := by
  obtain ⟨s₁, hs₁⟩ := cvMul_transitive a v
  have h := sphereFour_cvMul hb s₁
  rw [hs₁] at h
  have hw' : w ∈ vStabOrbit v (cvMul b s₁) := by
    rw [vStabOrbit_eq_sphereFour exists_rootModel h]
    exact hw
  obtain ⟨s₂, hs₂v, hs₂⟩ := hw'
  exact ⟨s₁ * s₂, by rw [cvMul_mul, hs₁, hs₂v], by rw [cvMul_mul, hs₂]⟩

theorem pairStabOrbit_cvMul
    (a b c : CVert) (s : Shat) :
    pairStabOrbit (cvMul a s) (cvMul b s) (cvMul c s) =
      (fun x => cvMul x s) '' pairStabOrbit a b c := by
  ext x
  constructor
  · rintro ⟨t, ha, hb, rfl⟩
    refine ⟨cvMul c (s * t * s⁻¹), ⟨s * t * s⁻¹, ?_, ?_, rfl⟩, ?_⟩
    · rw [cvMul_mul, cvMul_mul, ha, cvMul_inv_cancel]
    · rw [cvMul_mul, cvMul_mul, hb, cvMul_inv_cancel]
    · show cvMul (cvMul c (s * t * s⁻¹)) s = cvMul (cvMul c s) t
      rw [← cvMul_mul, inv_mul_cancel_right, cvMul_mul]
  · rintro ⟨_, ⟨t, ha, hb, rfl⟩, rfl⟩
    have e : s * (s⁻¹ * t * s) = t * s := by group
    refine ⟨s⁻¹ * t * s, ?_, ?_, ?_⟩
    · rw [← cvMul_mul, e, cvMul_mul, ha]
    · rw [← cvMul_mul, e, cvMul_mul, hb]
    · rw [← cvMul_mul, e, cvMul_mul]

theorem cvMul_mem_outerOrbit
    {a b u : CVert} {n : ℕ} (hu : u ∈ outerOrbit a b n) (s : Shat) :
    cvMul u s ∈ outerOrbit (cvMul a s) (cvMul b s) n := by
  refine ⟨(cgraph_adj_cvMul b u s).2 hu.1, fun h => hu.2.1 ?_, ?_⟩
  · rw [commonNeighbors_cvMul] at h
    obtain ⟨x, hx, hxu⟩ := h
    rwa [← cvMul_injective s hxu]
  · rw [pairStabOrbit_cvMul, Set.ncard_image_of_injective _ (cvMul_injective s)]
    exact hu.2.2

theorem not_isRoot_repRootL_four_add_three :
    ¬IsRoot Tag.E6 (repRootL 4 + repRootL 3) := by
  rw [← RootOps.isRootB_iff]
  decide +kernel

theorem commute_repPoint_four_three :
    Commute (repPoint 4) (repPoint 3) := by
  have h := (simply_laced_root_commutator_unit Tag.E6 (Or.inr (Or.inl rfl)) (isRoot_repRootL 4)
    (isRoot_repRootL 3) (by decide) (by decide)).2 not_isRoot_repRootL_four_add_three K
    (pinnedX Tag.E6 K (repRootL 4) 1) (mem_rootSubgroup.2 ⟨1, rfl⟩)
    (pinnedX Tag.E6 K (repRootL 3) 1) (mem_rootSubgroup.2 ⟨1, rfl⟩)
  rw [← coe_repPoint, ← coe_repPoint] at h
  exact Subtype.ext h.eq

theorem exists_cross_type_edge :
    ∃ a b c : CVert, b ∈ sphereThree a ∧ c ∈ sphereFour a ∧ cgraph.Adj b c := by
  obtain ⟨M, hL⟩ := exists_rootModel cv0
  have hmem : ∀ i : Fin 5, (SemidirectProduct.inl (repPoint i) : GStar) ∈ rootClassStar :=
    fun i => (mem_rootClassStar_iff _).2 ⟨_, FixedE6Root.repPoint_mem_rootClass i, rfl⟩
  have hord : ∀ i : Fin 5,
      orderOf (rootStar * (SemidirectProduct.inl (repPoint i) : GStar)) = repOrder i := by
    intro i
    rw [rootStar, ← map_mul, orderOf_injective _ SemidirectProduct.inl_injective,
      orderOf_rootInv_mul_repPoint]
  obtain ⟨a, ha⟩ := M.exists_pt_eq (IsConj.refl rootStar)
  obtain ⟨b, hb⟩ := M.exists_pt_eq (hmem 4)
  obtain ⟨c, hc⟩ := M.exists_pt_eq (hmem 3)
  have hab : orderOf (M.pt a * M.pt b) = 3 := by
    rw [ha, hb, hord]
    rfl
  have hac : orderOf (M.pt a * M.pt c) = 4 := by
    rw [ha, hc, hord]
    rfl
  have hbc : b ≠ c := by
    rintro rfl
    rw [hab] at hac
    exact absurd hac (by decide)
  refine ⟨a, b, c,
    (M.labelThree_dist_iff hL a b).2 ((orderOf_eq_three_iff (M.pt_mem a) (M.pt_mem b)).1 hab),
    (M.labelFour_dist_iff hL a c).2 ((orderOf_eq_four_iff (M.pt_mem a) (M.pt_mem c)).1 hac),
    (M.adj_iff_commute hbc).2 ?_⟩
  rw [hb, hc]
  exact commute_repPoint_four_three.map SemidirectProduct.inl

theorem outerOrbit_142155_subset
    (hamb : AmbientRootOrbitsHyp) {v w : CVert}
    (hw : w ∈ sphereThree v) : outerOrbit v w 142155 ⊆ sphereThree v := by
  intro u hu
  obtain ⟨-, -, -, -, -, -, -, -, -, hdist, -⟩ :=
    type_three_neighborhood_global_distance_bound_of hamb hw
  have hu2 : u ∈ sphereThree v ∪ sphereFour v := by
    rw [← (native_coset_graph_two_distance_two_orbits.2.2.1 v).1]
    exact hdist u ⟨hu.1, hu.2.1⟩
  rcases hu2 with h3 | h4
  · exact h3
  exfalso
  have h1 := natCard_vStab_inf_inf_mul v w u
  rw [(native_order_three_common_neighbors_exact_3510.1 v w hw).2.2.2.2.2, hu.2.2] at h1
  have hT : Nat.card (vStab v ⊓ vStab w ⊓ vStab u : Subgroup Shat) = 908328960 := by omega
  have hdvd := Subgroup.card_dvd_of_le
    (show vStab v ⊓ vStab w ⊓ vStab u ≤ vStab v ⊓ vStab u from fun _ hs => ⟨hs.1.1, hs.2⟩)
  rw [hT, natCard_vStab_inf_of_sphereFour h4] at hdvd
  exact absurd hdvd (by norm_num)

theorem outerOrbit_3127410_subset
    (hamb : AmbientRootOrbitsHyp)
    (hclique : ∀ v w : CVert, w ∈ sphereThree v → ∀ D : Set (cgraph.commonNeighbors v w),
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D →
        (Subtype.val '' D).ncard = 22)
    {v w : CVert} (hw : w ∈ sphereThree v) : outerOrbit v w 3127410 ⊆ sphereFour v := by
  obtain ⟨a, b, c, hb, hc, hbc⟩ := exists_cross_type_edge
  have hca : ¬cgraph.Adj a c := (cgraph_dist_eq_two_iff.1 hc.1).2.1
  have hc3 : c ∈ outerOrbit a b 142155 ∪ outerOrbit a b 694980 ∪ outerOrbit a b 3127410 := by
    rw [← (type_three_neighborhood_global_distance_bound_of hamb hb).1]
    exact ⟨hbc, fun h => hca h.1⟩
  have hdisj := disjoint_sphereThree_sphereFour exists_rootModel a
  have hc4 : c ∈ outerOrbit a b 3127410 := by
    rcases hc3 with (h | h) | h
    · exact absurd hc (Set.disjoint_left.1 hdisj (outerOrbit_142155_subset hamb hb h))
    · exact absurd hc (Set.disjoint_left.1 hdisj
        (fischer_126_neighbor_orbit_globally_type_three_of hamb hclique hb h))
    · exact h
  obtain ⟨s, hsa, hsb⟩ := exists_cvMul_eq_of_sphereThree hb hw
  have hcs := cvMul_mem_outerOrbit hc4 s
  rw [hsa, hsb] at hcs
  have hcs4 := sphereFour_cvMul hc s
  rw [hsa] at hcs4
  intro u hu
  rw [← (type_three_neighborhood_global_distance_bound_of hamb hw).2.2.1 _ _ hcs] at hu
  obtain ⟨t, htv, -, rfl⟩ := hu
  have h := sphereFour_cvMul hcs4 t
  rwa [htv] at h

theorem ncard_pairStabOrbit_of_cross
    (hamb : AmbientRootOrbitsHyp)
    (hclique : ∀ v w : CVert, w ∈ sphereThree v → ∀ D : Set (cgraph.commonNeighbors v w),
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D →
        (Subtype.val '' D).ncard = 22)
    {v w u : CVert} (hw : w ∈ sphereFour v) (hu : u ∈ cgraph.neighborSet v)
    (hu3 : u ∈ sphereThree w) : (pairStabOrbit v w u).ncard = 663552 := by
  have hvw : ¬cgraph.Adj w v := fun h =>
    (cgraph_dist_eq_two_iff.1 hw.1).2.1 (cgraph.adj_symm h)
  have hv4 : v ∈ sphereFour w := mem_sphereFour_comm.1 hw
  have hv3 : v ∈ outerOrbit w u 142155 ∪ outerOrbit w u 694980 ∪ outerOrbit w u 3127410 := by
    rw [← (type_three_neighborhood_global_distance_bound_of hamb hu3).1]
    exact ⟨cgraph.adj_symm hu, fun h => hvw h.1⟩
  have hdisj := disjoint_sphereThree_sphereFour exists_rootModel w
  have hv5 : v ∈ outerOrbit w u 3127410 := by
    rcases hv3 with (h | h) | h
    · exact absurd hv4 (Set.disjoint_left.1 hdisj (outerOrbit_142155_subset hamb hu3 h))
    · exact absurd hv4 (Set.disjoint_left.1 hdisj
        (fischer_126_neighbor_orbit_globally_type_three_of hamb hclique hu3 h))
    · exact h
  have h1 := natCard_vStab_inf_inf_mul w u v
  rw [(native_order_three_common_neighbors_exact_3510.1 w u hu3).2.2.2.2.2, hv5.2.2] at h1
  have hT : Nat.card (vStab w ⊓ vStab u ⊓ vStab v : Subgroup Shat) = 41287680 := by omega
  have e : vStab v ⊓ vStab w ⊓ vStab u = vStab w ⊓ vStab u ⊓ vStab v := by
    ext s
    simp only [Subgroup.mem_inf]
    tauto
  have h2 := natCard_vStab_inf_inf_mul v w u
  rw [natCard_vStab_inf_of_sphereFour hw, e, hT] at h2
  omega

theorem exists_mem_neighborSet_inter_sphereThree
    {v w : CVert} (hw : w ∈ sphereFour v) :
    ∃ u, u ∈ cgraph.neighborSet v ∧ u ∈ sphereThree w := by
  obtain ⟨a, b, c, hb, hc, hbc⟩ := exists_cross_type_edge
  obtain ⟨s, hsc, hsa⟩ := exists_cvMul_eq_of_sphereFour (mem_sphereFour_comm.1 hc) hw
  refine ⟨cvMul b s, ?_, ?_⟩
  · rw [← hsc]
    exact (cgraph_adj_cvMul c b s).2 (cgraph.adj_symm hbc)
  · rw [← hsa]
    exact sphereThree_cvMul hb s

theorem eightSizes_injective :
    ∀ i j : Fin 8, (![648, 8064, 663552, 1, 1134, 36288, 1161216, 2097152] : Fin 8 → ℕ) i =
      ![648, 8064, 663552, 1, 1134, 36288, 1161216, 2097152] j → i = j := by
  decide

theorem neighborSet_inter_sphereThree_eq
    (hamb : AmbientRootOrbitsHyp)
    (hclique : ∀ v w : CVert, w ∈ sphereThree v → ∀ D : Set (cgraph.commonNeighbors v w),
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D →
        (Subtype.val '' D).ncard = 22)
    {v w : CVert} (hw : w ∈ sphereFour v) (Ω : Fin 8 → Set CVert)
    (hsub : ∀ i, Ω i ⊆ cgraph.neighborSet v) (hpart : ∀ u ∈ cgraph.neighborSet v, ∃! i, u ∈ Ω i)
    (horb : ∀ i, ∀ u ∈ Ω i, {x | ∃ y ∈ vStab v ⊓ vStab w, cvMul u y = x} = Ω i)
    (hcard : ∀ i, (Ω i).ncard = ![648, 8064, 663552, 1, 1134, 36288, 1161216, 2097152] i) :
    cgraph.neighborSet v ∩ sphereThree w = Ω 2 := by
  have horb' : ∀ i, ∀ u ∈ Ω i, pairStabOrbit v w u = Ω i := fun i u hu => by
    rw [← horb i u hu]
    ext x
    exact ⟨fun ⟨s, hv, hw', hx⟩ => ⟨s, ⟨mem_vStab.2 hv, mem_vStab.2 hw'⟩, hx⟩,
      fun ⟨s, hs, hx⟩ => ⟨s, mem_vStab.1 hs.1, mem_vStab.1 hs.2, hx⟩⟩
  have hin : ∀ u ∈ cgraph.neighborSet v ∩ sphereThree w, u ∈ Ω 2 := by
    rintro u ⟨hu1, hu3⟩
    obtain ⟨i, hi, -⟩ := hpart u hu1
    have h := ncard_pairStabOrbit_of_cross hamb hclique hw hu1 hu3
    rw [horb' i u hi, hcard i] at h
    rw [← eightSizes_injective i 2 h]
    exact hi
  obtain ⟨u₀, hu₀1, hu₀3⟩ := exists_mem_neighborSet_inter_sphereThree hw
  have hu₀ := hin u₀ ⟨hu₀1, hu₀3⟩
  refine Set.Subset.antisymm hin fun x hx => ?_
  have hx' := hx
  rw [← horb' 2 u₀ hu₀] at hx'
  obtain ⟨s, -, hsw, rfl⟩ := hx'
  refine ⟨hsub 2 hx, ?_⟩
  have h := sphereThree_cvMul hu₀3 s
  rwa [hsw] at h

theorem fischer_remaining_orbit_global_types_of
    (hamb : AmbientRootOrbitsHyp)
    (hclique : ∀ v w : CVert, w ∈ sphereThree v → ∀ D : Set (cgraph.commonNeighbors v w),
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D →
        (Subtype.val '' D).ncard = 22) :
    (∀ v w : CVert, w ∈ sphereThree v →
      outerOrbit v w 142155 ∪ outerOrbit v w 694980 ⊆ sphereThree v ∧
        outerOrbit v w 3127410 ⊆ sphereFour v) ∧
    ∀ v w : CVert, w ∈ sphereFour v → ∀ Ω : Fin 8 → Set CVert,
      (∀ i, Ω i ⊆ cgraph.neighborSet v) → (∀ u ∈ cgraph.neighborSet v, ∃! i, u ∈ Ω i) →
      (∀ i, ∀ u ∈ Ω i, {x | ∃ y ∈ vStab v ⊓ vStab w, cvMul u y = x} = Ω i) →
      (∀ i, (Ω i).ncard = ![648, 8064, 663552, 1, 1134, 36288, 1161216, 2097152] i) →
      cgraph.neighborSet v ∩ sphereThree w = Ω 2 :=
  ⟨fun _ _ hw => ⟨Set.union_subset (outerOrbit_142155_subset hamb hw)
      (fischer_126_neighbor_orbit_globally_type_three_of hamb hclique hw),
      outerOrbit_3127410_subset hamb hclique hw⟩,
    fun _ _ hw Ω hsub hpart horb hcard =>
      neighborSet_inter_sphereThree_eq hamb hclique hw Ω hsub hpart horb hcard⟩

end CFSG.Monster.B.TwoA.Amalgam
