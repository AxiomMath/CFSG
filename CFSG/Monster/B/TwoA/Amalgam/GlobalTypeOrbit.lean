module

public import CFSG.Monster.B.TwoA.Amalgam.GlobalTypeCore
public import CFSG.Monster.B.TwoA.Amalgam.OrderThreeTT

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8

theorem exists_not_adj_of_ncard
    {v w : CVert}
    (hcl : ∀ D : Set (cgraph.commonNeighbors v w),
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D →
        (Subtype.val '' D).ncard = 22)
    {X : Set CVert} (hX : X ⊆ cgraph.commonNeighbors v w) (hcard : 22 < X.ncard) :
    ∃ a ∈ X, ∃ b ∈ X, a ≠ b ∧ ¬cgraph.Adj a b := by
  by_contra hcon'
  have hcon : ∀ a ∈ X, ∀ b ∈ X, a ≠ b → cgraph.Adj a b := fun a ha b hb hab =>
    by_contra fun hn => hcon' ⟨a, ha, b, hb, hab, hn⟩
  have : Finite CVert := short_F4_involution_coset_graph_data.1
  set D : Set (cgraph.commonNeighbors v w) := {z | (z : CVert) ∈ X} with hD
  have hDX : Subtype.val '' D = X := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hx
      exact ⟨⟨x, hX hx⟩, hx, rfl⟩
  have hclD : (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D := by
    intro a ha b hb hab
    exact hcon a ha b hb fun e => hab (Subtype.ext e)
  obtain ⟨D', hDD', hmax⟩ := Finite.exists_le_maximal hclD
  have h22 := hcl D' hmax
  have hle : X.ncard ≤ (Subtype.val '' D').ncard := by
    rw [← hDX]
    exact Set.ncard_le_ncard (Set.image_mono hDD') (Set.toFinite _)
  omega

theorem orderOf_clabel_mul_ne_three_of_mem_cPi
    {s : Shat} {a b : CVert} (ha : a ∈ cPi s)
    (hb : b ∈ cPi s) (hab : a ≠ b) (hna : ¬cgraph.Adj a b) :
    orderOf (clabel a * clabel b) ≠ 3 := by
  intro h3
  have ha' := mem_cPi_iff.1 ha
  have hb' := mem_cPi_iff.1 hb
  have hne : (⟨_, ha'⟩ : cPi0) ≠ ⟨_, hb'⟩ := fun e =>
    hab (cvMul_injective s⁻¹ (congrArg Subtype.val e))
  have hna' : ¬cgraphPi.Adj ⟨_, ha'⟩ ⟨_, hb'⟩ := fun h =>
    hna ((cgraph_adj_cvMul a b s⁻¹).1 h)
  have hsq := (native_coset_graph_order_four_common_neighbors.2.2 _ _ hne hna').1
  have h3' : orderOf (clabel (cvMul a s⁻¹) * clabel (cvMul b s⁻¹)) = 3 := by
    have e := lblOrd_cvMul a b s⁻¹
    rw [lblOrd, lblOrd, h3] at e
    exact e
  have hx : orderOf xhat = 3 := by
    rw [← hsq, Nat.Coprime.orderOf_pow (by rw [h3']; norm_num), h3']
  rw [orderOf_xhat] at hx
  exact absurd hx (by norm_num)

theorem fischer_126_neighbor_orbit_globally_type_three_of
    (hamb : AmbientRootOrbitsHyp)
    (hclique : ∀ v w : CVert, w ∈ sphereThree v → ∀ D : Set (cgraph.commonNeighbors v w),
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D →
        (Subtype.val '' D).ncard = 22)
    {v w : CVert} (hw : w ∈ sphereThree v) : outerOrbit v w 694980 ⊆ sphereThree v := by
  intro u hu
  obtain ⟨-, -, -, -, -, -, -, h126, -, hdist, -⟩ :=
    type_three_neighborhood_global_distance_bound_of hamb hw
  have hd : cgraph.dist v u = 2 := hdist u ⟨hu.1, hu.2.1⟩
  have hu2 : u ∈ sphereThree v ∪ sphereFour v := by
    rw [← (native_coset_graph_two_distance_two_orbits.2.2.1 v).1]
    exact hd
  rcases hu2 with h3 | h4
  · exact h3
  exfalso
  have hOF := native_coset_graph_order_four_common_neighbors.1 v u h4
  obtain ⟨s, hvs, hus⟩ := hOF.2.2.1
  have hsub := hOF.2.2.2.2 s hvs hus
  have hXM : cgraph.neighborSet u ∩ cgraph.commonNeighbors v w ⊆ cgraph.commonNeighbors v w :=
    Set.inter_subset_right
  obtain ⟨a, ha, b, hb, hab, hna⟩ :=
    exists_not_adj_of_ncard (hclique v w hw) hXM (by rw [h126 u hu]; norm_num)
  obtain ⟨θ₀, -, hTT⟩ := native_order_three_common_neighbor_three_transposition_group
  have h3 : orderOf (clabelS a * clabelS b) = 3 :=
    ((hTT v w hw).2.2.2.2.2.2.1 a (hXM ha) b (hXM hb) hab).2 hna
  have hmem : ∀ z ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors v w, z ∈ cPi s :=
    fun z hz => hsub ⟨hz.2.1, hz.1⟩
  refine orderOf_clabel_mul_ne_three_of_mem_cPi (hmem a ha) (hmem b hb) hab hna ?_
  rw [← Subgroup.orderOf_coe, Subgroup.coe_mul, coe_clabelS, coe_clabelS] at h3
  exact h3

end CFSG.Monster.B.TwoA.Amalgam
