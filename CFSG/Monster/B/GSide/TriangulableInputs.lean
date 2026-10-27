module

public import CFSG.Monster.B.GSide.RonanTwo
public import CFSG.Monster.B.GSide.RonanThreeCore
public import CFSG.Monster.B.TwoA.Amalgam.GlobalTypeRemain
public import CFSG.Monster.B.TwoA.Amalgam.SpectralThree

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open SimpleGraph CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam

theorem hno_of_ambient
    (hamb : AmbientRootOrbitsHyp) :
    ∀ v w u : CVert, w ∈ sphereThree v → cgraph.Adj w u → cgraph.dist v u ≠ 3 := by
  intro v w u hw hwu
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h⟩ :=
    type_three_neighborhood_global_distance_bound_of hamb hw
  exact h u hwu

theorem ht3_of_ambient
    (hamb : AmbientRootOrbitsHyp) :
    ∀ a b : CVert, b ∈ sphereThree a →
      ∀ u ∈ cgraph.neighborSet b \ cgraph.commonNeighbors a b,
        (cgraph.neighborSet u ∩ cgraph.commonNeighbors a b).Nonempty := by
  intro a b hb u hu
  obtain ⟨h1, -, -, -, -, -, h7, h8, h9, -⟩ :=
    type_three_neighborhood_global_distance_bound_of hamb hb
  rw [h1] at hu
  rcases hu with (hu | hu) | hu
  · exact Set.nonempty_of_ncard_ne_zero (by rw [h7 u hu]; norm_num)
  · exact Set.nonempty_of_ncard_ne_zero (by rw [h8 u hu]; norm_num)
  · exact Set.nonempty_of_ncard_ne_zero (by rw [h9 u hu]; norm_num)

theorem b3loc_of_hno
    (hno : ∀ v w u : CVert, w ∈ sphereThree v → cgraph.Adj w u → cgraph.dist v u ≠ 3) :
    ∀ v u c : CVert, cgraph.dist v u = 3 → cgraph.Adj u c → cgraph.dist v c = 2 →
      c ∈ sphereFour v := by
  intro v u c hvu huc hvc
  have hc : c ∈ {w | cgraph.dist v w = 2} := hvc
  rw [(native_coset_graph_two_distance_two_orbits.2.2.1 v).1] at hc
  rcases hc with hc | hc
  · exact absurd hvu (hno v c u hc huc.symm)
  · exact hc

theorem mem_omega_of_ncard_cvOrbit
    {a b u : CVert} {Ω : Fin 8 → Set CVert}
    (hpart : ∀ u ∈ cgraph.neighborSet a, ∃! i, u ∈ Ω i)
    (horb : ∀ i, ∀ u ∈ Ω i, cvOrbit (vStab a ⊓ vStab b) u = Ω i)
    (hcard : ∀ i, (Ω i).ncard = ![648, 8064, 663552, 1, 1134, 36288, 1161216, 2097152] i)
    (hu : u ∈ cgraph.neighborSet a) {j : Fin 8}
    (h : (cvOrbit (vStab a ⊓ vStab b) u).ncard =
      ![648, 8064, 663552, 1, 1134, 36288, 1161216, 2097152] j) : u ∈ Ω j := by
  obtain ⟨i, hi, -⟩ := hpart u hu
  have e : (![648, 8064, 663552, 1, 1134, 36288, 1161216, 2097152] : Fin 8 → ℕ) i =
      ![648, 8064, 663552, 1, 1134, 36288, 1161216, 2097152] j := by
    rw [← hcard i, ← horb i u hi, h]
  have hinj : Function.Injective
      (![648, 8064, 663552, 1, 1134, 36288, 1161216, 2097152] : Fin 8 → ℕ) := by decide
  rw [← hinj e]
  exact hi

theorem exists_cvMul_eq_of_mem_sphereFour
    {b a₀ a : CVert} (h₀ : a₀ ∈ sphereFour b)
    (h : a ∈ sphereFour b) : ∃ s : Shat, cvMul b s = b ∧ cvMul a₀ s = a := by
  obtain ⟨-, hdisj, horb, -⟩ := native_coset_graph_two_distance_two_orbits.2.2.1 b
  have hmem : vStabOrbit b a₀ ∈ ({sphereThree b, sphereFour b} : Set (Set CVert)) := by
    rw [← horb]
    exact ⟨a₀, h₀.1, rfl⟩
  have hself : a₀ ∈ vStabOrbit b a₀ := ⟨1, cvMul_one b, cvMul_one a₀⟩
  rcases hmem with e | e
  · rw [e] at hself
    exact absurd h₀ (Set.disjoint_left.1 hdisj hself)
  · rw [Set.mem_singleton_iff] at e
    have ha : a ∈ vStabOrbit b a₀ := by
      rw [e]
      exact h
    exact ha

theorem nonempty_neighborSet_inter_sphereDistThree
    (h3 : ∀ v : CVert, (sphereDistThree v).Nonempty) (hloc : DistThreeLocalOrbits)
    {a b : CVert} (hb : b ∈ sphereFour a) :
    (cgraph.neighborSet a ∩ sphereDistThree b).Nonempty := by
  obtain ⟨u₀, hu₀⟩ := h3 b
  obtain ⟨a₀, ha₀u, ha₀⟩ := (hloc b u₀ hu₀).2.1
  obtain ⟨s, hsb, hsa⟩ := exists_cvMul_eq_of_mem_sphereFour ha₀ (mem_sphereFour_comm.1 hb)
  refine ⟨cvMul u₀ s, ?_, ?_⟩
  · have h := (cgraph_adj_cvMul a₀ u₀ s).2 (cgraph.adj_symm ha₀u)
    rwa [hsa] at h
  · show cgraph.dist b (cvMul u₀ s) = 3
    rw [← hsb, dist_cvMul]
    exact hu₀

section Inputs

variable (hamb : AmbientRootOrbitsHyp)
  (hclique : ∀ v w : CVert, w ∈ sphereThree v → ∀ D : Set (cgraph.commonNeighbors v w),
    Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D →
      (Subtype.val '' D).ncard = 22)

include hamb hclique in
theorem hrem_of_inputs :
    ∀ a b : CVert, b ∈ sphereFour a → ∀ u ∈ cgraph.neighborSet a,
      (cvOrbit (vStab a ⊓ vStab b) u).ncard = 663552 → u ∈ sphereThree b := by
  intro a b hb u hu h
  obtain ⟨-, Ω, -, -, -, -, -, -, -, hsub, hpart, horb, hcard, -⟩ :=
    native_type_four_pair_eight_neighborhood_orbits a b hb
  have hrem := (fischer_remaining_orbit_global_types_of hamb hclique).2 a b hb Ω hsub hpart
    horb hcard
  have hu2 : u ∈ Ω 2 := mem_omega_of_ncard_cvOrbit hpart horb hcard hu h
  rw [← hrem] at hu2
  exact hu2.2

include hamb hclique in
theorem ht4a_of_inputs :
    ∀ a b : CVert, b ∈ sphereFour a → ∀ u ∈ cgraph.neighborSet a,
      (cvOrbit (vStab a ⊓ vStab b) u).ncard = 36288 →
        (cgraph.neighborSet u ∩ cgraph.commonNeighbors a b).ncard = 24 := by
  intro a b hb u hu h
  obtain ⟨-, Ω, -, -, -, -, -, -, -, hsub, hpart, horb, hcard, -, hΩ0, -⟩ :=
    native_type_four_pair_eight_neighborhood_orbits a b hb
  have hT := native_type_four_neighborhood_global_distance_bound
    (fischer_remaining_orbit_global_types_of hamb hclique).2 (hno_of_ambient hamb) hb hsub hpart
    horb hcard
  rw [← hΩ0]
  exact hT.2.2.2.1 u (mem_omega_of_ncard_cvOrbit hpart horb hcard hu (j := 5) h)

include hamb hclique in
theorem ht4b_of_inputs :
    ∀ a b : CVert, b ∈ sphereFour a → ∀ u ∈ cgraph.neighborSet a,
      ((cvOrbit (vStab a ⊓ vStab b) u).ncard = 1161216 ∨
        (cvOrbit (vStab a ⊓ vStab b) u).ncard = 2097152) →
        ∃ z ∈ cgraph.commonNeighbors a b, LabelThree z u := by
  intro a b hb u hu h
  obtain ⟨-, Ω, -, -, -, -, -, -, -, hsub, hpart, horb, hcard, -, hΩ0, -⟩ :=
    native_type_four_pair_eight_neighborhood_orbits a b hb
  have hT := native_type_four_neighborhood_global_distance_bound
    (fischer_remaining_orbit_global_types_of hamb hclique).2 (hno_of_ambient hamb) hb hsub hpart
    horb hcard
  rw [← hΩ0]
  rcases h with h | h
  · exact hT.2.2.2.2.2.2 u (mem_omega_of_ncard_cvOrbit hpart horb hcard hu (j := 6) h)
  · obtain ⟨z, hz⟩ := Set.nonempty_of_ncard_ne_zero
      (by rw [hT.2.2.2.2.2.1 u (mem_omega_of_ncard_cvOrbit hpart horb hcard hu (j := 7) h)];
          norm_num)
    exact ⟨z, hz.1, hz.2⟩

include hamb hclique in
theorem sphereDistThree_nonempty_of_inputs :
    ∀ v : CVert, (sphereDistThree v).Nonempty :=
  (native_graph_distance_three_exists_spectral_obstruction_of
    (fun v w hw => by
      obtain ⟨h1, -, -, h4, h5, h6, -⟩ := type_three_neighborhood_global_distance_bound_of hamb hw
      exact ⟨h1, h4, h5, h6⟩)
    (fischer_remaining_orbit_global_types_of hamb hclique)).1

include hamb hclique in
theorem h8064_of_inputs
    (hloc : DistThreeLocalOrbits) :
    ∀ a b : CVert, b ∈ sphereFour a → ∀ u ∈ cgraph.neighborSet a,
      (cvOrbit (vStab a ⊓ vStab b) u).ncard = 8064 → cgraph.dist b u = 3 := by
  intro a b hb u hu h
  obtain ⟨-, Ω, -, -, -, -, -, -, -, hsub, hpart, horb, hcard, -⟩ :=
    native_type_four_pair_eight_neighborhood_orbits a b hb
  have hT := native_type_four_neighborhood_global_distance_bound
    (fischer_remaining_orbit_global_types_of hamb hclique).2 (hno_of_ambient hamb) hb hsub hpart
    horb hcard
  have hne := nonempty_neighborSet_inter_sphereDistThree
    (sphereDistThree_nonempty_of_inputs hamb hclique) hloc hb
  have h1 : cgraph.neighborSet a ∩ sphereDistThree b = Ω 1 :=
    hT.2.1.resolve_left hne.ne_empty
  have hu1 : u ∈ Ω 1 := mem_omega_of_ncard_cvOrbit hpart horb hcard hu h
  rw [← h1] at hu1
  exact hu1.2

end Inputs

theorem cgraph_triangulable_of_inputs
    (hamb : AmbientRootOrbitsHyp)
    (hclique : ∀ v w : CVert, w ∈ sphereThree v → ∀ D : Set (cgraph.commonNeighbors v w),
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D →
        (Subtype.val '' D).ncard = 22)
    (hloc : DistThreeLocalOrbits) (hcoord : DistThreeFieldCoords) :
    CFSG.Monster.B.Recog.Triangulable cgraph :=
  cgraph_triangulable_of_local_weak (dist_le_three hloc (hno_of_ambient hamb))
    (cgraph_ronan_two (ht3_of_ambient hamb) (h8064_of_inputs hamb hclique hloc)
      (hrem_of_inputs hamb hclique) (ht4a_of_inputs hamb hclique) (ht4b_of_inputs hamb hclique))
    (b3loc_of_hno (hno_of_ambient hamb)) (b3con_of hcoord hloc) (b3tri_of hloc)

end CFSG.Monster.B.GSide
