module

public import CFSG.Monster.B.GSide.TriangulableInputs
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeCentOrbits
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeTraceMain
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeOuter
public import CFSG.Monster.B.TwoA.Amalgam.DistThreePaths
public import CFSG.Monster.B.TwoA.Amalgam.DiameterThree
public import CFSG.Monster.B.TwoA.Amalgam.FischerNodes

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.GSide

theorem native_maximal_clique_ncard :
    ∀ v w : CVert, w ∈ sphereThree v → ∀ D : Set (cgraph.commonNeighbors v w),
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D →
        (Subtype.val '' D).ncard = 22 :=
  fun v w hw D hD => (native_Fischer_maximal_clique_stabilizer_kernel v w hw).1 D hD

section Ambient

variable (hamb : AmbientRootOrbitsHyp)

include hamb

theorem sphereDistThree_nonempty_of_ambient :
    ∀ v : CVert, (sphereDistThree v).Nonempty :=
  sphereDistThree_nonempty_of_inputs hamb native_maximal_clique_ncard

theorem typeFourOrbit_of_ambient :
    ∀ ⦃v w : CVert⦄, w ∈ sphereFour v → ∀ u ∈ cgraph.neighborSet v ∩ sphereDistThree w,
      pairStabOrbit v w u = cgraph.neighborSet v ∩ sphereDistThree w ∧
        (cgraph.neighborSet v ∩ sphereDistThree w).ncard = 8064 :=
  native_type_four_neighborhood_dist_three_orbit
    (fischer_remaining_orbit_global_types_of hamb native_maximal_clique_ncard).2
    (hno_of_ambient hamb)

theorem distThreePaths_of_ambient :
    (∀ v u u' : CVert, u ∈ sphereDistThree v → u' ∈ sphereDistThree v →
      ∃ g : Shat, cvMul v g = v ∧ cvMul u g = u') ∧
    (∀ v w : CVert, w ∈ sphereFour v →
      (cgraph.neighborSet w ∩ sphereDistThree v).ncard = 8064 ∧
        ∀ u ∈ cgraph.neighborSet w ∩ sphereDistThree v,
          pairStabOrbit w v u = cgraph.neighborSet w ∩ sphereDistThree v) ∧
    (∀ v w : CVert, w ∈ sphereThree v → Disjoint (cgraph.neighborSet w) (sphereDistThree v)) ∧
    (∀ v u : CVert, u ∈ sphereDistThree v → (xSet v u).Nonempty ∧
      (∀ w ∈ xSet v u, ∀ w' ∈ xSet v u,
        ∃ g : Shat, cvMul v g = v ∧ cvMul u g = u ∧ cvMul w g = w') ∧
      ∀ w ∈ xSet v u, Nat.card ↥(vStab v ⊓ vStab u ⊓ vStab w) = 3397386240) ∧
    (∀ v u : CVert, u ∈ sphereDistThree v → (xSet u v).Nonempty ∧
      (∀ w ∈ xSet u v, ∀ w' ∈ xSet u v,
        ∃ g : Shat, cvMul v g = v ∧ cvMul u g = u ∧ cvMul w g = w') ∧
      ∀ w ∈ xSet u v, Nat.card ↥(vStab v ⊓ vStab u ⊓ vStab w) = 3397386240) :=
  native_distance_three_single_orbit_and_8064_paths (sphereDistThree_nonempty_of_ambient hamb)
    (fun v w hw u hwu => hno_of_ambient hamb v w u hw hwu) (typeFourOrbit_of_ambient hamb)

theorem distThreePathFact_of_ambient :
    DistThreePathFact := by
  obtain ⟨-, h2, -, h4, -⟩ := distThreePaths_of_ambient hamb
  refine ⟨fun v u hu => (h4 v u hu).1, fun v w hw u hu => ⟨hu.1, ?_⟩⟩
  obtain ⟨hcard, horb⟩ := h2 v w hw
  have hset : {x | ∃ y ∈ vStab w ⊓ vStab v, cvMul u y = x} = pairStabOrbit w v u := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy.1, hy.2, rfl⟩
    · rintro ⟨y, hyw, hyv, rfl⟩
      exact ⟨y, ⟨hyw, hyv⟩, rfl⟩
  rw [hset, horb u hu, hcard]

theorem labelsInput_of_ambient :
    DistThreeLabelsInput :=
  distThree_labels_of_pathFact (distThreePathFact_of_ambient hamb)

theorem outerInput_of_ambient :
    DistThreeOuterInput := by
  intro v u hvu ρ iv hρ y hy
  exact ((native_distance_three_label_is_outer_local_involution_of
    (distThreePathFact_of_ambient hamb) distThreeBaseTransvFact_holds
    (mem_sphereDistThree.2 hvu)).2.2 ρ hρ.1 y hy).1

theorem pathInput_of_ambient :
    DistThreePathInput := by
  obtain ⟨h1, h2, -, h4, -⟩ := distThreePaths_of_ambient hamb
  exact ⟨h1, fun v w hw => (h2 v w hw).1, h4⟩

theorem typeThreeBoundInput_of_ambient : TypeThreeBoundInput :=
  fun v w u hw hwu hu => hno_of_ambient hamb v w u hw hwu (mem_sphereDistThree.1 hu)

theorem distThreeLocalOrbits_of_ambient :
    DistThreeLocalOrbits := by
  intro v u hvu
  have h := native_distance_three_pair_two_local_root_orbits (labelsInput_of_ambient hamb)
    (outerInput_of_ambient hamb) (pathInput_of_ambient hamb)
    (typeThreeBoundInput_of_ambient hamb) hvu
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1⟩

theorem distThreeFieldCoords_of_ambient :
    DistThreeFieldCoords := by
  intro v u hvu
  obtain ⟨hc, ρ, iu, hcomp, hβ, -, hfix, -⟩ :=
    (native_distance_three_pair_two_local_root_orbits (labelsInput_of_ambient hamb)
      (outerInput_of_ambient hamb) (pathInput_of_ambient hamb)
      (typeThreeBoundInput_of_ambient hamb) hvu).2.2.2.2.2.2.2.2.2.1
  exact ⟨hc, ρ, iu, hcomp.2.2, hβ, hfix⟩

theorem ncard_sphereDistThree_of_ambient
    (v : CVert) :
    (sphereDistThree v).ncard = 23113728 := by
  obtain ⟨u, hu⟩ := sphereDistThree_nonempty_of_ambient hamb v
  obtain ⟨-, -, -, -, -, -, -, h⟩ :=
    native_distance_three_pair_is_full_local_centralizer (labelsInput_of_ambient hamb)
      (outerInput_of_ambient hamb) (pathInput_of_ambient hamb)
      (typeThreeBoundInput_of_ambient hamb) (mem_sphereDistThree.1 hu)
  exact h

theorem diameter_three_rank_five_of_ambient :
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
      (cgraph.neighborSet u ∩ sphereDistThree v).ncard = 69615 :=
  diameter_three_rank_five_of (distThreeLocalOrbits_of_ambient hamb) (hno_of_ambient hamb)
    (sphereDistThree_nonempty_of_ambient hamb) (distThreePaths_of_ambient hamb).1
    (ncard_sphereDistThree_of_ambient hamb)

theorem clabel_ne_of_dist_three_of_ambient :
    ∀ v u : CVert, cgraph.dist v u = 3 → clabel v ≠ clabel u := by
  intro v u hvu he
  apply (labelsInput_of_ambient hamb v u hvu).2.2.1
  apply Subtype.ext
  rw [coe_clabelS, coe_clabelS]
  exact he.symm

theorem global_label_of_ambient :
    Function.Injective clabel ∧
    Set.range clabel = {x : Dfull | ∃ s : Shat, x = (s : Dfull)⁻¹ * Sp8.cQ * s} ∧
    (∀ (v : CVert) (s : Shat), clabel (cvMul v s) = (s : Dfull)⁻¹ * clabel v * s) ∧
    ∀ (v : CVert) (s : Shat), (s : Dfull) * clabel v = clabel v * s ↔ cvMul v s = v :=
  global_label_of (diameter_three_rank_five_of_ambient hamb).1
    (clabel_ne_of_dist_three_of_ambient hamb)

theorem cgraph_triangulable_of_ambient :
    CFSG.Monster.B.Recog.Triangulable cgraph :=
  cgraph_triangulable_of_inputs hamb native_maximal_clique_ncard
    (distThreeLocalOrbits_of_ambient hamb) (distThreeFieldCoords_of_ambient hamb)

end Ambient

end CFSG.Monster.B.TwoA.Amalgam
