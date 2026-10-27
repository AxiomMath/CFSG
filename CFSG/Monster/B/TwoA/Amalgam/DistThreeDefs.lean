module

public import CFSG.Monster.B.TwoA.Amalgam.DistTwoCore
public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphLocal

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA

@[expose] def sphereDistThree
    (v : CVert) : Set CVert := {u | cgraph.dist v u = 3}

theorem mem_sphereDistThree
    {v u : CVert} : u ∈ sphereDistThree v ↔ cgraph.dist v u = 3 :=
  Iff.rfl

@[expose] def xSet
    (v u : CVert) : Set CVert := cgraph.neighborSet u ∩ sphereFour v

theorem mem_xSet
    {v u w : CVert} : w ∈ xSet v u ↔ w ∈ cgraph.neighborSet u ∧ w ∈ sphereFour v :=
  Iff.rfl

theorem dist_cvMul
    (v w : CVert) (s : Shat) :
    cgraph.dist (cvMul v s) (cvMul w s) = cgraph.dist v w := by
  have key : ∀ (v w : CVert) (s : Shat), cgraph.dist (cvMul v s) (cvMul w s) ≤ cgraph.dist v w :=
    by
    intro v w s
    obtain ⟨p, hp⟩ := (cgraph_connected.preconnected v w).exists_walk_length_eq_dist
    calc cgraph.dist (cvMul v s) (cvMul w s) ≤ (p.map (cvIso s).toHom).length :=
          SimpleGraph.dist_le _
      _ = cgraph.dist v w := by rw [SimpleGraph.Walk.length_map, hp]
  refine le_antisymm (key v w s) ?_
  have h := key (cvMul v s) (cvMul w s) s⁻¹
  rwa [cvMul_inv_cancel, cvMul_inv_cancel] at h

theorem sphereDistThree_cvMul
    {v u : CVert} (hu : u ∈ sphereDistThree v) (s : Shat) :
    cvMul u s ∈ sphereDistThree (cvMul v s) := by
  rw [mem_sphereDistThree, dist_cvMul]
  exact hu

theorem sphereFour_cvMul
    {v w : CVert} (hw : w ∈ sphereFour v) (s : Shat) :
    cvMul w s ∈ sphereFour (cvMul v s) :=
  ⟨dist_eq_two_cvMul hw.1 s, (labelFour_cvMul v w s).2 hw.2⟩

theorem mem_sphereFour_of_cvMul
    {v w : CVert} {s : Shat} (hv : cvMul v s = v)
    (hw : w ∈ sphereFour v) : cvMul w s ∈ sphereFour v := by
  have h := sphereFour_cvMul hw s
  rwa [hv] at h

theorem not_mem_sphereFour_of_cvMul
    {v w : CVert} {s : Shat} (hv : cvMul v s = v)
    (hw : w ∉ sphereFour v) : cvMul w s ∉ sphereFour v := by
  intro h
  apply hw
  have hv' : cvMul v s⁻¹ = v := by
    conv_lhs => rw [← hv]
    rw [cvMul_inv_cancel]
  have h' := mem_sphereFour_of_cvMul hv' h
  rwa [cvMul_inv_cancel] at h'

end CFSG.Monster.B.TwoA.Amalgam
