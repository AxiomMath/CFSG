module

public import CFSG.RankThree.GF2n.Smith81.S81TFin

public section

namespace CFSG.RankThree.GF2n.Smith81.MinuscT

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley


@[expose] def S5x : List Rt := [![2,2,3,4,3,2,1]]
@[expose] def S5y : List Rt := [![1,1,2,3,3,2,1], ![1,2,2,3,2,2,1]]
@[expose] def S5z : List Rt := [![1,2,2,3,2,1,0], ![1,1,2,2,2,2,1], ![1,1,2,3,2,1,1]]
@[expose] def S5u : List Rt := [![1,1,1,2,2,1,1], ![1,1,2,2,1,1,1], ![0,1,1,2,2,2,1]]
@[expose] def S5v : List Rt := [![1,2,2,3,2,1,0], ![1,1,1,2,2,1,1], ![1,1,2,2,1,1,1], ![0,1,1,2,2,2,1]]

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
theorem k12_5z : K12Cond okD5 inL5 S5z := by
  unfold K12Cond StarProp Star2Prop Two NoMixed CliqueOK A2list inM inMtop
  decide +kernel

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
theorem k12_5x : K12Cond okD5 inL5 S5x := by
  unfold K12Cond StarProp Star2Prop Two NoMixed CliqueOK A2list inM inMtop
  decide +kernel

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
theorem k12_5y : K12Cond okD5 inL5 S5y := by
  unfold K12Cond StarProp Star2Prop Two NoMixed CliqueOK A2list inM inMtop
  decide +kernel

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
theorem k3_5u : K3Cond okD5 inL5 S5u := by
  unfold K3Cond
  decide +kernel

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
theorem k3_5v : K3Cond okD5 inL5 S5v := by
  unfold K3Cond
  decide +kernel

@[expose] def e5Reps : List (List Rt) := [S5x, S5y, S5z, S5u, S5v]

theorem e5Reps_cond : ∀ S ∈ e5Reps, K12Cond okD5 inL5 S ∨ K3Cond okD5 inL5 S := by
  intro S hS
  simp only [e5Reps, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl k12_5x
  · exact Or.inl k12_5y
  · exact Or.inl k12_5z
  · exact Or.inr k3_5u
  · exact Or.inr k3_5v

end CFSG.RankThree.GF2n.Smith81.MinuscT
