module

public import CFSG.RankThree.GF2n.Smith81.S81TFin

public section

namespace CFSG.RankThree.GF2n.Smith81.MinuscT

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley


@[expose] def S4a2 : List Rt := [![0,1,0,0,0,0,0]]
@[expose] def S4c2 : List Rt := [![0,0,1,0,0,0,0], ![0,1,0,0,0,0,0]]
@[expose] def S4a4 : List Rt := [![0,1,1,1,0,0,0], ![0,1,0,1,1,0,0]]
@[expose] def S4c4 : List Rt := [![0,0,1,0,0,0,0], ![0,1,1,2,1,0,0], ![0,1,0,0,0,0,0]]
@[expose] def S4a6I : List Rt := [![0,0,1,0,0,0,0], ![0,1,1,2,2,1,0], ![0,1,1,2,1,1,1]]
@[expose] def S4a6II : List Rt := [![0,1,0,0,0,0,0], ![0,0,0,0,1,0,0], ![0,0,0,0,0,0,1]]
@[expose] def S4c6 : List Rt := [![0,1,0,0,0,0,0], ![0,0,1,0,0,0,0], ![0,0,0,0,1,0,0], ![0,0,0,0,0,0,1]]

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
theorem k12_4a4 : K12Cond okD4 inL4 S4a4 := by
  unfold K12Cond StarProp Star2Prop Two NoMixed CliqueOK A2list inM inMtop
  decide +kernel

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
theorem k12_4a2 : K12Cond okD4 inL4 S4a2 := by
  unfold K12Cond StarProp Star2Prop Two NoMixed CliqueOK A2list inM inMtop
  decide +kernel

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
theorem k12_4c2 : K12Cond okD4 inL4 S4c2 := by
  unfold K12Cond StarProp Star2Prop Two NoMixed CliqueOK A2list inM inMtop
  decide +kernel

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
theorem k12_4c4 : K12Cond okD4 inL4 S4c4 := by
  unfold K12Cond StarProp Star2Prop Two NoMixed CliqueOK A2list inM inMtop
  decide +kernel

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
theorem k12_4a6I : K12Cond okD4 inL4 S4a6I := by
  unfold K12Cond StarProp Star2Prop Two NoMixed CliqueOK A2list inM inMtop
  decide +kernel

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
theorem k3_4a6II : K3Cond okD4 inL4 S4a6II := by
  unfold K3Cond
  decide +kernel

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
theorem k3_4c6 : K3Cond okD4 inL4 S4c6 := by
  unfold K3Cond
  decide +kernel

@[expose] def e4Reps : List (List Rt) := [S4a2, S4c2, S4a4, S4c4, S4a6I, S4a6II, S4c6]

theorem e4Reps_cond : ∀ S ∈ e4Reps, K12Cond okD4 inL4 S ∨ K3Cond okD4 inL4 S := by
  intro S hS
  simp only [e4Reps, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl k12_4a2
  · exact Or.inl k12_4c2
  · exact Or.inl k12_4a4
  · exact Or.inl k12_4c4
  · exact Or.inl k12_4a6I
  · exact Or.inr k3_4a6II
  · exact Or.inr k3_4c6

end CFSG.RankThree.GF2n.Smith81.MinuscT
