module

public import CFSG.RankThree.GF2n.Smith81.S81TFin
public import CFSG.RankThree.GF2n.Smith81.S81TFast

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

@[expose] def S4a4R : List TFast.R5 := [
    (143169944, 144432467110006792, 59, 36099234751841793, 14),
    (143235224, 144432398390792200, 59, 36064187818182146, 14)]

@[expose] def S4a4G : List TFast.R5 := [
    (143165592, 144432398256312328, 57, 36099303336839170, 15),
    (143169672, 144397214018441224, 57, 36099235019751938, 13),
    (159942792, 144397213884223497, 57, 72092916117931010, 15),
    (143169688, 144432398390530056, 58, 36099234885535234, 14),
    (143161480, 144397213750005768, 55, 36099371922359810, 15),
    (142117000, 144397213884222984, 55, 54043401955836930, 14),
    (126388360, 144397213884223495, 55, 105690824180738, 13),
    (143169944, 144432467110006792, 59, 36099234751841793, 14),
    (143235224, 144432398390792200, 59, 36064187818182146, 14),
    (143235464, 144397282738180104, 59, 36064187818705409, 13),
    (142051464, 144397213883960840, 54, 54078449023190018, 14),
    (125339784, 144397213884222983, 54, 18049789308961794, 13),
    (143235480, 144432467110268936, 60, 36064187684488705, 14),
    (144283800, 144432398390792712, 60, 18120089333401090, 14),
    (143095688, 144397145030266888, 53, 36134419123406339, 15),
    (142047368, 144397213749743112, 53, 54078517474493954, 15),
    (125274248, 144397213883960839, 53, 18084836376314882, 13),
    (143239576, 144432467244486664, 61, 36064119233184769, 13),
    (144284056, 144432467110269448, 61, 18120089199707649, 14),
    (161061016, 144432398390792713, 61, 54113701980276226, 15),
    (142047112, 144397145030266376, 52, 54078517608187395, 15),
    (125270152, 144397213749743111, 52, 18084904827618818, 14),
    (144288152, 144432467244487176, 62, 18120020748403713, 13),
    (161061272, 144432467110269449, 62, 54113701846582785, 15),
    (125269896, 144397145030266375, 51, 18084904961312259, 14),
    (144353688, 144432467244749320, 63, 18084973681050625, 13),
    (161065368, 144432467244487177, 63, 54113633395278849, 14),
    (161130904, 144432467244749321, 64, 54078586327925761, 14),
    (162179480, 144432467244749833, 65, 36134487843144705, 14),
    (124151672, 144361960523697159, 47, 36064119098967043, 14)]

@[expose] def S4a4A : List (Fin 126) := [
    1, 3, 6, 10, 23, 24, 26, 37, 38, 50, 51, 52, 64, 65, 75, 76, 85, 93]

theorem S4a4R_eq : S4a4 = S4a4R.map fun s => decodeVec s.1 := by
  decide +kernel

theorem S4a4R_mem : ∀ s ∈ S4a4R, s ∈ TFast.tRecs := by
  decide +kernel

theorem S4a4G_eq : TFast.tRecs.filter (fun y => TFast.okc4 y.1 && TFast.asc S4a4R y) = S4a4G := by
  decide +kernel

theorem S4a4A_eq : TFast.tRecs.filter (TFast.A2c TFast.okc4 TFast.okdc4 S4a4R S4a4G) = S4a4A.map TFast.g := by
  decide +kernel

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
theorem k12_4a4_rest : TFast.K12CondA inL4 (S4a4A.map rt) S4a4 okD4 := by
  unfold TFast.K12CondA StarProp Star2Prop Two NoMixed CliqueOK inM inMtop
  decide +kernel

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
theorem k12_4a4 : K12Cond okD4 inL4 S4a4 :=
  TFast.K12Cond_of (TFast.A2list_eq S4a4R_eq S4a4R_mem TFast.hok4 TFast.hokd4 S4a4G_eq S4a4A S4a4A_eq)
    k12_4a4_rest

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

@[expose] def S4c4R : List TFast.R5 := [
    (143165832, 144397282603700232, 57, 36099303337362433, 14),
    (143239576, 144432467244486664, 61, 36064119233184769, 13),
    (143165592, 144432398256312328, 57, 36099303336839170, 15)]

@[expose] def S4c4G : List TFast.R5 := [
    (143165592, 144432398256312328, 57, 36099303336839170, 15),
    (143165832, 144397282603700232, 57, 36099303337362433, 14),
    (143231112, 144397213884485640, 57, 36064256403702786, 14),
    (159942792, 144397213884223497, 57, 72092916117931010, 15),
    (143100040, 144397213883961352, 55, 36134350538408962, 14),
    (142117000, 144397213884222984, 55, 54043401955836930, 14),
    (126388360, 144397213884223495, 55, 105690824180738, 13),
    (143169944, 144432467110006792, 59, 36099234751841793, 14),
    (142051464, 144397213883960840, 54, 54078449023190018, 14),
    (125339784, 144397213884222983, 54, 18049789308961794, 13),
    (143235480, 144432467110268936, 60, 36064187684488705, 14),
    (142047368, 144397213749743112, 53, 54078517474493954, 15),
    (125274248, 144397213883960839, 53, 18084836376314882, 13),
    (143239576, 144432467244486664, 61, 36064119233184769, 13),
    (144284056, 144432467110269448, 61, 18120089199707649, 14),
    (125270152, 144397213749743111, 52, 18084904827618818, 14),
    (144288152, 144432467244487176, 62, 18120020748403713, 13),
    (161061272, 144432467110269449, 62, 54113701846582785, 15),
    (144353688, 144432467244749320, 63, 18084973681050625, 13),
    (161065368, 144432467244487177, 63, 54113633395278849, 14),
    (161130904, 144432467244749321, 64, 54078586327925761, 14),
    (162179480, 144432467244749833, 65, 36134487843144705, 14),
    (124151672, 144361960523697159, 47, 36064119098967043, 14)]

@[expose] def S4c4A : List (Fin 126) := [
    4, 6, 23, 37, 50, 51, 64, 65, 75, 76, 85, 93]

theorem S4c4R_eq : S4c4 = S4c4R.map fun s => decodeVec s.1 := by
  decide +kernel

theorem S4c4R_mem : ∀ s ∈ S4c4R, s ∈ TFast.tRecs := by
  decide +kernel

theorem S4c4G_eq : TFast.tRecs.filter (fun y => TFast.okc4 y.1 && TFast.asc S4c4R y) = S4c4G := by
  decide +kernel

theorem S4c4A_eq : TFast.tRecs.filter (TFast.A2c TFast.okc4 TFast.okdc4 S4c4R S4c4G) = S4c4A.map TFast.g := by
  decide +kernel

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
theorem k12_4c4_rest : TFast.K12CondA inL4 (S4c4A.map rt) S4c4 okD4 := by
  unfold TFast.K12CondA StarProp Star2Prop Two NoMixed CliqueOK inM inMtop
  decide +kernel

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
theorem k12_4c4 : K12Cond okD4 inL4 S4c4 :=
  TFast.K12Cond_of (TFast.A2list_eq S4c4R_eq S4c4R_mem TFast.hok4 TFast.hokd4 S4c4G_eq S4c4A S4c4A_eq)
    k12_4c4_rest

@[expose] def S4a6IR : List TFast.R5 := [
    (143165832, 144397282603700232, 57, 36099303337362433, 14),
    (144353688, 144432467244749320, 63, 18084973681050625, 13),
    (161065368, 144432467244487177, 63, 54113633395278849, 14)]

@[expose] def S4a6IG : List TFast.R5 := [
    (143165592, 144432398256312328, 57, 36099303336839170, 15),
    (143165832, 144397282603700232, 57, 36099303337362433, 14),
    (144214152, 144397213884224008, 57, 18155204986274818, 14),
    (143165560, 144362029512134664, 55, 36099303605272578, 13),
    (143169928, 144397282737917960, 58, 36099234886058497, 13),
    (142117000, 144397213884222984, 55, 54043401955836930, 14),
    (143169944, 144432467110006792, 59, 36099234751841793, 14),
    (143235464, 144397282738180104, 59, 36064187818705409, 13),
    (161056904, 144397213884486153, 59, 54113770565796866, 15),
    (143235480, 144432467110268936, 60, 36064187684488705, 14),
    (144284040, 144397282738180616, 60, 18120089333924353, 13),
    (125274248, 144397213883960839, 53, 18084836376314882, 13),
    (143239576, 144432467244486664, 61, 36064119233184769, 13),
    (144284056, 144432467110269448, 61, 18120089199707649, 14),
    (161061256, 144397282738180617, 61, 54113701980799489, 14),
    (144288152, 144432467244487176, 62, 18120020748403713, 13),
    (161061272, 144432467110269449, 62, 54113701846582785, 15),
    (144353688, 144432467244749320, 63, 18084973681050625, 13),
    (161065368, 144432467244487177, 63, 54113633395278849, 14),
    (161130904, 144432467244749321, 64, 54078586327925761, 14),
    (162179480, 144432467244749833, 65, 36134487843144705, 14)]

@[expose] def S4a6IA : List (Fin 126) := [
    1, 5, 12, 23, 26, 30, 37, 40, 50, 51, 54, 64, 65, 85, 93]

theorem S4a6IR_eq : S4a6I = S4a6IR.map fun s => decodeVec s.1 := by
  decide +kernel

theorem S4a6IR_mem : ∀ s ∈ S4a6IR, s ∈ TFast.tRecs := by
  decide +kernel

theorem S4a6IG_eq : TFast.tRecs.filter (fun y => TFast.okc4 y.1 && TFast.asc S4a6IR y) = S4a6IG := by
  decide +kernel

theorem S4a6IA_eq : TFast.tRecs.filter (TFast.A2c TFast.okc4 TFast.okdc4 S4a6IR S4a6IG) = S4a6IA.map TFast.g := by
  decide +kernel

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
theorem k12_4a6I_rest : TFast.K12CondA inL4 (S4a6IA.map rt) S4a6I okD4 := by
  unfold TFast.K12CondA StarProp Star2Prop Two NoMixed CliqueOK inM inMtop
  decide +kernel

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
theorem k12_4a6I : K12Cond okD4 inL4 S4a6I :=
  TFast.K12Cond_of (TFast.A2list_eq S4a6IR_eq S4a6IR_mem TFast.hok4 TFast.hokd4 S4a6IG_eq S4a6IA S4a6IA_eq)
    k12_4a6I_rest

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
