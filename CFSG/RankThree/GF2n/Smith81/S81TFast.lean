module

public import CFSG.RankThree.GF2n.Smith81.S81TFin
public import CFSG.RankThree.GF2n.Smith81.S81E7Fast

public section

namespace CFSG.RankThree.GF2n.Smith81.TFast

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7Fast CFSG.RankThree.GF2n.Smith81.MinuscT

@[expose] def tdig (r j : ℕ) : ℕ := twP j r + 2 - twN j r

@[expose] def twOK (r : ℕ) : Bool :=
  (List.range 7).all fun j => Nat.ble (twN j r) (twP j r + 2) && Nat.ble (twP j r) (twN j r + 2)

@[expose] def TE (r : ℕ) : ℕ :=
  tdig r 0 + tdig r 1 * 512 + tdig r 2 * 512 ^ 2 + tdig r 3 * 512 ^ 3 + tdig r 4 * 512 ^ 4 +
    tdig r 5 * 512 ^ 5 + tdig r 6 * 512 ^ 6

@[expose] def ST (r : ℕ) : ℕ :=
  tdig r 0 + tdig r 1 + tdig r 2 + tdig r 3 + tdig r 4 + tdig r 5 + tdig r 6

abbrev R5 : Type := ℕ × ℕ × ℕ × ℕ × ℕ

@[expose] def trec (r : ℕ) : R5 := (r, RE r, SR r, TE r, ST r)

abbrev g (k : Fin 126) : R5 := trec ((Tag.rootCertificate .E7).roots.getD k 0)

@[expose] def tRecs : List R5 := [
    (143165577, 162411612393705480, 57, 36099303470793732, 15),
    (143165592, 144432398256312328, 57, 36099303336839170, 15),
    (143165832, 144397282603700232, 57, 36099303337362433, 14),
    (143169672, 144397214018441224, 57, 36099235019751938, 13),
    (143231112, 144397213884485640, 57, 36064256403702786, 14),
    (144214152, 144397213884224008, 57, 18155204986274818, 14),
    (159942792, 144397213884223497, 57, 72092916117931010, 15),
    (143165575, 126382815374741512, 55, 36099303471318016, 13),
    (143165833, 162411681113182216, 58, 36099303337100291, 15),
    (143165560, 144362029512134664, 55, 36099303605272578, 13),
    (143169688, 144432398390530056, 58, 36099234885535234, 14),
    (143165320, 144397145164746760, 55, 36099303604749315, 14),
    (143169928, 144397282737917960, 58, 36099234886058497, 13),
    (143161480, 144397213750005768, 55, 36099371922359810, 15),
    (143235208, 144397214018703368, 58, 36064187952398850, 13),
    (143100040, 144397213883961352, 55, 36134350538408962, 14),
    (144279688, 144397213884486152, 58, 18120157918921730, 14),
    (142117000, 144397213884222984, 55, 54043401955836930, 14),
    (160991368, 144397213884224009, 58, 54148817633149954, 15),
    (126388360, 144397213884223495, 55, 105690824180738, 13),
    (143165319, 126382746655264776, 54, 36099303605011457, 13),
    (143169929, 162411681247399944, 59, 36099234885796355, 14),
    (143161464, 144362029377916936, 54, 36099372056576514, 14),
    (143169944, 144432467110006792, 59, 36099234751841793, 14),
    (143235224, 144432398390792200, 59, 36064187818182146, 14),
    (143161224, 144397145030529032, 54, 36099372056053251, 15),
    (143235464, 144397282738180104, 59, 36064187818705409, 13),
    (143095944, 144397213749743624, 54, 36134418989712898, 15),
    (144283784, 144397214018703880, 59, 18120089467617794, 13),
    (142051464, 144397213883960840, 54, 54078449023190018, 14),
    (161056904, 144397213884486153, 59, 54113770565796866, 15),
    (125339784, 144397213884222983, 54, 18049789308961794, 13),
    (143161223, 126382746521047048, 53, 36099372056315393, 14),
    (143169945, 162446865619488776, 60, 36099234751579651, 15),
    (143235465, 162411681247662088, 60, 36064187818443267, 14),
    (143161208, 144361960658440200, 53, 36099372190269955, 14),
    (143095928, 144362029377654792, 53, 36134419123929602, 14),
    (143235480, 144432467110268936, 60, 36064187684488705, 14),
    (144283800, 144432398390792712, 60, 18120089333401090, 14),
    (143095688, 144397145030266888, 53, 36134419123406339, 15),
    (144284040, 144397282738180616, 60, 18120089333924353, 13),
    (142047368, 144397213749743112, 53, 54078517474493954, 15),
    (161061000, 144397214018703881, 60, 54113702114492930, 14),
    (125274248, 144397213883960839, 53, 18084836376314882, 13),
    (143161207, 126347562148958216, 52, 36099372190532097, 13),
    (143095687, 126382746520784904, 52, 36134419123668481, 14),
    (143235481, 162446865619750920, 61, 36064187684226563, 15),
    (144284041, 162411681247662600, 61, 18120089333662211, 14),
    (143095672, 144361960658178056, 52, 36134419257623043, 14),
    (142047352, 144362029377654280, 52, 54078517608710658, 14),
    (143239576, 144432467244486664, 61, 36064119233184769, 13),
    (144284056, 144432467110269448, 61, 18120089199707649, 14),
    (161061016, 144432398390792713, 61, 54113701980276226, 15),
    (142047112, 144397145030266376, 52, 54078517608187395, 15),
    (161061256, 144397282738180617, 61, 54113701980799489, 14),
    (125270152, 144397213749743111, 52, 18084904827618818, 14),
    (143095671, 126347562148696072, 51, 36134419257885185, 13),
    (142047111, 126382746520784392, 51, 54078517608449537, 14),
    (143239577, 162446865753968648, 62, 36064119232922627, 14),
    (144284057, 162446865619751432, 62, 18120089199445507, 15),
    (161061257, 162411681247662601, 62, 54113701980537347, 15),
    (143091576, 144361960523960328, 51, 36134487708926979, 15),
    (142047096, 144361960658177544, 51, 54078517742404099, 14),
    (125270136, 144362029377654279, 51, 18084904961835522, 13),
    (144288152, 144432467244487176, 62, 18120020748403713, 13),
    (161061272, 144432467110269449, 62, 54113701846582785, 15),
    (125269896, 144397145030266375, 51, 18084904961312259, 14),
    (143091575, 126347562014478344, 50, 36134487709189121, 14),
    (142047095, 126347562148695560, 50, 54078517742666241, 13),
    (125269895, 126382746520784391, 50, 18084904961574401, 13),
    (143239833, 162446934473445384, 63, 36064119099229186, 14),
    (144288153, 162446865753969160, 63, 18120020748141571, 14),
    (161061273, 162446865619751433, 63, 54113701846320643, 16),
    (142043000, 144361960523959816, 50, 54078586193708035, 15),
    (125269880, 144361960658177543, 50, 18084905095528963, 13),
    (144353688, 144432467244749320, 63, 18084973681050625, 13),
    (161065368, 144432467244487177, 63, 54113633395278849, 14),
    (143091319, 126347493295001608, 49, 36134487842882562, 14),
    (142042999, 126347562014477832, 49, 54078586193970177, 14),
    (125269879, 126347562148695559, 49, 18084905095791105, 12),
    (144288409, 162446934473445896, 64, 18120020614448130, 14),
    (144353689, 162446865754231304, 64, 18084973680788483, 14),
    (161065369, 162446865753969161, 64, 54113633395016707, 15),
    (141977464, 144361960523697672, 49, 54113633261061123, 15),
    (125265784, 144361960523959815, 49, 18084973546832899, 14),
    (161130904, 144432467244749321, 64, 54078586327925761, 14),
    (142042743, 126347493295001096, 48, 54078586327663618, 14),
    (141977463, 126347562014215688, 48, 54113633261323265, 14),
    (125265783, 126347562014477831, 48, 18084973547095041, 13),
    (144353945, 162446934473708040, 65, 18084973547095042, 14),
    (161065625, 162446934473445897, 65, 54113633261323266, 15),
    (161130905, 162446865754231305, 65, 54078586327663619, 15),
    (125200248, 144361960523697671, 48, 18120020614185987, 14),
    (162179480, 144432467244749833, 65, 36134487843144705, 14),
    (141977207, 126347493294738952, 47, 54113633395016706, 14),
    (125265527, 126347493295001095, 47, 18084973680788482, 13),
    (125200247, 126347562014215687, 47, 18120020614448129, 13),
    (144358041, 162446934607925768, 66, 18084905095791106, 13),
    (161131161, 162446934473708041, 66, 54078586193970178, 15),
    (162179481, 162446865754231817, 66, 36134487842882563, 15),
    (124151672, 144361960523697159, 47, 36064119098967043, 14),
    (141973111, 126347493160521224, 46, 54113701846320642, 15),
    (125199991, 126347493294738951, 46, 18120020748141570, 13),
    (124151671, 126347562014215175, 46, 36064119099229185, 13),
    (144358057, 162482118980014600, 67, 18084904961574402, 14),
    (161135257, 162446934607925769, 67, 54078517742666242, 14),
    (162179737, 162446934473708553, 67, 36134487709189122, 15),
    (141973095, 126312308788432392, 45, 54113701980537346, 14),
    (125195895, 126347493160521223, 45, 18120089199445506, 14),
    (124151415, 126347493294738439, 45, 36064119232922626, 13),
    (161135273, 162482118980014601, 68, 54078517608449538, 15),
    (162183833, 162446934607926281, 68, 36134419257885186, 14),
    (125195879, 126312308788432391, 44, 18120089333662210, 13),
    (124147319, 126347493160520711, 44, 36064187684226562, 14),
    (162183849, 162482118980015113, 69, 36134419123668482, 15),
    (162249369, 162446934608188425, 69, 36099372190532098, 14),
    (124147303, 126312308788431879, 43, 36064187818443266, 13),
    (124081783, 126347493160258567, 43, 36099234751579650, 14),
    (162249385, 162482118980277257, 70, 36099372056315394, 15),
    (124081767, 126312308788169735, 42, 36099234885796354, 13),
    (162253481, 162482119114494985, 71, 36099303605011458, 14),
    (124077671, 126312308653952007, 41, 36099303337100290, 14),
    (162253737, 162482187833971721, 72, 36099303471318017, 14),
    (124077415, 126312239934475271, 40, 36099303470793731, 14),
    (162253738, 180496586343453705, 73, 36099303471055875, 15),
    (124077414, 108297841424993287, 39, 36099303471055873, 13)]

theorem tRecs_eq : tRecs = (Tag.rootCertificate .E7).roots.map trec := by
  decide +kernel

theorem roots_twOK : (Tag.rootCertificate .E7).roots.all twOK = true := by
  decide +kernel

theorem roots_eq_map : (Tag.rootCertificate .E7).roots =
    (List.finRange 126).map fun k : Fin 126 => (Tag.rootCertificate .E7).roots.getD (k : ℕ) 0 := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_finRange, roots_length]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_finRange]
    simp only [Fin.cast_mk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
      Option.getD_some]

theorem tRecs_eq_map : tRecs = (List.finRange 126).map g := by
  rw [tRecs_eq, roots_eq_map, List.map_map]
  rfl

theorem g_mem (k : Fin 126) : g k ∈ tRecs := by
  rw [tRecs_eq_map]
  exact List.mem_map_of_mem (List.mem_finRange k)

theorem exists_of_mem_tRecs {y : R5} (h : y ∈ tRecs) : ∃ k : Fin 126, y = g k := by
  rw [tRecs_eq_map, List.mem_map] at h
  obtain ⟨k, -, rfl⟩ := h
  exact ⟨k, rfl⟩

theorem twOK_rc (k : Fin 126) : twOK ((Tag.rootCertificate .E7).roots.getD k 0) = true :=
  List.all_eq_true.1 roots_twOK _ (getD_root_mem k)

theorem rt_eq (k : Fin 126) : rt k = decodeVec (g k).1 := root_eq k

theorem extract7' (x0 x1 x2 x3 x4 x5 x6 y0 y1 y2 y3 y4 y5 y6 : ℕ)
    (hx0 : x0 < 5) (hx1 : x1 < 5) (hx2 : x2 < 5) (hx3 : x3 < 5) (hx4 : x4 < 5) (hx5 : x5 < 5)
    (hx6 : x6 < 5) (hy0 : y0 < 16) (hy1 : y1 < 16) (hy2 : y2 < 16) (hy3 : y3 < 16)
    (hy4 : y4 < 16) (hy5 : y5 < 16) (hy6 : y6 < 16) :
    (x0 + x1 * 512 + x2 * 512 ^ 2 + x3 * 512 ^ 3 + x4 * 512 ^ 4 + x5 * 512 ^ 5 + x6 * 512 ^ 6) *
      (y6 + y5 * 512 + y4 * 512 ^ 2 + y3 * 512 ^ 3 + y2 * 512 ^ 4 + y1 * 512 ^ 5 + y0 * 512 ^ 6)
      / 512 ^ 6 % 512 =
    x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3 + x4 * y4 + x5 * y5 + x6 * y6 := by
  have b : ∀ {x y : ℕ}, x < 5 → y < 16 → x * y ≤ 60 := fun hx hy =>
    Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)
  have e : (x0 + x1 * 512 + x2 * 512 ^ 2 + x3 * 512 ^ 3 + x4 * 512 ^ 4 + x5 * 512 ^ 5 +
      x6 * 512 ^ 6) *
      (y6 + y5 * 512 + y4 * 512 ^ 2 + y3 * 512 ^ 3 + y2 * 512 ^ 4 + y1 * 512 ^ 5 + y0 * 512 ^ 6) =
      (x0 * y6 + (x0 * y5 + x1 * y6) * 512 + (x0 * y4 + x1 * y5 + x2 * y6) * 512 ^ 2 +
        (x0 * y3 + x1 * y4 + x2 * y5 + x3 * y6) * 512 ^ 3 +
        (x0 * y2 + x1 * y3 + x2 * y4 + x3 * y5 + x4 * y6) * 512 ^ 4 +
        (x0 * y1 + x1 * y2 + x2 * y3 + x3 * y4 + x4 * y5 + x5 * y6) * 512 ^ 5) +
      (x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3 + x4 * y4 + x5 * y5 + x6 * y6) * 512 ^ 6 +
      ((x1 * y0 + x2 * y1 + x3 * y2 + x4 * y3 + x5 * y4 + x6 * y5) +
        (x2 * y0 + x3 * y1 + x4 * y2 + x5 * y3 + x6 * y4) * 512 +
        (x3 * y0 + x4 * y1 + x5 * y2 + x6 * y3) * 512 ^ 2 + (x4 * y0 + x5 * y1 + x6 * y2) * 512 ^ 3 +
        (x5 * y0 + x6 * y1) * 512 ^ 4 + x6 * y0 * 512 ^ 5) * 512 ^ 7 := by ring
  rw [e]
  have := b hx0 hy0; have := b hx0 hy1; have := b hx0 hy2; have := b hx0 hy3; have := b hx0 hy4
  have := b hx0 hy5; have := b hx0 hy6
  have := b hx1 hy1; have := b hx1 hy2; have := b hx1 hy3; have := b hx1 hy4; have := b hx1 hy5
  have := b hx1 hy6
  have := b hx2 hy2; have := b hx2 hy3; have := b hx2 hy4; have := b hx2 hy5; have := b hx2 hy6
  have := b hx3 hy3; have := b hx3 hy4; have := b hx3 hy5; have := b hx3 hy6
  have := b hx4 hy4; have := b hx4 hy5; have := b hx4 hy6
  have := b hx5 hy5; have := b hx5 hy6; have := b hx6 hy6
  omega

@[expose] def ipP (x y : R5) : ℕ := x.2.2.2.1 * y.2.1 / 512 ^ 6 % 512 + 112
@[expose] def ipN (x y : R5) : ℕ := 2 * y.2.2.1 + 8 * x.2.2.2.2

theorem tdig_cast {r j : ℕ} (h1 : twN j r ≤ twP j r + 2) :
    (tdig r j : ℤ) = (twP j r : ℤ) - (twN j r : ℤ) + 2 := by
  unfold tdig
  omega

theorem twOK_spec {r : ℕ} (h : twOK r = true) (j : ℕ) (hj : j < 7) :
    twN j r ≤ twP j r + 2 ∧ twP j r ≤ twN j r + 2 := by
  have := List.all_eq_true.1 h j (List.mem_range.2 hj)
  simpa only [Bool.and_eq_true, Nat.ble_eq] using this

theorem ipR_trec (r c : ℕ) (h : twOK r = true) :
    ipR (decodeVec r) (decodeVec c) = (ipP (trec r) (trec c) : ℤ) - (ipN (trec r) (trec c) : ℤ) := by
  have h0 := twOK_spec h 0 (by norm_num)
  have h1 := twOK_spec h 1 (by norm_num)
  have h2 := twOK_spec h 2 (by norm_num)
  have h3 := twOK_spec h 3 (by norm_num)
  have h4 := twOK_spec h 4 (by norm_num)
  have h5 := twOK_spec h 5 (by norm_num)
  have h6 := twOK_spec h 6 (by norm_num)
  have t0 := toWeight_decodeVec r 0
  have t1 := toWeight_decodeVec r 1
  have t2 := toWeight_decodeVec r 2
  have t3 := toWeight_decodeVec r 3
  have t4 := toWeight_decodeVec r 4
  have t5 := toWeight_decodeVec r 5
  have t6 := toWeight_decodeVec r 6
  have hx : ∀ j, j < 7 → tdig r j < 5 := fun j hj => by
    have := twOK_spec h j hj
    unfold tdig
    omega
  have ex := extract7' (tdig r 0) (tdig r 1) (tdig r 2) (tdig r 3) (tdig r 4) (tdig r 5)
    (tdig r 6) (rd c 0) (rd c 1) (rd c 2) (rd c 3) (rd c 4) (rd c 5) (rd c 6)
    (hx 0 (by norm_num)) (hx 1 (by norm_num)) (hx 2 (by norm_num)) (hx 3 (by norm_num))
    (hx 4 (by norm_num)) (hx 5 (by norm_num)) (hx 6 (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num))
  have c0 := tdig_cast h0.1
  have c1 := tdig_cast h1.1
  have c2 := tdig_cast h2.1
  have c3 := tdig_cast h3.1
  have c4 := tdig_cast h4.1
  have c5 := tdig_cast h5.1
  have c6 := tdig_cast h6.1
  show (∑ j : Fin 7, MinData.toWeight (decodeVec (τ := .E7) r) j * decodeVec (τ := .E7) c j) = _
  rw [Fin.sum_univ_seven]
  rw [t0, t1, t2, t3, t4, t5, t6]
  simp only [ipP, ipN, trec, TE, RE, SR, ST]
  rw [ex]
  show ((twP 0 r : ℤ) - twN 0 r) * ((rd c 0 : ℕ) - 8) + ((twP 1 r : ℤ) - twN 1 r) * ((rd c 1 : ℕ) - 8) +
    ((twP 2 r : ℤ) - twN 2 r) * ((rd c 2 : ℕ) - 8) + ((twP 3 r : ℤ) - twN 3 r) * ((rd c 3 : ℕ) - 8) +
    ((twP 4 r : ℤ) - twN 4 r) * ((rd c 4 : ℕ) - 8) + ((twP 5 r : ℤ) - twN 5 r) * ((rd c 5 : ℕ) - 8) +
    ((twP 6 r : ℤ) - twN 6 r) * ((rd c 6 : ℕ) - 8) = _
  have d0 : (twP 0 r : ℤ) - twN 0 r = tdig r 0 - 2 := by rw [c0]; ring
  have d1 : (twP 1 r : ℤ) - twN 1 r = tdig r 1 - 2 := by rw [c1]; ring
  have d2 : (twP 2 r : ℤ) - twN 2 r = tdig r 2 - 2 := by rw [c2]; ring
  have d3 : (twP 3 r : ℤ) - twN 3 r = tdig r 3 - 2 := by rw [c3]; ring
  have d4 : (twP 4 r : ℤ) - twN 4 r = tdig r 4 - 2 := by rw [c4]; ring
  have d5 : (twP 5 r : ℤ) - twN 5 r = tdig r 5 - 2 := by rw [c5]; ring
  have d6 : (twP 6 r : ℤ) - twN 6 r = tdig r 6 - 2 := by rw [c6]; ring
  rw [d0, d1, d2, d3, d4, d5, d6]
  push_cast
  ring

theorem trec_of_mem {y : R5} (hy : y ∈ tRecs) : y = trec y.1 ∧ twOK y.1 = true := by
  obtain ⟨k, rfl⟩ := exists_of_mem_tRecs hy
  exact ⟨rfl, twOK_rc k⟩

theorem ipR_rec {y s : R5} (hy : y ∈ tRecs) (hs : s ∈ tRecs) :
    ipR (decodeVec y.1) (decodeVec s.1) = (ipP y s : ℤ) - (ipN y s : ℤ) := by
  obtain ⟨ey, hy'⟩ := trec_of_mem hy
  obtain ⟨es, -⟩ := trec_of_mem hs
  rw [ipR_trec _ _ hy', ← ey, ← es]

@[expose] def C8 : ℕ := 8 + 8 * 512 + 8 * 512 ^ 2 + 8 * 512 ^ 3 + 8 * 512 ^ 4 + 8 * 512 ^ 5 + 8 * 512 ^ 6

theorem pack_add_iff (a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 c0 c1 c2 c3 c4 c5 c6 : ℕ)
    (_ha0 : a0 < 16) (ha1 : a1 < 16) (ha2 : a2 < 16) (ha3 : a3 < 16) (ha4 : a4 < 16) (ha5 : a5 < 16)
    (ha6 : a6 < 16) (_hb0 : b0 < 16) (hb1 : b1 < 16) (hb2 : b2 < 16) (hb3 : b3 < 16)
    (hb4 : b4 < 16) (hb5 : b5 < 16) (hb6 : b6 < 16) (_hc0 : c0 < 16) (hc1 : c1 < 16)
    (hc2 : c2 < 16) (hc3 : c3 < 16) (hc4 : c4 < 16) (hc5 : c5 < 16) (hc6 : c6 < 16) :
    (a6 + a5 * 512 + a4 * 512 ^ 2 + a3 * 512 ^ 3 + a2 * 512 ^ 4 + a1 * 512 ^ 5 + a0 * 512 ^ 6) +
        (b6 + b5 * 512 + b4 * 512 ^ 2 + b3 * 512 ^ 3 + b2 * 512 ^ 4 + b1 * 512 ^ 5 + b0 * 512 ^ 6) =
      (c6 + c5 * 512 + c4 * 512 ^ 2 + c3 * 512 ^ 3 + c2 * 512 ^ 4 + c1 * 512 ^ 5 + c0 * 512 ^ 6) +
        C8 ↔
    a0 + b0 = c0 + 8 ∧ a1 + b1 = c1 + 8 ∧ a2 + b2 = c2 + 8 ∧ a3 + b3 = c3 + 8 ∧ a4 + b4 = c4 + 8 ∧
      a5 + b5 = c5 + 8 ∧ a6 + b6 = c6 + 8 := by
  unfold C8
  omega

theorem add_coord_iff (r1 r2 r : ℕ) (j : Fin 7) :
    (decodeVec (τ := .E7) r1 + decodeVec (τ := .E7) r2 : Fin 7 → ℤ) j = decodeVec (τ := .E7) r j ↔
      rd r1 j + rd r2 j = rd r j + 8 := by
  show ((rd r1 j : ℕ) : ℤ) - 8 + (((rd r2 j : ℕ) : ℤ) - 8) = ((rd r j : ℕ) : ℤ) - 8 ↔ _
  omega

theorem add_decode_iff (r1 r2 r : ℕ) :
    decodeVec (τ := .E7) r1 + decodeVec r2 = decodeVec r ↔ RE r1 + RE r2 = RE r + C8 := by
  unfold RE
  rw [pack_add_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)), funext_iff]
  constructor
  · intro h
    exact ⟨(add_coord_iff r1 r2 r 0).1 (h (0 : Fin 7)), (add_coord_iff r1 r2 r 1).1 (h (1 : Fin 7)),
      (add_coord_iff r1 r2 r 2).1 (h (2 : Fin 7)), (add_coord_iff r1 r2 r 3).1 (h (3 : Fin 7)),
      (add_coord_iff r1 r2 r 4).1 (h (4 : Fin 7)), (add_coord_iff r1 r2 r 5).1 (h (5 : Fin 7)),
      (add_coord_iff r1 r2 r 6).1 (h (6 : Fin 7))⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩ (j : Fin 7)
    rw [add_coord_iff]
    fin_cases j
    exacts [h0, h1, h2, h3, h4, h5, h6]

theorem isRoot_rtk (k : Fin 126) : IsRoot .E7 (rt k) :=
  RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) k (by rw [roots_length]; exact k.2)

theorem ipR_rt_of_add {k₁ k₂ k : Fin 126} (h : rt k₁ + rt k₂ = rt k) : ipR (rt k) (rt k₁) = 1 := by
  have e := form_add_self posDef_cartan_E7 (rt k₁) (rt k₂)
  rw [h, form_self_root posDef_cartan_E7 (isRoot_rtk k), form_self_root posDef_cartan_E7 (isRoot_rtk k₁),
    form_self_root posDef_cartan_E7 (isRoot_rtk k₂)] at e
  show MinData.toWeight (rt k) ⬝ᵥ rt k₁ = 1
  rw [← h, MinData.toWeight_add, add_dotProduct, form_self_root posDef_cartan_E7 (isRoot_rtk k₁),
    form_comm posDef_cartan_E7 (rt k₂) (rt k₁)]
  omega

theorem ipR_add_left (α β γ : Rt) : ipR (α + β) γ = ipR α γ + ipR β γ := by
  show MinData.toWeight (α + β) ⬝ᵥ γ = _
  rw [MinData.toWeight_add, add_dotProduct]

@[expose] def posc (r : ℕ) : Bool := (List.range 7).all fun i => Nat.ble 8 (rd r i)

theorem posR_iff (r : ℕ) : posR (decodeVec r) ↔ posc r = true := by
  unfold posR posc
  rw [List.all_eq_true]
  constructor
  · intro h i hi
    have hi' : i < 7 := List.mem_range.1 hi
    have := h ⟨i, hi'⟩
    have e : decodeVec (τ := .E7) r ⟨i, hi'⟩ = ((rd r i : ℕ) : ℤ) - 8 := rfl
    rw [e] at this
    rw [Nat.ble_eq]
    omega
  · intro h i
    have := h i (List.mem_range.2 i.2)
    have e : decodeVec (τ := .E7) r i = ((rd r i : ℕ) : ℤ) - 8 := rfl
    rw [e]
    rw [Nat.ble_eq] at this
    omega

@[expose] def asc (SR : List R5) (y : R5) : Bool := SR.all fun s => Nat.ble (ipN y s) (ipP y s)

@[expose] def perpc (SR : List R5) (y : R5) : Bool := SR.all fun s => ipP y s == ipN y s

@[expose] def cov (okdc : ℕ → ℕ → Bool) (SR GR : List R5) (y : R5) : Bool :=
  GR.any fun y1 => (ipP y y1 == ipN y y1 + 1) && okdc y.1 y1.1 &&
    (SR.all fun s => Nat.ble (ipP y1 s + ipN y s) (ipP y s + ipN y1 s)) &&
    GR.any fun y2 => y1.2.1 + y2.2.1 == y.2.1 + C8

@[expose] def A2c (okc : ℕ → Bool) (okdc : ℕ → ℕ → Bool) (SR GR : List R5) (y : R5) : Bool :=
  okc y.1 && posc y.1 && asc SR y && (perpc SR y || cov okdc SR GR y)

section Bridge

variable {S : List Rt} {SR : List R5} (hS : S = SR.map fun s => decodeVec s.1)
  (hSR : ∀ s ∈ SR, s ∈ tRecs)
include hS hSR

theorem inAS_iff {y : R5} (hy : y ∈ tRecs) : inAS S (decodeVec y.1) ↔ asc SR y = true := by
  unfold inAS asc
  rw [hS, List.forall_mem_map, List.all_eq_true]
  refine forall₂_congr fun s hs => ?_
  rw [ipR_rec hy (hSR s hs), Nat.ble_eq]
  omega

theorem inPerpS_iff {y : R5} (hy : y ∈ tRecs) :
    inPerpS S (decodeVec y.1) ↔ perpc SR y = true := by
  unfold inPerpS perpc
  rw [hS, List.forall_mem_map, List.all_eq_true]
  refine forall₂_congr fun s hs => ?_
  rw [ipR_rec hy (hSR s hs), beq_iff_eq]
  omega

variable {okD : Rt → Prop} [DecidablePred okD] {okc : ℕ → Bool}
  (hok : ∀ r, okD (decodeVec r) ↔ okc r = true) {okdc : ℕ → ℕ → Bool}
  (hokd : ∀ r r1 r2 : ℕ, decodeVec (τ := .E7) r1 + decodeVec r2 = decodeVec r →
    okD (decodeVec r2) → okdc r r1 = true)
  {GR : List R5} (hG : tRecs.filter (fun y => okc y.1 && asc SR y) = GR)
include hok hokd hG

omit [DecidablePred okD] hokd in
theorem mem_GR_iff (k : Fin 126) :
    g k ∈ GR ↔ okD (rt k) ∧ inAS S (rt k) := by
  rw [← hG, List.mem_filter, rt_eq, hok, inAS_iff hS hSR (g_mem k), Bool.and_eq_true]
  exact ⟨fun h => h.2, fun h => ⟨g_mem k, h⟩⟩

theorem cover1_iff (k : Fin 126) : cover1 okD S (rt k) ↔ cov okdc SR GR (g k) = true := by
  unfold cover1 cov
  constructor
  · rintro ⟨k₁, k₂, hsum, hok₁, hok₂, has₁, has₂⟩
    have hy₁ : g k₁ ∈ GR := (mem_GR_iff hS hSR hok hG k₁).2 ⟨hok₁, has₁⟩
    have hy₂ : g k₂ ∈ GR := (mem_GR_iff hS hSR hok hG k₂).2 ⟨hok₂, has₂⟩
    have hsum' := hsum
    rw [rt_eq, rt_eq, rt_eq] at hsum'
    refine List.any_eq_true.2 ⟨g k₁, hy₁, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, List.any_eq_true.2 ⟨g k₂, hy₂, ?_⟩⟩
    · have h1 := ipR_rt_of_add hsum
      rw [rt_eq, rt_eq, ipR_rec (g_mem k) (g_mem k₁)] at h1
      omega
    · rw [rt_eq] at hok₂
      exact hokd _ _ _ hsum' hok₂
    · rw [List.all_eq_true]
      intro s hs
      have hs' := hSR s hs
      have e := ipR_add_left (rt k₁) (rt k₂) (decodeVec s.1)
      rw [hsum] at e
      have h2 : 0 ≤ ipR (rt k₂) (decodeVec s.1) := by
        unfold inAS at has₂
        exact has₂ _ (by rw [hS]; exact List.mem_map_of_mem hs)
      rw [rt_eq, rt_eq, rt_eq, ipR_rec (g_mem k) hs', ipR_rec (g_mem k₁) hs',
        ipR_rec (g_mem k₂) hs'] at e
      rw [rt_eq, ipR_rec (g_mem k₂) hs'] at h2
      rw [Nat.ble_eq]
      omega
    · rw [beq_iff_eq]
      exact (add_decode_iff _ _ _).1 hsum'
  · intro h
    obtain ⟨y₁, hy₁, h⟩ := List.any_eq_true.1 h
    simp only [Bool.and_eq_true] at h
    obtain ⟨y₂, hy₂, h2⟩ := List.any_eq_true.1 h.2
    rw [beq_iff_eq] at h2
    have hm₁ := hy₁
    have hm₂ := hy₂
    rw [← hG, List.mem_filter] at hm₁ hm₂
    obtain ⟨k₁, rfl⟩ := exists_of_mem_tRecs hm₁.1
    obtain ⟨k₂, rfl⟩ := exists_of_mem_tRecs hm₂.1
    have e₁ := (mem_GR_iff hS hSR hok hG k₁).1 hy₁
    have e₂ := (mem_GR_iff hS hSR hok hG k₂).1 hy₂
    refine ⟨k₁, k₂, ?_, e₁.1, e₂.1, e₁.2, e₂.2⟩
    rw [rt_eq, rt_eq, rt_eq]
    exact (add_decode_iff _ _ _).2 h2

theorem A2pred_iff (k : Fin 126) :
    (okD (rt k) ∧ posR (rt k) ∧ inAS S (rt k) ∧ (cover1 okD S (rt k) ∨ inPerpS S (rt k))) ↔
      A2c okc okdc SR GR (g k) = true := by
  unfold A2c
  rw [cover1_iff hS hSR hok hokd hG k]
  rw [rt_eq, hok, posR_iff, inAS_iff hS hSR (g_mem k), inPerpS_iff hS hSR (g_mem k)]
  simp only [Bool.and_eq_true, Bool.or_eq_true]
  tauto

theorem A2list_eq (A2i : List (Fin 126))
    (hA : tRecs.filter (A2c okc okdc SR GR) = A2i.map g) : A2list okD S = A2i.map rt := by
  unfold A2list
  have hf : (List.finRange 126).filter (fun k => decide (okD (rt k) ∧ posR (rt k) ∧
      inAS S (rt k) ∧ (cover1 okD S (rt k) ∨ inPerpS S (rt k)))) =
      (List.finRange 126).filter (fun k => A2c okc okdc SR GR (g k)) := by
    apply List.filter_congr
    intro k _
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact A2pred_iff hS hSR hok hokd hG k
  have hrt : (rt : Fin 126 → Rt) = (fun y : R5 => decodeVec y.1) ∘ g := by
    funext k
    exact rt_eq k
  rw [hf, hrt, ← List.map_map, ← List.map_map (g := fun y : R5 => decodeVec y.1) (f := g)]
  congr 1
  show List.map g (List.filter (A2c okc okdc SR GR ∘ g) (List.finRange 126)) = _
  rw [← List.filter_map, ← tRecs_eq_map]
  exact hA

end Bridge

@[expose] def okc4 (r : ℕ) : Bool := r % 16 == 8
@[expose] def okdc4 (r r1 : ℕ) : Bool := r % 16 == r1 % 16
@[expose] def okc5 (_ : ℕ) : Bool := true
@[expose] def okdc5 (_ _ : ℕ) : Bool := true

theorem hok4 (r : ℕ) : okD4 (decodeVec r) ↔ okc4 r = true := by
  show ((r / 16 ^ (0 : ℕ) % 16 : ℕ) : ℤ) - 8 = 0 ↔ (r % 16 == 8) = true
  rw [beq_iff_eq, pow_zero, Nat.div_one]
  omega

theorem hokd4 (r r1 r2 : ℕ) (h : decodeVec (τ := .E7) r1 + decodeVec r2 = decodeVec r)
    (h2 : okD4 (decodeVec r2)) : okdc4 r r1 = true := by
  have e : r1 / 16 ^ 0 % 16 + r2 / 16 ^ 0 % 16 = r / 16 ^ 0 % 16 + 8 :=
    (add_coord_iff r1 r2 r 0).1 (congrFun h (0 : Fin 7))
  have e2 := (hok4 r2).1 h2
  unfold okc4 at e2
  unfold okdc4
  rw [beq_iff_eq] at e2 ⊢
  simp only [pow_zero, Nat.div_one] at e
  omega

theorem hok5 (r : ℕ) : okD5 (decodeVec r) ↔ okc5 r = true := ⟨fun _ => rfl, fun _ => trivial⟩

theorem hokd5 (r r1 r2 : ℕ) (_h : decodeVec (τ := .E7) r1 + decodeVec r2 = decodeVec r)
    (_h2 : okD5 (decodeVec r2)) : okdc5 r r1 = true := rfl

abbrev K12CondA (inL : Fin e7Data.d → Prop) (A2 S : List Rt) (okD : Rt → Prop) : Prop :=
  (∀ β ∈ S, ∃ k : Fin 126, rt k = β) ∧ S.Nodup ∧ (∀ β ∈ S, ∀ γ ∈ S, β ≠ γ → ipR β γ = 0) ∧
  (∀ β ∈ S, okD β) ∧ StarProp okD inL S ∧ Star2Prop okD inL S ∧ Two inL S ∧
  NoMixed inL A2 S ∧ CliqueOK inL A2 S ∧
  (∀ a : Fin e7Data.d, inL a → cntW S a (-(e7Data.wt a)) % 2 = 0)

theorem K12Cond_of {okD : Rt → Prop} [DecidablePred okD] {inL : Fin e7Data.d → Prop}
    {S A2 : List Rt} (h : A2list okD S = A2) (hc : K12CondA inL A2 S okD) : K12Cond okD inL S := by
  unfold K12Cond
  rw [h]
  exact hc

end CFSG.RankThree.GF2n.Smith81.TFast
