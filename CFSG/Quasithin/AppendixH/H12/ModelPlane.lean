module

public import CFSG.Quasithin.AppendixH.H12.ModelOrbit

public section

namespace CFSG.Quasithin.AppendixH.H12.Model

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H12Cert
  CFSG.Quasithin.H13.MatNCert CFSG.Open
open CFSG.ASVolI.ChH (ptStab)

@[expose] def Wb : List ℕ := [5, 10, 113, 146, 1313, 2610]

@[expose] def Wsub : Subgroup Vec12 := spanSub Wb

@[expose] def planes : List (List ℕ) := [
    [5, 10, 113, 146, 1313, 2610],
    [80, 160, 2019, 2417, 759, 857],
    [634, 927, 2028, 2420, 456, 588],
    [1361, 2722, 1749, 2922, 1921, 2498],
    [1371, 2733, 1269, 2138, 1694, 3047],
    [1284, 2568, 327, 649, 87, 169],
    [1444, 2808, 3047, 3449, 1527, 2649],
    [2727, 4089, 2649, 4014, 4038, 1355],
    [2728, 4092, 2886, 3467, 3315, 1105],
    [2648, 4012, 1355, 2701, 3247, 1269],
    [2882, 3459, 1105, 2210, 3519, 1749],
    [171, 253, 261, 522, 974, 327],
    [913, 482, 21, 42, 734, 871],
    [2578, 3875, 1105, 2210, 227, 113],
    [2098, 3091, 1355, 2701, 233, 126],
    [507, 605, 261, 522, 3730, 2019],
    [507, 605, 21, 42, 3736, 2028],
    [2882, 3459, 257, 514, 3359, 1573],
    [2648, 4012, 20, 40, 3888, 1296],
    [171, 253, 1041, 2082, 2412, 3764],
    [913, 482, 1585, 2834, 2163, 3217],
    [2578, 3875, 1285, 2570, 2795, 3965],
    [2098, 3091, 1824, 2352, 2513, 3682],
    [2907, 3501, 2789, 3962, 456, 588],
    [2910, 3495, 2522, 3695, 759, 857],
    [362, 703, 3704, 1948, 2177, 3266],
    [515, 769, 957, 470, 152, 236],
    [44, 52, 680, 1020, 157, 230],
    [610, 947, 544, 816, 2433, 3778],
    [3712, 1984, 2720, 4080, 1177, 2286],
    [3984, 1504, 2725, 4090, 1964, 2548],
    [3278, 1095, 2600, 3900, 3461, 1738],
    [3265, 1090, 2872, 3356, 4005, 1530],
    [220, 100, 2040, 2396, 2621, 3862],
    [998, 379, 1762, 2931, 2621, 3862],
    [3473, 1762, 1844, 2328, 937, 510],
    [3748, 2040, 1028, 2056, 937, 510],
    [396, 708, 3060, 3416, 1585, 2834],
    [396, 708, 2254, 3143, 1041, 2082],
    [3265, 1090, 1128, 2236, 1285, 2570],
    [3278, 1095, 1613, 2950, 1824, 2352],
    [44, 52, 2198, 3307, 2789, 3962],
    [515, 769, 2444, 3780, 2522, 3695],
    [2098, 3091, 1097, 2190, 376, 668],
    [2907, 3501, 212, 104, 882, 403],
    [2910, 3495, 996, 376, 66, 131],
    [362, 703, 3345, 1570, 3024, 3424],
    [352, 688, 3899, 1309, 2767, 3909],
    [675, 1009, 908, 452, 3194, 1183],
    [947, 465, 428, 756, 3679, 1957],
    [656, 992, 1219, 2113, 2975, 3557],
    [191, 213, 1500, 2660, 2490, 3807],
    [339, 673, 2164, 3224, 3370, 1599],
    [614, 955, 2401, 3762, 3125, 1050],
    [1984, 2368, 3683, 1969, 367, 693],
    [1504, 2672, 3961, 1438, 357, 698],
    [1095, 2185, 604, 932, 595, 929],
    [52, 24, 3475, 1761, 3427, 1713],
    [769, 258, 3756, 2036, 3913, 1422],
    [314, 543, 737, 882, 1056, 2096],
    [794, 303, 193, 66, 1333, 2586],
    [1874, 2467, 1712, 3024, 1766, 2939],
    [3570, 1619, 3088, 1056, 998, 379],
    [4050, 1379, 3887, 1333, 220, 100],
    [1822, 2343, 3485, 1766, 705, 834],
    [1550, 2823, 3751, 2041, 705, 834],
    [2550, 3675, 332, 644, 1042, 2083],
    [2278, 3195, 873, 446, 1597, 2838],
    [3628, 1844, 1028, 2056, 1585, 2834],
    [705, 834, 708, 840, 937, 510],
    [2462, 3815, 2680, 3996, 549, 826],
    [1371, 2733, 273, 546, 828, 276],
    [1346, 2691, 257, 514, 1459, 2769],
    [1111, 2217, 20, 40, 1462, 2779],
    [357, 698, 273, 546, 3030, 3435],
    [367, 693, 276, 552, 2758, 3915],
    [755, 849, 1344, 2688, 2490, 3807]]

@[expose] def planeImg : List (ℕ × ℕ) := [
    (0, 1),
    (2, 3),
    (1, 73),
    (4, 5),
    (3, 6),
    (5, 0),
    (6, 7),
    (8, 9),
    (7, 8),
    (10, 4),
    (9, 11),
    (12, 13),
    (11, 72),
    (14, 15),
    (13, 58),
    (16, 10),
    (15, 17),
    (18, 19),
    (17, 71),
    (20, 21),
    (19, 63),
    (22, 16),
    (21, 23),
    (24, 25),
    (23, 45),
    (25, 26),
    (27, 22),
    (26, 28),
    (28, 29),
    (30, 31),
    (29, 70),
    (32, 27),
    (31, 33),
    (34, 35),
    (33, 69),
    (36, 37),
    (35, 68),
    (38, 32),
    (37, 39),
    (40, 12),
    (39, 41),
    (42, 40),
    (41, 43),
    (43, 44),
    (45, 46),
    (44, 59),
    (47, 42),
    (46, 48),
    (49, 50),
    (48, 54),
    (51, 52),
    (50, 51),
    (53, 47),
    (52, 53),
    (55, 56),
    (54, 30),
    (56, 57),
    (58, 49),
    (57, 14),
    (60, 61),
    (59, 62),
    (61, 24),
    (63, 64),
    (62, 34),
    (65, 66),
    (64, 55),
    (67, 60),
    (66, 67),
    (68, 36),
    (69, 20),
    (70, 65),
    (71, 18),
    (73, 38),
    (72, 74),
    (75, 76),
    (74, 75),
    (76, 2)]

@[expose] def spanMask (b : List ℕ) : ℕ := maskOf (spanN b)

private theorem maskOf_eq_of_mem_iff {l l' : List ℕ} (h : ∀ c, c ∈ l ↔ c ∈ l') :
    maskOf l = maskOf l' := by
  apply Nat.eq_of_testBit_eq
  intro c
  rw [testBit_maskOf, testBit_maskOf]
  by_cases hc : c ∈ l
  · have hc' : c ∈ l' := (h c).mp hc
    simp [hc, hc']
  · have hc' : c ∉ l' := fun h' => hc ((h c).mpr h')
    simp [hc, hc']

private theorem spanMask_eq_of_spanSub_eq {a b : List ℕ}
    (ha : ∀ c ∈ a, c < 4096) (hb : ∀ c ∈ b, c < 4096) (h : spanSub a = spanSub b) :
    spanMask a = spanMask b := by
  unfold spanMask
  apply maskOf_eq_of_mem_iff
  intro c
  by_cases hc : c < 4096
  · exact (spanSub_eq_iff ha hb).mp h c hc
  · constructor
    · intro hmem; exact absurd (spanN_lt ha c hmem) hc
    · intro hmem; exact absurd (spanN_lt hb c hmem) hc

@[expose] def planeCheck : Bool :=
  (List.range 77).all fun i =>
    (planeImg.getD i (0, 0)).1 < 77 && (planeImg.getD i (0, 0)).2 < 77 &&
      spanMask ((planes.getD i []).map (mvN (gG.getD 0 one12))) ==
        spanMask (planes.getD (planeImg.getD i (0, 0)).1 []) &&
      spanMask ((planes.getD i []).map (mvN (gG.getD 1 one12))) ==
        spanMask (planes.getD (planeImg.getD i (0, 0)).2 [])

set_option maxRecDepth 200000 in
theorem planeCheck_eq : planeCheck = true := by
  decide +kernel

private theorem planeCheck_facts (n : ℕ) (hn : n < 77) :
    (planeImg.getD n (0, 0)).1 < 77 ∧ (planeImg.getD n (0, 0)).2 < 77 ∧
    spanMask ((planes.getD n []).map (mvN (gG.getD 0 one12))) =
      spanMask (planes.getD (planeImg.getD n (0, 0)).1 []) ∧
    spanMask ((planes.getD n []).map (mvN (gG.getD 1 one12))) =
      spanMask (planes.getD (planeImg.getD n (0, 0)).2 []) := by
  have h := List.all_eq_true.mp planeCheck_eq n (List.mem_range.mpr hn)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

private theorem gmv_gU_eq (i c : ℕ) : gmv (gU i) c = mvN (gG.getD i one12) c := by
  rw [gmv, gU_val, colsN_decN (validN_getD validN_gG i)]

theorem planes_length : planes.length = 77 := by
  decide

theorem planes_valid : ∀ b ∈ planes, ∀ c ∈ b, c < 4096 := by
  decide

theorem Wb_valid : ∀ c ∈ Wb, c < 4096 := by
  decide

theorem Wb_mem_planes : Wb ∈ planes := by
  decide

theorem card_Wsub : Nat.card Wsub = 64 := by
  rw [Wsub, card_spanSub Wb_valid]
  decide +kernel

private theorem hvalid_getD : ∀ n, n < 77 → ∀ c ∈ planes.getD n [], c < 4096 := by
  intro n hn c hc
  exact planes_valid _ (by
    rw [List.getD_eq_getElem planes [] (by simpa [planes_length] using hn)]
    exact List.getElem_mem _) c hc

theorem planes_closed {g : Γ12} (hg : g ∈ G0) {b : List ℕ} (hb : b ∈ planes) :
    ∃ b' ∈ planes, smulSub g (spanSub b) = spanSub b' := by
  have hstep : ∀ i < 2, ∀ P, (∃ a ∈ planes, P = spanSub a) →
      ∃ a' ∈ planes, smulSub (gU i) P = spanSub a' := by
    intro i hi P hP
    obtain ⟨a, ha, hPa⟩ := hP
    obtain ⟨n, hn, hna⟩ := List.mem_iff_getElem.mp ha
    have hn77 : n < 77 := by simpa [planes_length] using hn
    obtain ⟨h1, h2, hm0, hm1⟩ := planeCheck_facts n hn77
    have hnlen : n < planes.length := by simpa [planes_length] using hn77
    have haeq : a = planes.getD n [] := by
      rw [← hna, List.getD_eq_getElem planes [] hnlen]
    rw [hPa, haeq]
    have key : ∀ (i : ℕ) (hmap : gmv (gU i) = mvN (gG.getD i one12))
        (j : ℕ) (hj77 : j < 77)
        (hm : spanMask ((planes.getD n []).map (mvN (gG.getD i one12))) =
          spanMask (planes.getD j [])),
        ∃ a' ∈ planes,
          smulSub (gU i) (spanSub (planes.getD n [])) = spanSub a' := by
      intro i hmap j hj77 hm
      have hjlen : j < planes.length := by simpa [planes_length] using hj77
      refine ⟨planes.getD j [], ?_, ?_⟩
      · rw [List.getD_eq_getElem planes [] hjlen]
        exact List.getElem_mem _
      · rw [smulSub_spanSub, hmap]
        refine (spanSub_eq_iff ?_ (hvalid_getD j hj77)).mpr ?_
        · intro c hc
          obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
          simpa using mvN_lt (validN_getD validN_gG i).2 d
        · intro c _
          exact mem_iff_of_maskOf_eq hm c
    have hi01 : i = 0 ∨ i = 1 := by omega
    rcases hi01 with rfl | rfl
    · exact key 0 (funext (gmv_gU_eq 0)) _ h1 hm0
    · exact key 1 (funext (gmv_gU_eq 1)) _ h2 hm1
  exact closed_of_gen_act smulSub smulSub_one smulSub_mul
    (fun P => ∃ a ∈ planes, P = spanSub a) hstep hg ⟨b, hb, rfl⟩

theorem plane_through_1465 {b : List ℕ} (hb : b ∈ planes) {x : ℕ} (hx : x ∈ lineOf 1465)
    (hxb : x ∈ spanN b) : spanSub b = Wsub := by
  obtain ⟨n, hn, hna⟩ := List.mem_iff_getElem.mp hb
  have hn77 : n < 77 := by simpa [planes_length] using hn
  have hnlen : n < planes.length := by simpa [planes_length] using hn77
  have hbn : b = planes.getD n [] := by
    rw [← hna, List.getD_eq_getElem planes [] hnlen]
  rw [hbn] at hxb ⊢
  have hcheck : ((List.range 77).all fun k => (spanN (planes.getD k [])).all fun x =>
      !((lineOf 1465).contains x) || (spanMask (planes.getD k []) == spanMask Wb)) = true := by
    decide +kernel
  have hk := (List.all_eq_true.mp hcheck) n (List.mem_range.mpr hn77)
  have hxl : (lineOf 1465).contains x = true := List.contains_iff_mem.mpr hx
  have hmem := (List.all_eq_true.mp hk) x hxb
  rw [Bool.or_eq_true, beq_iff_eq] at hmem
  rcases hmem with hf | heq
  · rw [hxl] at hf
    exact Bool.noConfusion hf
  · show spanSub (planes.getD n []) = spanSub Wb
    refine (spanSub_eq_iff (hvalid_getD n hn77) Wb_valid).mpr fun c _ => ?_
    exact mem_iff_of_maskOf_eq heq c

@[expose] def planes5Idx : List ℕ := [0, 25, 56, 69, 71]

@[expose] def planes5 : List (List ℕ) := planes5Idx.map fun i => planes.getD i []

theorem planes5_length : planes5.length = 5 := by
  decide

theorem planes5_mem_planes : ∀ b ∈ planes5, b ∈ planes ∧ 5 ∈ spanN b := by
  decide +kernel

theorem planes5_complete {b : List ℕ} (hb : b ∈ planes) (h5 : 5 ∈ spanN b) :
    ∃ b' ∈ planes5, spanSub b = spanSub b' := by
  obtain ⟨n, hn, hna⟩ := List.mem_iff_getElem.mp hb
  have hn77 : n < 77 := by simpa [planes_length] using hn
  have hnlen : n < planes.length := by simpa [planes_length] using hn77
  have hbn : b = planes.getD n [] := by
    rw [← hna, List.getD_eq_getElem planes [] hnlen]
  rw [hbn] at h5 ⊢
  have hcheck : ((List.range 77).all fun k =>
      !((spanN (planes.getD k [])).contains 5) || planes5Idx.contains k) = true := by
    decide +kernel
  have hk := (List.all_eq_true.mp hcheck) n (List.mem_range.mpr hn77)
  rw [Bool.or_eq_true] at hk
  have hmem5 : n ∈ planes5Idx := by
    rcases hk with hnot | hmem
    · exfalso
      have hcont : (spanN (planes.getD n [])).contains 5 = true := List.contains_iff_mem.mpr h5
      rw [hcont] at hnot
      exact Bool.noConfusion hnot
    · exact List.contains_iff_mem.mp hmem
  exact ⟨planes.getD n [], List.mem_map.mpr ⟨n, hmem5, rfl⟩, rfl⟩

theorem planes5_inj : Function.Injective fun i : Fin 5 => spanSub (planes5.getD i []) := by
  have hvalid5 : ∀ (i : ℕ) (hi : i < 5), ∀ c ∈ planes5.getD i [], c < 4096 := by
    intro i hi c hc
    have hmem : planes5.getD i [] ∈ planes5 := by
      rw [List.getD_eq_getElem planes5 [] (by simpa [planes5_length] using hi)]
      exact List.getElem_mem _
    exact planes_valid _ (planes5_mem_planes _ hmem).1 c hc
  have h : ((List.range 5).all fun a => (List.range 5).all fun b =>
      (a == b) || (spanMask (planes5.getD a []) != spanMask (planes5.getD b []))) = true := by
    decide +kernel
  intro i j hij
  have hi := (List.all_eq_true.mp h) i.val (List.mem_range.mpr i.isLt)
  have hj := (List.all_eq_true.mp hi) j.val (List.mem_range.mpr j.isLt)
  rw [Bool.or_eq_true] at hj
  rcases hj with heq | hne
  · exact Fin.ext (beq_iff_eq.mp heq)
  · exfalso
    apply (bne_iff_ne.mp hne)
    exact spanMask_eq_of_spanSub_eq (hvalid5 i.val i.isLt) (hvalid5 j.val j.isLt) hij

theorem Wsub_isotropic : ∀ u ∈ Wsub, ∀ v ∈ Wsub, f0 u v = 0 := by
  intro u hu v hv
  rw [Wsub, mem_spanSub_iff Wb_valid] at hu hv
  conv_lhs => rw [← dc_cd u, ← dc_cd v]
  rw [f0_dc (cd_lt u) (cd_lt v)]
  have h : ((spanN Wb).all fun a => (spanN Wb).all fun b =>
      !(polN 12 Qcols (mvN z12 (mvN z12 a)) b) && !(polN 12 Qcols a b)) = true := by
    decide +kernel
  have ha := (List.all_eq_true.mp h) (cd u) hu
  have hb := (List.all_eq_true.mp ha) (cd v) hv
  rw [Bool.and_eq_true] at hb
  have hb1 : polN 12 Qcols (mvN z12 (mvN z12 (cd u))) (cd v) = false := by
    simpa using hb.1
  have hb2 : polN 12 Qcols (cd u) (cd v) = false := by
    simpa using hb.2
  rw [hb1, hb2]
  rfl

theorem smulSub_zU_Wsub : smulSub zU Wsub = Wsub := by
  have hmask : spanMask (Wb.map (mvN z12)) = spanMask Wb := by decide +kernel
  rw [Wsub, smulSub_spanSub]
  have hmap : Wb.map (gmv zU) = Wb.map (mvN z12) := by
    apply List.map_congr_left
    intro c _
    rw [gmv, zU_val, colsN_decN validN_z12]
  rw [hmap]
  refine (spanSub_eq_iff ?_ Wb_valid).mpr fun c _ => mem_iff_of_maskOf_eq hmask c
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  exact z12_lt d

theorem T0_le_ptStab_Wsub : T0 ≤ ptStab glHom G0 Wsub := by
  refine (Subgroup.closure_le (ptStab glHom G0 Wsub)).mpr ?_
  intro u hu
  have hgen : ∀ g ∈ tG, ∀ c ∈ Wb, mvN g c ∈ spanN Wb := by
    have h : (tG.all fun g => Wb.all fun c => (spanN Wb).contains (mvN g c)) = true := by
      decide +kernel
    intro g hg c hc
    exact List.contains_iff_mem.mp ((List.all_eq_true.mp ((List.all_eq_true.mp h) g hg)) c hc)
  have hle : smulSub u Wsub ≤ Wsub := by
    show smulSub u (spanSub Wb) ≤ spanSub Wb
    rw [smulSub_spanSub]
    refine (spanSub_le_iff ?_ Wb_valid).mpr ?_
    · intro c hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      exact gmv_lt u d
    · intro c hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      exact hgen (colsN u.val) hu d hd
  exact (mem_ptStab_iff G0 Wsub u).mpr
    ⟨T0_le_G (Subgroup.subset_closure hu), smulSub_eq_of_le u Wsub hle⟩

theorem zU_mem_ptStab_Wsub : zU ∈ ptStab glHom G0 Wsub := by
  exact (mem_ptStab_iff G0 Wsub zU).mpr ⟨zU_mem, smulSub_zU_Wsub⟩

@[expose] def nonhypPts : List ℕ := [5, 113, 116, 123, 126, 1313, 1323, 1360, 1375, 1459, 1462,
  1474, 1479, 1480, 1485]

@[expose] def hypPts : List ℕ := [1316, 1326, 1365, 1370, 1465, 1468]

theorem mem_Wb_iff {c : ℕ} (hc : c < 4096) :
    c ∈ spanN Wb ↔ c = 0 ∨ ∃ r ∈ nonhypPts ++ hypPts, c ∈ lineOf r := by
  have h : (List.range 4096).all (fun c => (spanN Wb).contains c ==
      (c == 0 || ((nonhypPts ++ hypPts).flatMap lineOf).contains c)) = true := by
    decide +kernel
  have hc' := (List.all_eq_true.mp h) c (List.mem_range.mpr hc)
  have hc'' : (spanN Wb).contains c =
      (c == 0 || ((nonhypPts ++ hypPts).flatMap lineOf).contains c) := by
    simpa [beq_iff_eq] using hc'
  rw [← List.contains_iff_mem, hc'', Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem,
    List.mem_flatMap]

theorem hyp_mem_O1465 : ∀ r ∈ hypPts, ∀ x ∈ lineOf r, x ∈ O1465 := by
  decide +kernel

theorem mem_hyp_of_mem_O1465 {c : ℕ} (hc : c ∈ spanN Wb) (hc0 : c ≠ 0) (h : c ∈ O1465) :
    ∃ r ∈ hypPts, c ∈ lineOf r := by
  have hclt : c < 4096 := spanN_lt Wb_valid c hc
  have hcheck : (List.range 4096).all (fun c =>
      !((spanN Wb).contains c) || (c == 0) || !((O1465).contains c) ||
        ((hypPts.flatMap lineOf).contains c)) = true := by
    decide +kernel
  have hc' := (List.all_eq_true.mp hcheck) c (List.mem_range.mpr hclt)
  have h1 : (spanN Wb).contains c = true := List.contains_iff_mem.mpr hc
  have h2 : (c == 0) = false := by
    cases hh : c == 0 with
    | false => rfl
    | true => exact absurd (beq_iff_eq.mp hh) hc0
  have h3 : (O1465.contains c) = true := List.contains_iff_mem.mpr h
  simp only [h1, h2, h3, Bool.not_true, Bool.not_false, Bool.or_false, Bool.false_or] at hc'
  exact List.mem_flatMap.mp (List.contains_iff_mem.mp hc')

theorem hypPts_length : hypPts.length = 6 := by
  decide

theorem hypPts_lt : ∀ r ∈ hypPts, r < 4096 := by
  decide

theorem nonhypPts_lt : ∀ r ∈ nonhypPts, r < 4096 := by
  decide

end CFSG.Quasithin.AppendixH.H12.Model
