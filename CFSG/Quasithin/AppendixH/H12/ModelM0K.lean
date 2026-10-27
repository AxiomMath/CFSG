module

public import CFSG.Quasithin.AppendixH.H12.ModelAct
public import CFSG.Certificates.Kernel.Mat12PSound
public import CFSG.Quasithin.H13.L32NMatN

public section

namespace CFSG.Quasithin.AppendixH.H12.ModelM0K

open CFSG.Quasithin.AppendixH.H12.Model CFSG.Quasithin.H.Mathieu.H12Cert CFSG.Quasithin.H13.MatNCert
  CFSG.KC.Mat12P

@[expose] def gQ : List ℕ := [12688179074850678486840935154304820009009156,
  11892279212000954280667021665496042051862544]

theorem gQ_eq : gG.map codeQ = gQ := by decide +kernel

@[expose] def evalQ (w : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) oneQ (fun i _ acc => mulQ (gQ.getD i oneQ) acc) w

theorem tW_eq (w : List ℕ) : evalW 12 gG w = unpackQ (evalQ w) := by
  induction w with
  | nil => exact oneQ_eq.symm
  | cons i w ih =>
    change mulN (gG.getD i (oneN 12)) (evalW 12 gG w) = unpackQ (mulQ (gQ.getD i oneQ) (evalQ w))
    rw [ih, getD_unpackQ gG (by decide) i, gQ_eq, mulN_unpackQ]

theorem all_tW (L : List (List ℕ)) (C : List ℕ) (hC : (L.map evalQ == C) = true)
    (P : List ℕ → Bool) : L.all (fun w => P (tW w)) = C.all (fun X => P (unpackQ X)) := by
  rw [← beq_iff_eq.1 hC, List.all_map]
  congr 1
  funext w
  change P (evalW 12 gG w) = P (unpackQ (evalQ w))
  rw [tW_eq]

theorem map_tW (L : List (List ℕ)) (C : List ℕ) (hC : (L.map evalQ == C) = true) :
    L.map tW = C.map unpackQ := by
  rw [← beq_iff_eq.1 hC, List.map_map]
  exact List.map_congr_left fun w _ => tW_eq w

@[expose] def WM : ℕ :=
  539038908596799980756355826415860343198194268446526443055240346306164849602401297345367578126613534026243730640186658393156223805256243225251204265072067331410805933359347617399950069933472809631668845228289206877109572776451712022589811211479038756035726497995911051934225955218822707948614485483872280885333761186158831483614512621181263280409795426892057570550276676609703398006268829322497783213715243583692171125517660074866218183665202699989243135494812752999064128097632256906325405825889438788205093628416111928506549274620362988395161894563297894331972515937259674298502946304573718764905938457829476466851492188007281517564042737891159503195715887442360451229178605698516751822942322481570048072445525421062385789798814280872187682737896879284685246197315208192561631147520526594004321374677543312823430739303116075750251740056606824820087344649558976756937538652915118979728419622986639474025820571675733184105981462379481456061395937136504362406425043478691428452719327628607339515748955288832235706810333679680267790297057801165871176817324891110251107339295854817977860475677491537495261287618358985568933120290333336979525245356564678028724755568103310590388688002674039224566420719130508146362483055414296492575327265

theorem spanMask_Wb : spanMask Wb = WM := by decide +kernel

theorem contains_spanN_Wb (x : ℕ) : (spanN Wb).contains x = WM.testBit x := by
  rw [← spanMask_Wb, spanMask, testBit_maskOf]
  exact Bool.eq_iff_iff.2 (by simp [List.contains_iff_mem])

theorem testBit_raw (m y : ℕ) : m.testBit y = Nat.beq (Nat.land (Nat.shiftRight m y) 1) 1 := by
  have e : Nat.land (Nat.shiftRight m y) 1 = m / 2 ^ y % 2 := by
    change (m >>> y) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e]
  refine Bool.eq_iff_iff.2 ?_
  rw [Nat.beq_eq, ← Nat.one_and_eq_mod_two, ← Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (m >>> y) with h | h
  · have h1 : 1 &&& m >>> y = 0 := by rw [Nat.one_and_eq_mod_two, h]
    rw [h1]
    exact ⟨fun hb => by simp [Nat.testBit, h1] at hb, fun h0 => absurd h0 (by decide)⟩
  · have h1 : 1 &&& m >>> y = 1 := by rw [Nat.one_and_eq_mod_two, h]
    rw [h1]
    exact ⟨fun _ => rfl, fun _ => by simp [Nat.testBit, h1]⟩

@[expose] def wmB (x : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight WM x) 1) 1

@[expose] def commRow (X c : ℕ) : Bool := wmB (Nat.xor (mvNR (unpackQ X) c) c)

theorem contains_Wb_raw (x : ℕ) : (spanN Wb).contains x = wmB x := by
  rw [contains_spanN_Wb, testBit_raw]
  rfl

theorem comm_row_eq (X c : ℕ) : WM.testBit (mvN (unpackQ X) c ^^^ c) = commRow X c := by
  rw [commRow, ← mvN_toR, testBit_raw]
  rfl

@[expose] def WL : List ℕ := [0, 5, 10, 15, 113, 116, 123, 126, 146, 151, 152, 157, 227, 230, 233, 236,
  1313, 1316, 1323, 1326, 1360, 1365, 1370, 1375, 1459, 1462, 1465, 1468, 1474, 1479, 1480, 1485,
  2610, 2615, 2616, 2621, 2627, 2630, 2633, 2636, 2720, 2725, 2730, 2735, 2769, 2772, 2779, 2782,
  3859, 3862, 3865, 3868, 3938, 3943, 3944, 3949, 3969, 3972, 3979, 3982, 4080, 4085, 4090, 4095]

theorem spanN_Wb : (spanN Wb == WL) = true := by decide +kernel

theorem xor_check : (WL.all fun a => WL.all fun b => wmB (Nat.xor a b)) = true := by decide +kernel

theorem wm_iff (x : ℕ) : WM.testBit x = true ↔ x ∈ WL := by
  rw [← spanMask_Wb, spanMask, testBit_maskOf, decide_eq_true_iff, beq_iff_eq.1 spanN_Wb]

theorem wm_xor {a b : ℕ} (ha : WM.testBit a = true) (hb : WM.testBit b = true) :
    WM.testBit (a ^^^ b) = true := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 xor_check a ((wm_iff a).1 ha)) b ((wm_iff b).1 hb)
  rw [testBit_raw]
  exact h

theorem wm_zero : WM.testBit 0 = true := (wm_iff 0).2 List.mem_cons_self

theorem mvN_mem (B : List ℕ) (hB : ∀ b ∈ B, WM.testBit b = true) (v : ℕ) :
    WM.testBit (mvN B v) = true := by
  induction B generalizing v with
  | nil =>
    simp only [mvN]
    exact wm_zero
  | cons b B ih =>
    simp only [mvN]
    refine wm_xor ?_ (ih (fun c hc => hB c (List.mem_cons_of_mem _ hc)) _)
    split
    · exact hB b List.mem_cons_self
    · exact wm_zero

theorem mvN_zip (A C : List ℕ) (h : A.length = C.length) (v : ℕ) :
    mvN (List.zipWith (· ^^^ ·) A C) v = mvN A v ^^^ mvN C v := by
  induction A generalizing C v with
  | nil =>
    cases C with
    | nil => simp [mvN]
    | cons c C => simp at h
  | cons a A ih =>
    cases C with
    | nil => simp at h
    | cons c C =>
      simp only [List.zipWith_cons_cons, mvN]
      rw [ih C (by simpa using h)]
      split
      · simp only [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]
      · simp only [Nat.zero_xor]

theorem mvN_one12 {c : ℕ} (hc : c < 4096) : mvN (oneN 12) c = c := by
  have h := decN_mulVec (n := 12) (A := oneN 12) validN_oneN.1 c
  rw [decN_oneN, Matrix.one_mulVec] at h
  exact vecN_inj (mvN_lt validN_oneN.2 c) (by norm_num; exact hc) h.symm

theorem comm_mem (A : List ℕ) (hA : A.length = 12)
    (hB : ∀ b ∈ List.zipWith (· ^^^ ·) A (oneN 12), wmB b = true) {c : ℕ} (hc : c < 4096) :
    WM.testBit (mvN A c ^^^ c) = true := by
  have e : mvN A c ^^^ c = mvN (List.zipWith (· ^^^ ·) A (oneN 12)) c := by
    rw [mvN_zip A (oneN 12) (by rw [hA]; rfl) c, mvN_one12 hc]
  rw [e]
  exact mvN_mem _ (fun b hb => by rw [testBit_raw]; exact hB b hb) c

theorem tW_length (w : List ℕ) : (tW w).length = 12 := by
  change (evalW 12 gG w).length = 12
  rw [tW_eq]
  rfl

@[expose] def qQL : List ℕ := [11151733894906779683522195341810241573494785,
  18640660806054068269277718796285499532169227, 11095480192216388829700292041174488442260040,
  11095480592812465684198542305864483713848771, 19239410147899700050011415451896035325549127,
  3713615051338881708514234806339787093763529, 18640661206650091082751802274905937992748928,
  3092874968023351066909142909981729564176261, 3713614620761650990039984398941164146276930,
  11151734325484057325016576195185961147891594, 11946784627988999815968440141100408278379085,
  10322420621980929178687154253043176075714447, 11946784223494903103557002552072456764700102,
  3092875372517405213873649883452349867913230, 19239409721220498783334541102711157203158476,
  10322421048660185080575300345409129037201412]

@[expose] def sigQ (Pg : ℕ → List ℕ) (n : ℕ) (X : ℕ) : List ℕ :=
  (List.range n).map fun i => spanMask ((Pg i).map (mvN (unpackQ X)))

theorem sigOf_eq (Pg : ℕ → List ℕ) (n : ℕ) (w : List ℕ) : sigOf Pg n w = sigQ Pg n (evalQ w) := by
  rw [sigOf, sigQ]
  change _ = (List.range n).map fun i => spanMask ((Pg i).map (mvN (unpackQ (evalQ w))))
  rw [← tW_eq]

@[expose] def keyS (s : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun m _ acc => Nat.add (Nat.mod m 1000003) (Nat.mul 1000003 acc)) s

@[expose] def memB (c : ℕ) (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun a _ r => Bool.rec (motive := fun _ => Bool) r true (Nat.beq a c)) L

@[expose] def nodupK (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun a t r => Bool.rec (motive := fun _ => Bool) r false (memB a t)) L

theorem memB_false {c : ℕ} {L : List ℕ} (h : memB c L = false) : c ∉ L := by
  induction L with
  | nil => exact List.not_mem_nil
  | cons a L ih =>
    change Bool.rec (motive := fun _ => Bool) (memB c L) true (Nat.beq a c) = false at h
    cases ha : Nat.beq a c
    · rw [ha] at h
      rw [List.mem_cons, not_or]
      exact ⟨fun e => by rw [e, Nat.beq_refl] at ha; exact Bool.false_ne_true ha.symm, ih h⟩
    · rw [ha] at h
      exact absurd h.symm Bool.false_ne_true

theorem nodup_of_nodupK {L : List ℕ} (h : nodupK L = true) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons a L ih =>
    change Bool.rec (motive := fun _ => Bool) (nodupK L) false (memB a L) = true at h
    cases ha : memB a L
    · rw [ha] at h
      exact List.nodup_cons.2 ⟨memB_false ha, ih h⟩
    · rw [ha] at h
      exact absurd h Bool.false_ne_true

theorem sig_nodup (Pg : ℕ → List ℕ) (n : ℕ) (L : List (List ℕ))
    (h : nodupK (L.map fun w => keyS (sigQ Pg n (evalQ w))) = true) : (L.map (sigOf Pg n)).Nodup := by
  have e : L.map (sigOf Pg n) = L.map fun w => sigQ Pg n (evalQ w) :=
    List.map_congr_left fun w _ => sigOf_eq Pg n w
  rw [e]
  refine List.Nodup.of_map keyS ?_
  rw [List.map_map]
  exact nodup_of_nodupK h

end CFSG.Quasithin.AppendixH.H12.ModelM0K
