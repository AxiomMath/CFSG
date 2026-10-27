module

public import CFSG.Sporadic.Co1.Module.U6OddLitInputs
public import CFSG.Sporadic.Co1.Module.U6OddForest
public import CFSG.Sporadic.Co1.Module.U6OddProg
public import CFSG.Sporadic.Co1.Module.U6OddTuple

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1.Module.U6Odd

open CFSG.Blueprint CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.SortTree CFSG.KC.U6Odd
  CFSG.KC.InvFam CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.TwoBK CFSG.Sporadic.Co1.OddNative CFSG.Sporadic.Co1.U6OddNative
  CFSG.Sporadic.Co1.Module.CoTwo

theorem lenLL_eq : ∀ L : List (List ℕ), lenLL L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (lenLL_eq L)

theorem beq_false_of_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem getL_map (f : ℕ → ℕ) : ∀ (L : List ℕ) (l : ℕ), l < L.length →
    getL 0 (L.map f) l = f (getL 0 L l)
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: L, l + 1, h => getL_map f L l (by simpa using h)

theorem xcK_eq : ∀ (c : List ℕ) (m : ℕ), xcK c m = xcN c m
  | [], _ => rfl
  | x :: xs, m => by
    change Nat.xor (Bool.rec (motive := fun _ => ℕ) 0 x (Nat.beq (m % 2) 1)) (xcK xs (m / 2)) =
      (if m % 2 = 1 then x else 0) ^^^ xcN xs (m / 2)
    rw [xcK_eq xs]
    congr 1
    by_cases h : m % 2 = 1
    · simp only [h, ↓reduceIte]
      rfl
    · simp only [h, ↓reduceIte, beq_false_of_ne h]

theorem xcN_take : ∀ (c : List ℕ) (n m : ℕ), m < 2 ^ n → xcN (c.take n) m = xcN c m
  | [], n, m, _ => by simp
  | x :: xs, 0, m, h => by
    have hm : m = 0 := by simpa using h
    subst hm
    rw [xcN_zero, xcN_zero]
  | x :: xs, n + 1, m, h => by
    simp only [List.take_succ_cons, xcN]
    rw [xcN_take xs n (m / 2) (by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at h; exact h)]

@[expose] noncomputable def stepIn (L : ℕ → ℕ) (b : List ℕ) (k : ℕ) (c : List ℕ) (W' : List ℕ)
    (acc : List (List ℕ)) : List (List ℕ) :=
  List.rec (motive := fun _ => List (List ℕ)) acc
    (fun x _ ih2 => (fun c' => Bool.rec (motive := fun _ => List (List ℕ)) ih2
      (List.cons c' ih2) (newOK L b k c')) (List.append c (List.cons x List.nil))) W'

theorem tupStep_cons (L : ℕ → ℕ) (W b : List ℕ) (k : ℕ) (c : List ℕ) (ps : List (List ℕ)) :
    tupStep L W b k (c :: ps) = stepIn L b k c W (tupStep L W b k ps) := rfl

theorem stepIn_acc {L : ℕ → ℕ} {b : List ℕ} {k : ℕ} {c : List ℕ} :
    ∀ (W' : List ℕ) (acc : List (List ℕ)) (y : List ℕ), y ∈ acc → y ∈ stepIn L b k c W' acc
  | [], _, _, hy => hy
  | x :: W', acc, y, hy => by
    change y ∈ Bool.rec (motive := fun _ => List (List ℕ)) (stepIn L b k c W' acc)
      ((c ++ [x]) :: stepIn L b k c W' acc) (newOK L b k (c ++ [x]))
    cases newOK L b k (c ++ [x])
    · exact stepIn_acc W' acc y hy
    · exact List.mem_cons_of_mem _ (stepIn_acc W' acc y hy)

theorem stepIn_mem {L : ℕ → ℕ} {b : List ℕ} {k : ℕ} {c : List ℕ} {x : ℕ}
    (h : newOK L b k (c ++ [x]) = true) :
    ∀ (W' : List ℕ) (acc : List (List ℕ)), x ∈ W' → c ++ [x] ∈ stepIn L b k c W' acc
  | [], _, hx => absurd hx List.not_mem_nil
  | y :: W', acc, hx => by
    change c ++ [x] ∈ Bool.rec (motive := fun _ => List (List ℕ)) (stepIn L b k c W' acc)
      ((c ++ [y]) :: stepIn L b k c W' acc) (newOK L b k (c ++ [y]))
    rcases List.mem_cons.1 hx with rfl | hx'
    · rw [h]
      exact List.mem_cons_self
    · cases newOK L b k (c ++ [y])
      · exact stepIn_mem h W' acc hx'
      · exact List.mem_cons_of_mem _ (stepIn_mem h W' acc hx')

theorem mem_tupStep {L : ℕ → ℕ} {W b : List ℕ} {k : ℕ} {c : List ℕ} {x : ℕ} (hx : x ∈ W)
    (h : newOK L b k (c ++ [x]) = true) :
    ∀ ps : List (List ℕ), c ∈ ps → c ++ [x] ∈ tupStep L W b k ps
  | [], hc => absurd hc List.not_mem_nil
  | c0 :: ps, hc => by
    rw [tupStep_cons]
    rcases List.mem_cons.1 hc with rfl | hc'
    · exact stepIn_mem h W _ hx
    · exact stepIn_acc W _ _ (mem_tupStep hx h ps hc')

theorem tupIter_succ (L : ℕ → ℕ) (W b : List ℕ) (n k : ℕ) (ps : List (List ℕ)) :
    tupIter L W b (n + 1) k ps = tupIter L W b n (k + 1) (tupStep L W b k ps) := rfl

theorem mem_tupsK {L : ℕ → ℕ} {W b : List ℕ} {u₁ u₂ : ℕ} {c : List ℕ} (hb : 2 ≤ b.length)
    (hlen : c.length = b.length) (h01 : c.take 2 = [u₁, u₂])
    (hW : ∀ i < c.length, 2 ≤ i → c.getD i 0 ∈ W)
    (hsig : ∀ m < 2 ^ b.length, L (xcK c m) = L (xcK b m)) : c ∈ tupsK L W b u₁ u₂ := by
  have step : ∀ k, 2 ≤ k → k < c.length → ∀ ps, c.take k ∈ ps →
      c.take (k + 1) ∈ tupStep L W b k ps := by
    intro k hk hkc ps hps
    have e : c.take (k + 1) = c.take k ++ [c.getD k 0] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hkc, List.getD_eq_getElem _ _ hkc]
      rfl
    rw [e]
    refine mem_tupStep (hW k hkc hk) ?_ ps hps
    rw [← e]
    unfold newOK
    rw [allN_iff]
    intro j hj
    rw [pw2_eq] at hj ⊢
    refine beq_iff.2 ?_
    have hm : 2 ^ k + j < 2 ^ (k + 1) := by rw [pow_succ]; omega
    have hm' : 2 ^ k + j < 2 ^ b.length :=
      lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega))
    change L (xcK (c.take (k + 1)) (2 ^ k + j)) = L (xcK b (2 ^ k + j))
    rw [xcK_eq, xcN_take c (k + 1) _ hm, ← xcK_eq]
    exact hsig _ hm'
  have key : ∀ n k ps, k + n = b.length → 2 ≤ k → c.take k ∈ ps →
      c.take (k + n) ∈ tupIter L W b n k ps := by
    intro n
    induction n with
    | zero =>
      intro k ps _ _ hps
      change c.take (k + 0) ∈ ps
      simpa using hps
    | succ n ih =>
      intro k ps hkn hk hps
      have e : k + (n + 1) = (k + 1) + n := by omega
      rw [tupIter_succ, e]
      exact ih (k + 1) _ (by omega) (by omega) (step k hk (by omega) ps hps)
  have h := key (lenL b - 2) 2 [[u₁, u₂]] (by rw [InvFam.lenL_eq]; omega) le_rfl (by rw [h01]; simp)
  have e : 2 + (lenL b - 2) = c.length := by
    rw [InvFam.lenL_eq]
    omega
  rw [e, List.take_length] at h
  exact h

variable {W : U6W}

theorem lit_len (hW : U6OK W) : W.R.length = 67 := by
  have h := InvFam.progK_len prog 2 hW.prog
  have hp : prog.length = 65 := rfl
  omega

theorem lit_take (hW : U6OK W) : W.R.take 2 = [W.reg 0, W.reg 1] := by
  have hl := lit_len hW
  match h : W.R, hl with
  | a :: b :: rest, _ => simp [U6W.reg, InvFam.getL_eq, h]

theorem lit_regs (hW : U6OK W) : regsRows = (W.R.map (unpackR 24)).toArray := by
  have e : (#[dat.rowsA, dat.rowsB] : Array (Array ℕ)) =
      ((W.R.take 2).map (unpackR 24)).toArray := by
    rw [lit_take hW, hW.rA, hW.rB]
    rfl
  rw [regsRows, initRows, e, prog_sound hW.prog]

theorem lit_rr (hW : U6OK W) {i : ℕ} (hi : i < 67) : rr i = unpackR 24 (W.reg i) := by
  have hl := lit_len hW
  rw [rr, lit_regs hW]
  simp [U6W.reg, InvFam.getL_eq, hl, hi]


theorem lit_pm (hW : U6OK W) {i : ℕ} (hi : i < 67) : PM (regG i) (W.reg i) := by
  unfold PM
  rw [← lit_rr hW hi]
  exact mat_reg i

theorem lit_tr (hW : U6OK W) {i : ℕ} (hi : i < 67) : trK 24 (W.reg i) = W.regT i := by
  have h := (allN_iff _ _).1 hW.tr i (by rw [InvFam.lenL_eq, lit_len hW]; exact hi)
  exact beq_iff.1 h

theorem lit_act (hW : U6OK W) {i : ℕ} (hi : i < 67) (v : ℕ) :
    co1Act (regG i) (toVecD 24 v) = toVecD 24 (vmF 24 (W.regT i) v) :=
  pm_act (lit_pm hW hi) (lit_tr hW hi) v

theorem lit_idx (hW : U6OK W) {L : List ℕ} (h : bndK (lenL W.R) L = true) : ∀ i ∈ L, i < 67 := by
  intro i hi
  have := InvFam.bnd_spec h i hi
  rwa [InvFam.lenL_eq, lit_len hW] at this

theorem lit_fix (hW : U6OK W) {I vs : List ℕ} (hI : ∀ i ∈ I, i < 67) (h : fixAllK W.RT I vs = true) :
    ∀ i ∈ I, ∀ v ∈ vs, co1Act (regG i) (toVecD 24 v) = toVecD 24 v := by
  intro i hi v hv
  rw [lit_act hW (hI i hi), U6W.regT, InvFam.fixAll_spec h i hi v hv]

theorem getD_mem_of_lt {α : Type*} {L : List α} {i : ℕ} (d : α) (hi : i < L.length) :
    L.getD i d ∈ L := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem le_ncard_of_inj {α : Type*} {s : Set α} {n : ℕ} (f : ℕ → α) (hf : ∀ i < n, f i ∈ s)
    (hinj : ∀ i < n, ∀ j < n, f i = f j → i = j) (hs : s.Finite) : n ≤ s.ncard := by
  have hsub : f '' Set.Iio n ⊆ s := by
    rintro _ ⟨i, hi, rfl⟩
    exact hf i hi
  have hinj' : Set.InjOn f (Set.Iio n) := fun i hi j hj e => hinj i hi j hj e
  have hc : (f '' Set.Iio n).ncard = n := by
    rw [hinj'.ncard_image, Set.ncard_Iio_nat]
  calc n = (f '' Set.Iio n).ncard := hc.symm
    _ ≤ s.ncard := Set.ncard_le_ncard hsub hs

theorem le_card_of_inj {K : Subgroup NativeSporadic.Co1} {n : ℕ} (f : ℕ → NativeSporadic.Co1)
    (hf : ∀ i < n, f i ∈ K) (hinj : ∀ i < n, ∀ j < n, f i = f j → i = j) : n ≤ Nat.card K := by
  have hfin := finite_co1
  have e : Nat.card K = (K : Set NativeSporadic.Co1).ncard := Nat.card_coe_set_eq _
  rw [e]
  exact le_ncard_of_inj f hf hinj (Set.toFinite _)

theorem lit_lv_mem {pd : PrimeData} {P : PrimeW} (hP : PrimeOK W pd P) {n : ℕ} (hn : n < pd.base.length) :
    pd.lv.getD n [] ∈ pd.lv :=
  getD_mem_of_lt [] (by rw [hP.lenLv]; exact hn)

theorem lit_lv_idx (hW : U6OK W) {pd : PrimeData} {P : PrimeW} (hP : PrimeOK W pd P) {n : ℕ}
    (hn : n < pd.base.length) : ∀ i ∈ pd.lv.getD n [], i < 67 := fun i hi =>
  lit_idx hW hP.idx i (List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨_, lit_lv_mem hP hn, hi⟩))

theorem lit_g_idx (hW : U6OK W) {pd : PrimeData} {P : PrimeW} (hP : PrimeOK W pd P) : pd.g < 67 :=
  lit_idx hW hP.idx pd.g List.mem_cons_self

theorem take_mem {base : List ℕ} {j n : ℕ} (hj : j < n) (hn : n ≤ base.length) :
    base.getD j 0 ∈ base.take n := by
  have hjt : j < (base.take n).length := by rw [List.length_take]; omega
  have e : (base.take n)[j] = base.getD j 0 := by
    rw [List.getElem_take, List.getD_eq_getElem _ _ (by omega)]
  rw [← e]
  exact List.getElem_mem hjt

theorem lit_chain_card (hW : U6OK W) {pd : PrimeData} {P : PrimeW} (hP : PrimeOK W pd P) :
    ((List.range pd.base.length).map fun i => pd.sz.getD i 0).prod *
      Nat.card (chainGrp u1 u2 pd.base pd.base.length) ≤ Nat.card (chainGrp u1 u2 pd.base 0) := by
  have hfin := finite_co1
  have hcs := @card_step NativeSporadic.Co1 Vec24 _ co1Act hfin Odd.co1Act_mul' Odd.co1Act_one'
  have hbase := InvFam.bnd_spec hP.base
  have key : ∀ n, n ≤ pd.base.length →
      ((List.range n).map fun i => pd.sz.getD i 0).prod * Nat.card (chainGrp u1 u2 pd.base n) ≤
        Nat.card (chainGrp u1 u2 pd.base 0) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hn' : n < pd.base.length := hn
      have ih' := ih hn'.le
      have hIr := lit_lv_idx hW hP hn'
      have hfix := lit_fix hW hIr (hP.fix n hn')
      have hmem : ∀ l ∈ pd.lv.getD n [], regG l ∈ chainGrp u1 u2 pd.base n := by
        intro l hl
        rw [mem_chainGrp]
        refine ⟨hfix l hl u1 (by simp), hfix l hl u2 (by simp), fun j hj => hfix l hl _ ?_⟩
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (take_mem hj hn'.le))
      obtain ⟨t, ht, hinj⟩ := InvFam.vec_family (chainGrp u1 u2 pd.base n) (hP.tree n hn')
        (hbase _ (getD_mem_of_lt 0 hn')) (fun l => regG (getL 0 (pd.lv.getD n []) l))
        (fun l hl => hmem _ (InvFam.getL_mem hl))
        (fun l hl v => by rw [lit_act hW (hIr _ (InvFam.getL_mem hl))]; rfl)
      have horb : pd.sz.getD n 0 ≤
          (orbitSet co1Act (chainGrp u1 u2 pd.base n) (toVecD 24 (pd.base.getD n 0))).ncard :=
        le_ncard_of_inj (fun i => co1Act (t i) (toVecD 24 (pd.base.getD n 0)))
          (fun i hi => ⟨t i, (ht i hi).1, rfl⟩) hinj (Set.toFinite _)
      have hstep := hcs (H := chainGrp u1 u2 pd.base n) (K := chainGrp u1 u2 pd.base (n + 1))
        inf_le_left (x := toVecD 24 (pd.base.getD n 0))
        (fun g hg => by
          have := hg
          simp only [chainGrp, Subgroup.mem_inf, mem_vstab] at this
          exact this.2) horb
      rw [List.range_succ, List.map_append, List.prod_append]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      calc ((List.range n).map fun i => pd.sz.getD i 0).prod * pd.sz.getD n 0 *
            Nat.card (chainGrp u1 u2 pd.base (n + 1))
          = ((List.range n).map fun i => pd.sz.getD i 0).prod *
              (pd.sz.getD n 0 * Nat.card (chainGrp u1 u2 pd.base (n + 1))) := by ring
        _ ≤ ((List.range n).map fun i => pd.sz.getD i 0).prod *
              Nat.card (chainGrp u1 u2 pd.base n) := Nat.mul_le_mul_left _ hstep
        _ ≤ _ := ih'
  exact key _ le_rfl

theorem lit_chain_le_k (hW : U6OK W) {pd : PrimeData} {P : PrimeW} (hP : PrimeOK W pd P)
    (hU : Nat.card (chainGrp u1 u2 pd.base 0) = 9196830720) :
    Nat.card (chainGrp u1 u2 pd.base pd.base.length) ≤ pd.k := by
  have h1 := lit_chain_card hW hP
  rw [hU] at h1
  have h2 := hP.prod
  set Pr := ((List.range pd.base.length).map fun i => pd.sz.getD i 0).prod with hPr
  have hPpos : 0 < Pr := by
    by_contra h0
    have : Pr = 0 := by omega
    rw [this] at h2
    simp at h2
  exact Nat.le_of_mul_le_mul_left (h1.trans h2) hPpos

theorem lit_g (hW : U6OK W) {pd : PrimeData} {P : PrimeW} (hP : PrimeOK W pd P) :
    orderOf (regG pd.g) = pd.p ∧ regG pd.g ∈ chainGrp u1 u2 pd.base pd.base.length := by
  have hg := lit_g_idx hW hP
  have hpm := lit_pm hW hg
  have hpow : regG pd.g ^ pd.p = 1 := by
    apply matHom_injective
    have h := pm_pow hpm pd.p
    unfold PM at h
    rw [h, hP.gpow, map_one, unpackR_idF, rowsMatrix_idRows]
  have hne : regG pd.g ≠ 1 := fun h1 =>
    hP.gne (pm_eq hpm pm_one hP.gcanon.symm canon_idF h1)
  have : Fact pd.p.Prime := ⟨hP.prime⟩
  refine ⟨orderOf_eq_prime hpow hne, ?_⟩
  have hfix := lit_fix hW (fun i hi => by rw [List.mem_singleton.1 hi]; exact hg) hP.gfix pd.g
    List.mem_cons_self
  rw [mem_chainGrp]
  exact ⟨hfix u1 (by simp), hfix u2 (by simp), fun j hj => hfix _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (getD_mem_of_lt 0 hj)))⟩

theorem lit_W (hW : U6OK W) {pd : PrimeData} {P : PrimeW} (hP : PrimeOK W pd P) {x : ℕ}
    (hx : x < 2 ^ 24) (hfx : co1Act (regG pd.g) (toVecD 24 x) = toVecD 24 x) : x ∈ P.W := by
  have hg := lit_g_idx hW hP
  have hfl := CFSG.KC.Co1Fix.fixList_eq_of hP.fixc hP.fixl
  have e : [unpackR 24 (W.regT pd.g), unpackR 24 (W.regT pd.g)] =
      [unpackR 24 (W.reg pd.g), unpackR 24 (W.reg pd.g)].map (transposeRows 24) := by
    simp only [List.map_cons, List.map_nil, CFSG.KC.F2W.transposeRows_unpackR, lit_tr hW hg]
  rw [← hfl, e, Odd.mem_fixList]
  refine ⟨hx, fun M hM => ?_⟩
  have hM' : M = unpackR 24 (W.reg pd.g) := by simpa using hM
  rw [hM']
  have hpm := lit_pm hW hg
  unfold PM at hpm
  rw [← hpm]
  exact hfx

theorem lit_W_lt {pd : PrimeData} {P : PrimeW} (hP : PrimeOK W pd P) {x : ℕ} (hx : x ∈ P.W) :
    x < 2 ^ 24 := by
  have h2 := hP.fixl
  unfold CFSG.KC.Co1Fix.fixListK at h2
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h2
  exact (h2.1.2 x hx).1.1

theorem lit_lab {pd : PrimeData} {P : PrimeW} (hP : PrimeOK W pd P) {w : ℕ} (hw : w ∈ P.W) :
    labC P.PV P.LB w = labU6 w :=
  beq_iff.1 (InvFam.allL_iff.1 hP.labT w hw)

theorem lit_W_xor (hW : U6OK W) {pd : PrimeData} {P : PrimeW} (hP : PrimeOK W pd P) {x y : ℕ}
    (hx : x ∈ P.W) (hy : y ∈ P.W) : (x ^^^ y) ∈ P.W := by
  have hg := lit_g_idx hW hP
  have hfl := CFSG.KC.Co1Fix.fixList_eq_of hP.fixc hP.fixl
  refine lit_W hW hP (Nat.xor_lt_two_pow (lit_W_lt hP hx) (lit_W_lt hP hy)) ?_
  have hfx : ∀ z ∈ P.W, co1Act (regG pd.g) (toVecD 24 z) = toVecD 24 z := by
    intro z hz
    have h2 := hP.fixl
    unfold CFSG.KC.Co1Fix.fixListK at h2
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h2
    rw [lit_act hW hg, (h2.1.2 z hz).1.2]
  rw [toVecD_xor, co1Act_add, hfx x hx, hfx y hy]

theorem lit_W_zero (hW : U6OK W) {pd : PrimeData} {P : PrimeW} (hP : PrimeOK W pd P) : 0 ∈ P.W :=
  lit_W hW hP (by norm_num) (by rw [toVecD_zero, co1Act_zero])

theorem hu₁ : u1 < 2 ^ 24 := by decide

theorem hu₂ : u2 < 2 ^ 24 := by decide

theorem lit_b_take2 {pd : PrimeData} {P : PrimeW} (hP : PrimeOK W pd P) :
    pd.b.take 2 = [u1, u2] ∧ 2 + pd.base.length ≤ pd.b.length := by
  have h := hP.shape
  have hl := congrArg List.length h
  simp only [List.length_take, List.length_cons] at hl
  refine ⟨?_, by omega⟩
  have : (pd.b.take (2 + pd.base.length)).take 2 = [u1, u2] := by rw [h]; rfl
  rwa [List.take_take, min_eq_left (by omega)] at this

theorem lit_tuple_mem (hW : U6OK W) (hL : LSpec labU6) {pd : PrimeData} {P : PrimeW}
    (hP : PrimeOK W pd P) {n : NativeSporadic.Co1}
    (hnW : ∀ v, co1Act (regG pd.g) v = v → co1Act (regG pd.g) (co1Act n v) = co1Act n v)
    (hnu : co1Act n (toVecD 24 u1) = toVecD 24 u1 ∧ co1Act n (toVecD 24 u2) = toVecD 24 u2) :
    pd.b.map (fun x => codeOf (co1Act n (toVecD 24 x))) ∈ tupsK (labC P.PV P.LB) P.W pd.b u1 u2 := by
  have hg := lit_g_idx hW hP
  obtain ⟨h2, hlb⟩ := lit_b_take2 hP
  have hlt : ∀ x ∈ pd.b, x < 2 ^ 24 := InvFam.bnd_spec hP.blt
  have hbfix := lit_fix hW (fun i hi => by rw [List.mem_singleton.1 hi]; exact hg) hP.bfix pd.g
    List.mem_cons_self
  set f : ℕ → ℕ := fun x => codeOf (co1Act n (toVecD 24 x)) with hfdef
  have hfv : ∀ x, toVecD 24 (f x) = co1Act n (toVecD 24 x) := fun x => toVecD_codeOf _
  have hbW : ∀ x ∈ pd.b, x ∈ P.W := fun x hx => lit_W hW hP (hlt x hx) (hbfix x hx)
  have hfW : ∀ x ∈ pd.b, f x ∈ P.W := fun x hx =>
    lit_W hW hP (codeOf_lt _) (by rw [hfv]; exact hnW _ (hbfix x hx))
  have hc : ∀ v ∈ pd.b.map f, v ∈ P.W := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
    exact hfW x hx
  have hxW : ∀ (c : List ℕ), (∀ v ∈ c, v ∈ P.W) → ∀ m, xcN c m ∈ P.W :=
    xcN_mem_of (lit_W_zero hW hP) (fun x hx y hy => lit_W_xor hW hP hx hy)
  refine mem_tupsK (by omega) (by simp) ?_ ?_ ?_
  · rw [← List.map_take, h2]
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    refine ⟨?_, ?_⟩
    · change codeOf (co1Act n (toVecD 24 u1)) = u1
      rw [hnu.1, codeOf_toVecD hu₁]
    · change codeOf (co1Act n (toVecD 24 u2)) = u2
      rw [hnu.2, codeOf_toVecD hu₂]
  · intro i hi _
    exact hc _ (getD_mem_of_lt 0 hi)
  · intro m _
    rw [xcK_eq, xcK_eq, lit_lab hP (hxW _ hc m), lit_lab hP (hxW _ hbW m)]
    have hc' : ∀ v ∈ pd.b.map f, v < 2 ^ 24 := fun v hv => lit_W_lt hP (hc v hv)
    refine lab_inv hL (n := n) (xcN_lt hlt m) (xcN_lt hc' m) ?_
    refine xcN_equiv pd.b _ (by simp) (fun i hi => ?_) m
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, hfv,
      List.getD_eq_getElem _ _ hi]

theorem lit_card_le_t_inf (hW : U6OK W) (hL : LSpec labU6) {pd : PrimeData} {P : PrimeW}
    (hP : PrimeOK W pd P) (N : Subgroup NativeSporadic.Co1)
    (hNW : ∀ n ∈ N, ∀ v, co1Act (regG pd.g) v = v → co1Act (regG pd.g) (co1Act n v) = co1Act n v)
    (hNu : ∀ n ∈ N, co1Act n (toVecD 24 u1) = toVecD 24 u1 ∧
      co1Act n (toVecD 24 u2) = toVecD 24 u2) :
    Nat.card N ≤ pd.t * Nat.card ↥(N ⊓ chainGrp u1 u2 pd.base pd.base.length) := by
  have hfin := finite_co1
  have htake := hP.shape
  have htl : (tupsK (labC P.PV P.LB) P.W pd.b u1 u2).length ≤ pd.t := by
    have h := ble_iff.1 hP.tup
    rwa [lenLL_eq] at h
  let bvec : Fin pd.b.length → Vec24 := fun i => toVecD 24 (pd.b.getD i 0)
  have horbit := CFSG.Sporadic.Co1.Module.Pairs.ncard_orbit_mul_card_inf_stabilizer N bvec
  have horb_le : (MulAction.orbit N bvec).ncard ≤ pd.t := by
    let T : Set (List ℕ) := {l | l ∈ tupsK (labC P.PV P.LB) P.W pd.b u1 u2}
    have hsub : MulAction.orbit N bvec ⊆
        (fun l : List ℕ => fun i : Fin pd.b.length => toVecD 24 (l.getD i 0)) '' T := by
      rintro _ ⟨⟨n, hn⟩, rfl⟩
      refine ⟨pd.b.map (fun x => codeOf (co1Act n (toVecD 24 x))),
        lit_tuple_mem hW hL hP (hNW n hn) (hNu n hn), ?_⟩
      funext i
      have hi : (i : ℕ) < pd.b.length := i.2
      change toVecD 24 ((pd.b.map (fun x => codeOf (co1Act n (toVecD 24 x)))).getD (i : ℕ) 0) =
        n • toVecD 24 (pd.b.getD (i : ℕ) 0)
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, toVecD_codeOf,
        List.getD_eq_getElem _ _ hi]
      rfl
    calc (MulAction.orbit N bvec).ncard
        ≤ ((fun l : List ℕ => fun i : Fin pd.b.length => toVecD 24 (l.getD i 0)) '' T).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ T.ncard := Set.ncard_image_le (List.finite_toSet _)
      _ ≤ (tupsK (labC P.PV P.LB) P.W pd.b u1 u2).length := by
          have : T = ((tupsK (labC P.PV P.LB) P.W pd.b u1 u2).toFinset : Set (List ℕ)) := by
            ext l; simp [T]
          rw [this, Set.ncard_coe_finset]
          exact List.toFinset_card_le _
      _ ≤ pd.t := htl
  have hstab : N ⊓ MulAction.stabilizer NativeSporadic.Co1 bvec ≤
      chainGrp u1 u2 pd.base pd.base.length := by
    rintro g ⟨-, hg⟩
    rw [mem_chainGrp]
    have hfix : ∀ i : Fin pd.b.length, co1Act g (toVecD 24 (pd.b.getD i 0)) =
        toVecD 24 (pd.b.getD i 0) := fun i => congrFun (MulAction.mem_stabilizer_iff.1 hg) i
    have hlen : 2 + pd.base.length ≤ pd.b.length := by
      have := congrArg List.length htake
      simp only [List.length_take, List.length_cons] at this
      omega
    have hentry : ∀ k < 2 + pd.base.length, pd.b.getD k 0 =
        (u1 :: u2 :: pd.base).getD k 0 := by
      intro k hk
      have hkb : k < pd.b.length := by omega
      have hkt : k < (List.take (2 + pd.base.length) pd.b).length := by
        rw [List.length_take]; omega
      have e1 : (List.take (2 + pd.base.length) pd.b).getD k 0 = pd.b.getD k 0 := by
        rw [List.getD_eq_getElem _ _ hkt, List.getD_eq_getElem _ _ hkb, List.getElem_take]
      rw [← e1, htake]
    refine ⟨?_, ?_, fun j hj => ?_⟩
    · have := hfix ⟨0, by omega⟩
      rw [hentry 0 (by omega)] at this
      exact this
    · have := hfix ⟨1, by omega⟩
      rw [hentry 1 (by omega)] at this
      exact this
    · have := hfix ⟨2 + j, by omega⟩
      have e : (u1 :: u2 :: pd.base).getD (2 + j) 0 = pd.base.getD j 0 := by
        have e2 : 2 + j = j + 1 + 1 := by omega
        rw [e2, List.getD_cons_succ, List.getD_cons_succ]
      rw [hentry (2 + j) (by omega), e] at this
      exact this
  have hcardstab : Nat.card ↥(N ⊓ MulAction.stabilizer NativeSporadic.Co1 bvec) ≤
      Nat.card ↥(N ⊓ chainGrp u1 u2 pd.base pd.base.length) :=
    Subgroup.card_le_of_le (le_inf inf_le_left hstab)
  calc Nat.card N = (MulAction.orbit N bvec).ncard *
        Nat.card ↥(N ⊓ MulAction.stabilizer NativeSporadic.Co1 bvec) := horbit.symm
    _ ≤ pd.t * Nat.card ↥(N ⊓ chainGrp u1 u2 pd.base pd.base.length) :=
      Nat.mul_le_mul horb_le hcardstab

theorem lit_card_le_tk (hW : U6OK W) (hL : LSpec labU6) {pd : PrimeData} {P : PrimeW}
    (hP : PrimeOK W pd P) (hU : Nat.card (chainGrp u1 u2 pd.base 0) = 9196830720)
    (N : Subgroup NativeSporadic.Co1)
    (hNW : ∀ n ∈ N, ∀ v, co1Act (regG pd.g) v = v → co1Act (regG pd.g) (co1Act n v) = co1Act n v)
    (hNu : ∀ n ∈ N, co1Act n (toVecD 24 u1) = toVecD 24 u1 ∧
      co1Act n (toVecD 24 u2) = toVecD 24 u2) :
    Nat.card N ≤ pd.t * pd.k := by
  have hfin := finite_co1
  refine (lit_card_le_t_inf hW hL hP N hNW hNu).trans (Nat.mul_le_mul_left _ ?_)
  exact (Subgroup.card_le_of_le inf_le_right).trans (lit_chain_le_k hW hP hU)

theorem enc_inj {x y : ℕ} (hx : Canon x) (hy : Canon y)
    (e : rowsMatrix 24 (unpackR 24 x) = rowsMatrix 24 (unpackR 24 y)) : x = y :=
  eq_of_unpackR hx hy (rowsMatrix_injective_of_valid (validRows_unpackR x) (validRows_unpackR y) e)

theorem pm_inv_of {x : NativeSporadic.Co1} {A B : ℕ} (hx : PM x A) (h : mulF 24 A B = idF 24) :
    PM x⁻¹ B := by
  unfold PM at *
  refine matHom_inv_eq ?_
  rw [hx, rM_mul, h, unpackR_idF, rowsMatrix_idRows]

theorem right_family (C : Subgroup NativeSporadic.Co1) {U : List ℕ} {ng n : ℕ} {T : STree}
    (hT : T.OK (actR U) ng (idF 24) 576 n) (gen : ℕ → NativeSporadic.Co1)
    (hgen : ∀ l < ng, gen l ∈ C) (hU : ∀ l < ng, PM (gen l) (getL 0 U l)) :
    ∃ x : ℕ → NativeSporadic.Co1, (∀ i < n, x i ∈ C ∧ PM (x i) (valF 576 (T.tab i))) ∧
      ∀ i < n, ∀ j < n, x i = x j → i = j := by
  obtain ⟨t, ht, hd⟩ := InvFam.sort_family C (fun g M => M * matHom g⁻¹)
    (fun g h M => by simp only [mul_inv_rev, map_mul, Matrix.mul_assoc])
    (fun M => by simp only [inv_one, map_one, Matrix.mul_one]) hT
    (fun X => rowsMatrix 24 (unpackR 24 X)) (fun l => (gen l)⁻¹)
    (fun l hl => C.inv_mem (hgen l hl)) Canon canon_idF
    (fun l _ y _ => by unfold actR; rw [CFSG.KC.F2W.mulW_eq]; exact canon_mulF _ _)
    (fun l hl y _ => by
      unfold actR
      rw [CFSG.KC.F2W.mulW_eq, ← rM_mul, inv_inv, ← hU l hl])
    (fun x y hx hy e => enc_inj hx hy e)
  have hone : rowsMatrix 24 (unpackR 24 (idF 24)) = 1 := by rw [unpackR_idF, rowsMatrix_idRows]
  refine ⟨fun i => (t i)⁻¹, fun i hi => ⟨C.inv_mem (ht i hi).1, ?_⟩, fun i hi j hj e => hd i hi j hj ?_⟩
  · unfold PM
    rw [(ht i hi).2.2, hone, Matrix.one_mul]
  · change (t i)⁻¹ = (t j)⁻¹ at e
    rw [hone, Matrix.one_mul, Matrix.one_mul, e]

theorem lit_class (hW : U6OK W) :
    60 * Nat.card ↥(chainGrp u1 u2 data11.base data11.base.length ⊓
      Subgroup.centralizer ({regG data11.g} : Set NativeSporadic.Co1)) ≤
      Nat.card (chainGrp u1 u2 data11.base data11.base.length) := by
  have hfin := finite_co1
  set K := chainGrp u1 u2 data11.base data11.base.length with hK
  have hcl : ∀ i ∈ cls11, i < 67 := lit_idx hW hW.clIdx
  have hfix := lit_fix hW hcl hW.clFix
  have hgen : ∀ l < 2, regG (getL 0 cls11 l) ∈ K := by
    intro l hl
    have hm : getL 0 cls11 l ∈ cls11 := InvFam.getL_mem (by rw [hW.clLen]; exact hl)
    rw [hK, mem_chainGrp]
    refine ⟨hfix _ hm u1 (by simp), hfix _ hm u2 (by simp), fun j hj => hfix _ hm _ ?_⟩
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (getD_mem_of_lt 0 hj))
  have hpm : ∀ l < 2, PM (regG (getL 0 cls11 l)) (W.reg (getL 0 cls11 l)) := fun l hl =>
    lit_pm hW (hcl _ (InvFam.getL_mem (by rw [hW.clLen]; exact hl)))
  have hinv : ∀ l < 2, PM (regG (getL 0 cls11 l))⁻¹ (getL 0 W.X l) := fun l hl =>
    pm_inv_of (hpm l hl) (beq_iff.1 ((allN_iff _ _).1 hW.clInv l hl))
  have hg11 : data11.g < 67 := by decide
  have hg := lit_pm hW hg11
  obtain ⟨t, ht, hd⟩ := InvFam.sort_family K (fun g M => matHom g * M * matHom g⁻¹)
    (fun g h M => by simp only [mul_inv_rev, map_mul, Matrix.mul_assoc])
    (fun M => by simp only [map_one, inv_one, Matrix.one_mul, Matrix.mul_one]) hW.cl
    (fun X => rowsMatrix 24 (unpackR 24 X)) (fun l => regG (getL 0 cls11 l)) hgen Canon
    hW.clCanon.symm
    (fun l _ y _ => by unfold actH; rw [CFSG.KC.F2W.mulW_eq]; exact canon_mulF _ _)
    (fun l hl y _ => by
      unfold actH
      have hl' : l < cls11.length := by rw [← InvFam.lenL_eq, hW.clLen]; exact hl
      rw [CFSG.KC.F2W.mulW_eq, CFSG.KC.F2W.mulW_eq, ← rM_mul, ← rM_mul, getL_map _ _ l hl',
        ← hpm l hl, ← hinv l hl])
    (fun x y hx hy e => enc_inj hx hy e)
  have hroot : rowsMatrix 24 (unpackR 24 (W.reg data11.g)) = matHom (regG data11.g) := hg.symm
  refine card_mul_cent_le K (regG data11.g) 60 (fun i => t i) (fun i => (ht i i.2).1)
    (fun i j e => Fin.ext (hd i i.2 j j.2 ?_))
  simp only at e
  rw [hroot, ← map_mul, ← map_mul, ← map_mul, ← map_mul, e]

theorem anyN_spec {f : ℕ → Bool} : ∀ {n : ℕ}, anyN n f = true → ∃ i < n, f i = true
  | 0, h => absurd h Bool.false_ne_true
  | n + 1, h => by
    change orB (f n) (anyN n f) = true at h
    cases hf : f n
    · rw [hf] at h
      obtain ⟨i, hi, hfi⟩ := anyN_spec h
      exact ⟨i, by omega, hfi⟩
    · exact ⟨n, by omega, hf⟩

theorem normK_spec {x g : NativeSporadic.Co1} {X G p : ℕ} (hx : PM x X) (hg : PM g G)
    (h : normK X G p = true) : ∃ j : ℕ, x * g = g ^ j * x := by
  obtain ⟨j, -, hj⟩ := anyN_spec h
  refine ⟨j + 1, matHom_injective ?_⟩
  have h1 := pm_mul hx hg
  have h2 := pm_mul (pm_pow hg (j + 1)) hx
  unfold PM at h1 h2
  rw [h1, h2, beq_iff.1 hj]

theorem lit_norm (hW : U6OK W) :
    71 ≤ Nat.card ↥(Subgroup.normalizer ((Subgroup.zpowers (regG data5.g) :
      Subgroup NativeSporadic.Co1) : Set NativeSporadic.Co1) ⊓
        (vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2))) := by
  have hfin := finite_co1
  have hn : ∀ i ∈ nrm5, i < 67 := lit_idx hW hW.nIdx
  have hfix := lit_fix hW hn hW.nFix
  have hg5 : data5.g < 67 := by decide
  have hg := lit_pm hW hg5
  have hgen : ∀ l < 2, regG (getL 0 nrm5 l) ∈ Subgroup.normalizer ((Subgroup.zpowers (regG data5.g) :
      Subgroup NativeSporadic.Co1) : Set NativeSporadic.Co1) ⊓
        (vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2)) := by
    intro l hl
    have hm : getL 0 nrm5 l ∈ nrm5 := InvFam.getL_mem (by rw [hW.nLen]; exact hl)
    obtain ⟨j, hj⟩ := normK_spec (lit_pm hW (hn _ hm)) hg (InvFam.allL_iff.1 hW.nNorm _ hm)
    exact Subgroup.mem_inf.2 ⟨mem_normalizer_zpowers hj,
      Subgroup.mem_inf.2 ⟨hfix _ hm u1 (by simp), hfix _ hm u2 (by simp)⟩⟩
  obtain ⟨x, hx, hd⟩ := right_family _ hW.nT (fun l => regG (getL 0 nrm5 l)) hgen
    (fun l hl => by
      rw [getL_map _ _ l (by rw [← InvFam.lenL_eq, hW.nLen]; exact hl)]
      exact lit_pm hW (hn _ (InvFam.getL_mem (by rw [hW.nLen]; exact hl))))
  have h120 : (71 : ℕ) ≤ 120 := by norm_num
  exact h120.trans (le_card_of_inj x (fun i hi => (hx i hi).1) hd)

theorem zerosK_le : ∀ (n : ℕ) (f : ℕ → ℕ) (s : Finset ℕ), (∀ i ∈ s, i < n ∧ f i = 0) →
    s.card ≤ zerosK n f
  | 0, f, s, hs => by
    have : s = ∅ := Finset.eq_empty_of_forall_notMem fun i hi => by have := (hs i hi).1; omega
    rw [this]
    exact Nat.zero_le _
  | n + 1, f, s, hs => by
    change s.card ≤ Nat.add (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq (f n) 0)) (zerosK n f)
    have hrest := zerosK_le n f (s.erase n) (fun i hi => by
      have h1 := hs i (Finset.mem_of_mem_erase hi)
      exact ⟨by have := Finset.ne_of_mem_erase hi; omega, h1.2⟩)
    by_cases hn : n ∈ s
    · have hf : Nat.beq (f n) 0 = true := Nat.beq_eq_true_eq _ _ ▸ (hs n hn).2
      rw [hf]
      have := Finset.card_erase_add_one hn
      change s.card ≤ 1 + zerosK n f
      omega
    · rw [Finset.erase_eq_of_notMem hn] at hrest
      exact hrest.trans (Nat.le_add_left _ _)

theorem lit_s0 (hW : U6OK W) :
    ∃ S : Subgroup NativeSporadic.Co1, Nat.card S = 729 ∧
      S ≤ vstab (toVecD 24 u1) ⊓ vstab (toVecD 24 u2) ∧
      ∀ A : Subgroup NativeSporadic.Co1, A ≤ S → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
        Nat.card A < 243 := by
  have hfin := finite_co1
  have hs : ∀ i ∈ s0gens, i < 67 := lit_idx hW hW.sIdx
  have hfix := lit_fix hW hs hW.sFix
  have hlen : ∀ l < 3, getL 0 s0gens l ∈ s0gens := fun l hl =>
    InvFam.getL_mem (by rw [hW.sLen]; exact hl)
  set gen : ℕ → NativeSporadic.Co1 := fun l => regG (getL 0 s0gens l) with hgdef
  set S := Subgroup.closure (Set.range fun l : Fin 3 => gen l) with hS
  have hgS : ∀ l < 3, gen l ∈ S := fun l hl => Subgroup.subset_closure ⟨⟨l, hl⟩, rfl⟩
  have hl3 : ∀ l < 3, l < s0gens.length := fun l hl => by rw [← InvFam.lenL_eq, hW.sLen]; exact hl
  have hpmg : ∀ l < 3, PM (gen l) (getL 0 (s0gens.map W.reg) l) := fun l hl => by
    rw [getL_map _ _ l (hl3 l hl)]
    exact lit_pm hW (hs _ (hlen l hl))
  obtain ⟨x, hx, hd⟩ := right_family S hW.sT gen hgS hpmg
  have hval : ∀ i < 729, W.s0v i = valF 576 (W.s0.tab i) := fun _ _ => rfl
  have hroot : ∃ j < 729, valF 576 (W.s0.tab j) = idF 24 :=
    (tree_sound_chunks hW.sT.1 hW.sT.2).2.2.2 (by norm_num)
  have hcl := close_sound hW.sC
  have hord : ∀ l < 3, gen l ^ getL 0 s0ord l = 1 := by
    intro l hl
    apply matHom_injective
    have h := pm_pow (hpmg l hl) (getL 0 s0ord l)
    unfold PM at h
    rw [h, getL_map _ _ l (hl3 l hl), beq_iff.1 ((allN_iff _ _).1 hW.sOrd l hl), map_one, unpackR_idF,
      rowsMatrix_idRows]
  have hmulr : ∀ y, (∃ i < 729, PM y (valF 576 (W.s0.tab i))) → ∀ l < 3,
      ∃ i < 729, PM (y * gen l) (valF 576 (W.s0.tab i)) := by
    rintro y ⟨i, hi, hyi⟩ l hl
    obtain ⟨he, hact⟩ := hcl i hi l hl
    refine ⟨_, he, ?_⟩
    rw [← hact]
    unfold actR
    rw [CFSG.KC.F2W.mulW_eq]
    exact pm_mul hyi (hpmg l hl)
  have hpow : ∀ y, (∃ i < 729, PM y (valF 576 (W.s0.tab i))) → ∀ l < 3, ∀ k : ℕ,
      ∃ i < 729, PM (y * gen l ^ k) (valF 576 (W.s0.tab i)) := by
    intro y hy l hl k
    induction k with
    | zero => simpa using hy
    | succ k ih =>
      rw [pow_succ, ← mul_assoc]
      exact hmulr _ ih l hl
  have hall : ∀ y ∈ S, ∃ i < 729, PM y (valF 576 (W.s0.tab i)) := by
    intro y hy
    refine Subgroup.closure_induction_right (p := fun y _ => ∃ i < 729, PM y (valF 576 (W.s0.tab i)))
      ?_ ?_ ?_ hy
    · obtain ⟨j, hj, hjv⟩ := hroot
      exact ⟨j, hj, by rw [hjv]; exact pm_one⟩
    · rintro z - _ ⟨l, rfl⟩ hz
      exact hmulr z hz l l.2
    · rintro z - _ ⟨l, rfl⟩ hz
      have hinv : (gen l)⁻¹ = gen l ^ (getL 0 s0ord l - 1) := by
        have h1 := hord l l.2
        have hpos : 1 ≤ getL 0 s0ord l := by
          rcases (by omega : (l : ℕ) = 0 ∨ (l : ℕ) = 1 ∨ (l : ℕ) = 2) with h | h | h <;>
            · rw [h]; decide
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hpos, h1]
      rw [hinv]
      exact hpow z hz l l.2 _
  have hxS : ∀ i < 729, x i ∈ S := fun i hi => (hx i hi).1
  have hpt : ∀ y ∈ S, ∃ i < 729, y = x i := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := hall y hy
    exact ⟨i, hi, matHom_injective (hyi.trans (hx i hi).2.symm)⟩
  have hcard : Nat.card S = 729 := by
    refine le_antisymm ?_ (le_card_of_inj x hxS hd)
    have e : Nat.card S = (S : Set NativeSporadic.Co1).ncard := Nat.card_coe_set_eq _
    rw [e]
    have hsub : (S : Set NativeSporadic.Co1) ⊆ x '' Set.Iio 729 := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := hpt y hy
      exact ⟨i, hi, rfl⟩
    calc (S : Set NativeSporadic.Co1).ncard ≤ (x '' Set.Iio 729).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (Set.Iio 729).ncard := Set.ncard_image_le (Set.finite_Iio 729)
      _ = 729 := Set.ncard_Iio_nat 729
  have hcent : ∀ i < 729, W.c0 i ≠ 0 →
      Nat.card ↥(S ⊓ Subgroup.centralizer ({x i} : Set NativeSporadic.Co1)) < 243 := by
    intro i hi hne
    have hw := (allN_iff _ _).1 hW.sW i hi
    unfold witK at hw
    have hw0 : Nat.beq (W.c0 i) 0 = false := beq_false_of_ne hne
    rw [hw0] at hw
    change andB _ _ = true at hw
    obtain ⟨hw1, hw2⟩ := andB_true_iff.1 hw
    have hpair : ∀ t < 3, fget (W.c0 i) (Nat.mul 2 t) 10 < 729 ∧
        fget (W.c0 i) (Nat.succ (Nat.mul 2 t)) 10 < 729 ∧
        x (fget (W.c0 i) (Nat.mul 2 t) 10) * x i =
          x (fget (W.c0 i) (Nat.succ (Nat.mul 2 t)) 10) * x (fget (W.c0 i) (Nat.mul 2 t) 10) := by
      intro t ht
      have h := (allN_iff _ _).1 hw1 t ht
      obtain ⟨h1, h2⟩ := andB_true_iff.1 h
      obtain ⟨h2, h3⟩ := andB_true_iff.1 h2
      have hj := blt_iff.1 h1
      have hk := blt_iff.1 h2
      refine ⟨hj, hk, matHom_injective ?_⟩
      have e1 := pm_mul (hx _ hj).2 (hx i hi).2
      have e2 := pm_mul (hx _ hk).2 (hx _ hj).2
      unfold PM at e1 e2
      rw [e1, e2, ← CFSG.KC.F2W.mulW_eq, ← CFSG.KC.F2W.mulW_eq]
      exact congrArg _ (congrArg _ (beq_iff.1 h3))
    have hdist := hw2
    simp only [andB_true_iff] at hdist
    obtain ⟨d01, d02, d12, d0i, d1i, d2i⟩ := hdist
    have nb : ∀ {a b : ℕ}, notB (Nat.beq a b) = true → a ≠ b := fun {a b} h e => by
      rw [e, Nat.beq_refl] at h
      exact Bool.false_ne_true h
    obtain ⟨j0, k0, e0⟩ := hpair 0 (by norm_num)
    obtain ⟨j1, k1, e1⟩ := hpair 1 (by norm_num)
    obtain ⟨j2, k2, e2⟩ := hpair 2 (by norm_num)
    change fget (W.c0 i) 0 10 < 729 at j0
    change fget (W.c0 i) 1 10 < 729 at k0
    change x (fget (W.c0 i) 0 10) * x i = x (fget (W.c0 i) 1 10) * x (fget (W.c0 i) 0 10) at e0
    change fget (W.c0 i) 2 10 < 729 at j1
    change fget (W.c0 i) 3 10 < 729 at k1
    change x (fget (W.c0 i) 2 10) * x i = x (fget (W.c0 i) 3 10) * x (fget (W.c0 i) 2 10) at e1
    change fget (W.c0 i) 4 10 < 729 at j2
    change fget (W.c0 i) 5 10 < 729 at k2
    change x (fget (W.c0 i) 4 10) * x i = x (fget (W.c0 i) 5 10) * x (fget (W.c0 i) 4 10) at e2
    let c : Fin 4 → NativeSporadic.Co1 := ![1, x (fget (W.c0 i) 0 10), x (fget (W.c0 i) 2 10),
      x (fget (W.c0 i) 4 10)]
    let k : Fin 4 → ℕ := ![i, fget (W.c0 i) 1 10, fget (W.c0 i) 3 10, fget (W.c0 i) 5 10]
    have hk729 : ∀ a, k a < 729 := by
      intro a
      fin_cases a
      · exact hi
      · exact k0
      · exact k1
      · exact k2
    have hck : ∀ a, c a * x i * (c a)⁻¹ = x (k a) := by
      intro a
      fin_cases a
      · simp [c, k]
      · change x (fget (W.c0 i) 0 10) * x i * (x (fget (W.c0 i) 0 10))⁻¹ = x (fget (W.c0 i) 1 10)
        rw [e0, mul_inv_cancel_right]
      · change x (fget (W.c0 i) 2 10) * x i * (x (fget (W.c0 i) 2 10))⁻¹ = x (fget (W.c0 i) 3 10)
        rw [e1, mul_inv_cancel_right]
      · change x (fget (W.c0 i) 4 10) * x i * (x (fget (W.c0 i) 4 10))⁻¹ = x (fget (W.c0 i) 5 10)
        rw [e2, mul_inv_cancel_right]
    have hkinj : Function.Injective k := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> first
        | rfl
        | (exfalso; simp only [k] at hab
           first
            | exact nb d01 hab | exact nb d01 hab.symm | exact nb d02 hab | exact nb d02 hab.symm
            | exact nb d12 hab | exact nb d12 hab.symm | exact nb d0i hab | exact nb d0i hab.symm
            | exact nb d1i hab | exact nb d1i hab.symm | exact nb d2i hab | exact nb d2i hab.symm)
    have hcS : ∀ a, c a ∈ S := by
      intro a
      fin_cases a
      · exact S.one_mem
      · exact hxS _ j0
      · exact hxS _ j1
      · exact hxS _ j2
    have h4 := card_mul_cent_le S (x i) 4 c hcS (fun a b e => by
      have e' : x (k a) = x (k b) := by rw [← hck a, ← hck b]; exact e
      exact hkinj (hd _ (hk729 a) _ (hk729 b) e'))
    rw [hcard] at h4
    omega
  refine ⟨S, hcard, ?_, fun A hAS hcomm => ?_⟩
  · rw [hS, Subgroup.closure_le]
    rintro _ ⟨l, rfl⟩
    have hm := hlen l l.2
    exact Subgroup.mem_inf.2 ⟨hfix _ hm u1 (by simp), hfix _ hm u2 (by simp)⟩
  · by_contra hA
    have hAz : ∀ a ∈ A, ∃ i < 729, a = x i ∧ W.c0 i = 0 := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := hpt a (hAS ha)
      refine ⟨i, hi, rfl, by_contra fun hne => ?_⟩
      have hle : A ≤ S ⊓ Subgroup.centralizer ({x i} : Set NativeSporadic.Co1) := fun b hb =>
        Subgroup.mem_inf.2 ⟨hAS hb, Subgroup.mem_centralizer_singleton_iff.2 (hcomm b hb _ ha)⟩
      have := Subgroup.card_le_of_le hle
      have := hcent i hi hne
      omega
    choose! idx hidx using hAz
    classical
    let s : Finset ℕ := (Set.toFinite (A : Set NativeSporadic.Co1)).toFinset.image idx
    have hsz : s.card ≤ zerosK 729 W.c0 := zerosK_le 729 W.c0 s (by
      intro i his
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 his
      rw [Set.Finite.mem_toFinset] at ha
      exact ⟨(hidx a ha).1, (hidx a ha).2.2⟩)
    have hinjA : Set.InjOn idx (A : Set NativeSporadic.Co1) := by
      intro a ha b hb e
      rw [(hidx a ha).2.1, (hidx b hb).2.1, e]
    have hsc : s.card = Nat.card A := by
      rw [Finset.card_image_of_injOn (by simpa using hinjA), ← Set.ncard_eq_toFinset_card _]
      exact (Nat.card_coe_set_eq _).symm
    have := hW.sB
    omega

end CFSG.Sporadic.Co1.Module.U6Odd

end
