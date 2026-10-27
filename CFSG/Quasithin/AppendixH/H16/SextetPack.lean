module

public import CFSG.Quasithin.Background.HLUCode24Gen
public import CFSG.Quasithin.Background.HZCoc24Pack
public import CFSG.Quasithin.AppendixH.H16.MaskChief

public section

namespace CFSG.ASVolI.H16.SxPack

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.LU24
  CFSG.Quasithin.H.Coc24Pack

@[expose] def allLt (f : ℕ → Bool) (n : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => Bool.rec false acc (f k)) n

@[expose] def anyLt (f : ℕ → Bool) (n : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k acc => Bool.rec acc true (f k)) n

theorem of_allLt {f : ℕ → Bool} : ∀ {n : ℕ}, allLt f n = true → ∀ k < n, f k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h, k, hk => by
    have h' : Bool.rec false (allLt f n) (f n) = true := h
    cases hf : f n
    · rw [hf] at h'
      exact absurd h' Bool.false_ne_true
    · rw [hf] at h'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact of_allLt h' k hk
      · exact hf

theorem exists_of_anyLt {f : ℕ → Bool} : ∀ {n : ℕ}, anyLt f n = true → ∃ k < n, f k = true
  | 0, h => absurd h Bool.false_ne_true
  | n + 1, h => by
    have h' : Bool.rec (anyLt f n) true (f n) = true := h
    cases hf : f n
    · rw [hf] at h'
      obtain ⟨k, hk, hfk⟩ := exists_of_anyLt h'
      exact ⟨k, Nat.lt_succ_of_lt hk, hfk⟩
    · exact ⟨n, Nat.lt_succ_self n, hf⟩

@[expose] def actK (cs : List ℕ) (m : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun c _ ih m => Nat.xor (Bool.rec 0 c (Nat.beq (Nat.mod m 2) 1)) (ih (Nat.div m 2))) cs m

theorem actK_eq : ∀ (cs : List ℕ) (m : ℕ), actK cs m = actM cs m
  | [], _ => rfl
  | c :: cs, m => by
    have h : actK (c :: cs) m = Bool.rec 0 c (Nat.beq (m % 2) 1) ^^^ actK cs (m / 2) := rfl
    rw [h, actK_eq cs, actM]
    congr 1
    cases hb : Nat.beq (m % 2) 1
    · have hm : ¬ m % 2 = 1 := fun h' => by rw [h'] at hb; exact absurd hb (by decide)
      rw [if_neg hm]
    · rw [if_pos (Nat.eq_of_beq_eq_true hb)]

@[expose] def parK (k m : ℕ) : Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => false)
    (fun _ ih m => Bool.rec (ih (Nat.div m 2)) (Bool.rec true false (ih (Nat.div m 2)))
      (Nat.beq (Nat.mod m 2) 1)) k m

theorem parK_succ (k m : ℕ) :
    parK (k + 1) m = ((m % 2 == 1) != parK k (m / 2)) := by
  have h : parK (k + 1) m = Bool.rec (parK k (m / 2)) (Bool.rec true false (parK k (m / 2)))
      (Nat.beq (m % 2) 1) := rfl
  rw [h]
  have hb : (m % 2 == 1) = Nat.beq (m % 2) 1 := rfl
  rw [hb]
  cases Nat.beq (m % 2) 1 <;> cases parK k (m / 2) <;> rfl

@[expose] def memB (B x : ℕ) : Bool := Nat.blt 0 (Nat.land 1 (Nat.shiftRight B x))

theorem memB_eq (B x : ℕ) : memB B x = B.testBit x := by
  change Nat.blt 0 (1 &&& (B >>> x)) = (1 &&& (B >>> x) != 0)
  generalize 1 &&& (B >>> x) = t
  cases t <;> rfl

@[expose] def bitsOf (L : List ℕ) : ℕ := L.foldr (fun u acc => acc ||| 1 <<< u) 0

theorem mem_of_testBit : ∀ (L : List ℕ) (x : ℕ), (bitsOf L).testBit x = true → x ∈ L
  | [], x, h => by
    change (0 : ℕ).testBit x = true at h
    rw [Nat.zero_testBit] at h
    exact absurd h Bool.false_ne_true
  | u :: L, x, h => by
    change (bitsOf L ||| 1 <<< u).testBit x = true at h
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true] at h
    rcases h with h | h
    · exact List.mem_cons_of_mem u (mem_of_testBit L x h)
    · rw [of_decide_eq_true h]
      exact List.mem_cons_self

theorem mem_of_memB {L : List ℕ} {B x : ℕ} (hB : bitsOf L = B) (h : memB B x = true) : x ∈ L := by
  rw [memB_eq, ← hB] at h
  exact mem_of_testBit L x h

@[expose] def usBits : ℕ :=
  314233197641542515516479127906044010241710278827100376266394244813023094122941755944876063720655461415891962281466908050038039634673764889340994982329854576553934633680535778436846302126175696319892640548601979185824378503906104290350576503365183339677978216902198847115102644689503462958792711164064026827097588090938276022128282555156575521744863098981028473515105732183021104426576683952574493691180048047073071316787531447366957790495190004443348228237471072689038773108189095727161304576340127450462450106074241901684064411569708710608324009744400385

theorem usBits_eq : bitsOf uSMasks = usBits := by
  decide +kernel

theorem mem_uS {x : ℕ} (h : memB usBits x = true) : x ∈ uSMasks := mem_of_memB usBits_eq h

@[expose] def xcT : ℕ :=
  430666557359749994363776197968129681291999612559852159092535745836283761152247267348802881281524741567472964346359752765363908289660180262734579166892744102901152902796847390883494214780113403920849825784515762940196733822346065157311473279835403516890639808232226925943661174448080395289811391377661362176

@[expose] def xcK (J : ℕ) : ℕ := Nat.land (Nat.shiftRight xcT (Nat.mul 16 J)) 65535

@[expose] def g1K : ℕ := 897641350104222698714232081601768518

@[expose] def g2K : ℕ := 187140310991371938096741885074749127

@[expose] def tK : ℕ := 210612956321353997592989794072419700

@[expose] def tiK : ℕ := 100398093789040343632513102951832020

theorem codes_dec : sxG1Arr = dec g1K ∧ sxG2Arr = dec g2K ∧ sxTArr = dec tK ∧ sxTInv = dec tiK := by
  unfold dec
  decide +kernel

@[expose] def ksK (i : ℕ) : ℕ := wK [g1K, g2K] (ksWord6 i)

theorem ks6Arr_dec (i : ℕ) : ks6Arr i = dec (ksK i) := by
  rw [ks6Arr, codes_dec.1, codes_dec.2.1, ksK, ← wArr_dec]
  rfl

theorem ks6_list : (List.range 6).map ks6Arr = ((List.range 6).map ksK).map dec := by
  rw [List.map_map]
  exact List.map_congr_left fun i _ => ks6Arr_dec i

@[expose] def conjB (S S' : ℕ → ℕ) (i : ℕ) : Bool :=
  Bool.rec false
    (Nat.beq (cK (cK tiK (ksK i)) tK) (wK ((List.range 6).map ksK) (subW (S' i))))
    (Nat.beq (cK (cK tK (ksK i)) tiK) (wK ((List.range 6).map ksK) (subW (S i))))

theorem conj_of_conjB (S S' : ℕ → ℕ) (h : allLt (conjB S S') 6 = true) : ∀ i < 6,
    cArr (cArr sxTArr (ks6Arr i)) sxTInv = wArr ((List.range 6).map ks6Arr) (subW (S i)) ∧
      cArr (cArr sxTInv (ks6Arr i)) sxTArr = wArr ((List.range 6).map ks6Arr) (subW (S' i)) := by
  intro i hi
  have hb' := of_allLt h i hi
  unfold conjB at hb'
  obtain ⟨_, _, hT, hTi⟩ := codes_dec
  rw [ks6_list, hT, hTi, ks6Arr_dec, wArr_dec, wArr_dec, cArr_dec, cArr_dec, cArr_dec, cArr_dec]
  cases h1 : Nat.beq (cK (cK tK (ksK i)) tiK) (wK ((List.range 6).map ksK) (subW (S i)))
  · rw [h1] at hb'
    exact absurd hb' Bool.false_ne_true
  · rw [h1] at hb'
    exact ⟨dec_inj (Nat.eq_of_beq_eq_true h1), dec_inj (Nat.eq_of_beq_eq_true hb')⟩

@[expose] def allLt64 (f : ℕ → Bool) (a : ℕ) : Bool :=
  allLt (fun q => allLt (fun r => f (Nat.add (Nat.mul 64 q) r)) 64) a

theorem of_allLt64 {f : ℕ → Bool} {a : ℕ} (h : allLt64 f a = true) : ∀ k < 64 * a, f k = true := by
  intro k hk
  have hq : k / 64 < a := by omega
  have h1 : f (Nat.add (Nat.mul 64 (k / 64)) (k % 64)) = true :=
    of_allLt (of_allLt h (k / 64) hq) (k % 64) (Nat.mod_lt _ (by norm_num))
  have hk' : Nat.add (Nat.mul 64 (k / 64)) (k % 64) = k := Nat.div_add_mod k 64
  rwa [hk'] at h1

theorem allLt_of {f : ℕ → Bool} : ∀ {n : ℕ}, (∀ k < n, f k = true) → allLt f n = true
  | 0, _ => rfl
  | n + 1, h => by
    have h' : allLt f (n + 1) = Bool.rec false (allLt f n) (f n) := rfl
    rw [h', h n (Nat.lt_succ_self n)]
    exact allLt_of fun k hk => h k (Nat.lt_succ_of_lt hk)

theorem parK_eq {p : ℕ → ℕ → Bool} (h0 : ∀ m, p 0 m = false)
    (hs : ∀ k m, p (k + 1) m = ((m % 2 == 1) != p k (m / 2))) : ∀ k m, p k m = parK k m
  | 0, m => h0 m
  | k + 1, m => by rw [hs, parK_succ, parK_eq h0 hs k]

@[expose] def beqB (a b : Bool) : Bool := Bool.rec (Bool.rec true false b) b a

theorem eq_of_beqB {a b : Bool} (h : beqB a b = true) : a = b := by
  cases a <;> cases b
  · rfl
  · exact absurd h Bool.false_ne_true
  · exact absurd h Bool.false_ne_true
  · rfl

@[expose] def andB (x y : Bool) : Bool := Bool.rec false y x

theorem andB_eq_true {x y : Bool} (h : andB x y = true) : x = true ∧ y = true := by
  cases x
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

@[expose] def par10 (m : ℕ) : Bool := parK 11 (Nat.land m 1192)

@[expose] def presB (T : List ℕ) (m : ℕ) : Bool :=
  andB (beqB (par10 (actK sxG1C m)) (par10 m))
    (andB (beqB (par10 (actK sxG2C m)) (par10 m)) (beqB (par10 (actK T m)) (par10 m)))

theorem presB_spec {T : List ℕ} {m : ℕ} (h : presB T m = true) :
    parK 11 (actM sxG1C m &&& 1192) = parK 11 (m &&& 1192) ∧
      parK 11 (actM sxG2C m &&& 1192) = parK 11 (m &&& 1192) ∧
      parK 11 (actM T m &&& 1192) = parK 11 (m &&& 1192) := by
  unfold presB at h
  obtain ⟨h1, h23⟩ := andB_eq_true h
  obtain ⟨h2, h3⟩ := andB_eq_true h23
  rw [← actK_eq, ← actK_eq, ← actK_eq]
  exact ⟨eq_of_beqB h1, eq_of_beqB h2, eq_of_beqB h3⟩

@[expose] def transvB (c : ℕ → ℕ) (i m : ℕ) : Bool :=
  Bool.rec (memB usBits (Nat.xor (actK (ksC6 i) m) m))
    (memB usBits (Nat.xor (Nat.xor (actK (ksC6 i) m) m) (c i))) (par10 m)

theorem transvB_spec {c : ℕ → ℕ} {i m : ℕ} (h : transvB c i m = true) :
    (parK 11 (m &&& 1192) = false → (actM (ksC6 i) m ^^^ m) ∈ uSMasks) ∧
      (parK 11 (m &&& 1192) = true → (actM (ksC6 i) m ^^^ m ^^^ c i) ∈ uSMasks) := by
  rw [← actK_eq]
  have h' : Bool.rec (memB usBits (actK (ksC6 i) m ^^^ m))
      (memB usBits (actK (ksC6 i) m ^^^ m ^^^ c i)) (parK 11 (m &&& 1192)) = true := h
  refine ⟨fun hq => ?_, fun hq => ?_⟩
  · rw [hq] at h'
    exact mem_uS h'
  · rw [hq] at h'
    exact mem_uS h'

@[expose] def spanB (m : ℕ) : Bool :=
  Bool.rec (anyLt (fun J => memB usBits (Nat.xor m (xcK J))) 64) true (par10 m)

theorem spanB_spec {m : ℕ} (h : spanB m = true) (hq : parK 11 (m &&& 1192) = false) :
    ∃ J < 64, (m ^^^ xcK J) ∈ uSMasks := by
  have h' : Bool.rec (anyLt (fun J => memB usBits (m ^^^ xcK J)) 64) true
      (parK 11 (m &&& 1192)) = true := h
  rw [hq] at h'
  obtain ⟨J, hJ, hm⟩ := exists_of_anyLt h'
  exact ⟨J, hJ, mem_uS hm⟩

@[expose] def fixB (m : ℕ) : Bool :=
  Bool.rec true (memB usBits m) (allLt (fun i => Nat.beq (actK (ksC6 i) m) m) 6)

theorem fixB_spec {m : ℕ} (h : fixB m = true) (hf : ∀ i < 6, actM (ksC6 i) m = m) :
    m ∈ uSMasks := by
  have ha : allLt (fun i => Nat.beq (actK (ksC6 i) m) m) 6 = true :=
    allLt_of fun i hi => by
      rw [actK_eq, hf i hi]
      exact Nat.beq_refl m
  have h' : Bool.rec true (memB usBits m) (allLt (fun i => Nat.beq (actK (ksC6 i) m) m) 6) =
    true := h
  rw [ha] at h'
  exact mem_uS h'

@[expose] def redB (E : List ℕ) (m : ℕ) : Bool :=
  Bool.rec (Nat.beq (reduceBy E m) 0) true (par10 m)

@[expose] def minK (a b : ℕ) : ℕ := Bool.rec b a (Nat.ble a b)

theorem minK_eq (a b : ℕ) : minK a b = min a b := by
  unfold minK
  cases h : Nat.ble a b
  · have hab : ¬ a ≤ b := fun h' => by rw [Nat.ble_eq_true_of_le h'] at h; exact absurd h (by decide)
    rw [Nat.min_def, if_neg hab]
  · rw [Nat.min_def, if_pos (Nat.le_of_ble_eq_true h)]

@[expose] def redK (bs : List ℕ) (v : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun v => v) (fun p _ ih v => ih (minK v (Nat.xor v p))) bs v

theorem redK_eq : redK = reduceBy := by
  funext bs
  induction bs with
  | nil => rfl
  | cons p bs ih =>
    funext v
    have h : redK (p :: bs) v = redK bs (minK v (v ^^^ p)) := rfl
    rw [h, ih, minK_eq]
    rfl

@[expose] def echStepK (bs : List ℕ) (r : ℕ) : List ℕ := Bool.rec (bs ++ [r]) bs (Nat.beq r 0)

@[expose] def echK (l bs : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ → List ℕ) (fun bs => bs)
    (fun v _ ih bs => ih (echStepK bs (redK bs v))) l bs

theorem echK_eq (l : List ℕ) : ∀ bs, echK l bs =
    l.foldl (fun bs v => if reduceBy bs v = 0 then bs else bs ++ [reduceBy bs v]) bs := by
  induction l with
  | nil => intro bs; rfl
  | cons v l ih =>
    intro bs
    have h : echK (v :: l) bs = echK l (echStepK bs (redK bs v)) := rfl
    rw [h, ih, List.foldl_cons, redK_eq]
    congr 1
    unfold echStepK
    cases hb : Nat.beq (reduceBy bs v) 0
    · rw [if_neg (Nat.ne_of_beq_eq_false hb)]
    · rw [if_pos (Nat.eq_of_beq_eq_true hb)]

@[expose] def wActK (cs : List (List ℕ)) (u : List ℕ) (m : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun m => m) (fun i _ ih m => actK (cs.getD i []) (ih m)) u m

theorem wActK_eq : wActK = CFSG.Quasithin.H.Coc.wAct := by
  funext cs u
  induction u with
  | nil => rfl
  | cons i u ih =>
    funext m
    have h : wActK cs (i :: u) m = actK (cs.getD i []) (wActK cs u m) := rfl
    rw [h, ih, actK_eq]
    rfl

@[expose] def allK (l : List ℕ) (f : ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => Bool.rec false ih (f a)) l

theorem allK_eq (l : List ℕ) (f : ℕ → Bool) : allK l f = l.all f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have h : allK (a :: l) f = Bool.rec false (allK l f) (f a) := rfl
    rw [h, ih, List.all_cons]
    cases f a <;> rfl

theorem beq_nat (a b : ℕ) : (a == b) = Nat.beq a b := by
  rw [Bool.eq_iff_iff]
  simp [Nat.beq_eq]

@[expose] def chiefK (cs : List (List ℕ)) (bx by_ : List ℕ) (words : List (List ℕ)) : Bool :=
  allK (combos by_) fun m =>
    Bool.rec (allK by_ fun b => Nat.beq (redK (echK (bx ++ words.map fun u => wActK cs u m) []) b) 0)
      true (Nat.beq (redK (echK bx []) m) 0)

theorem redK_apply (bs : List ℕ) (v : ℕ) : redK bs v = reduceBy bs v := by rw [redK_eq]

theorem wActK_apply (cs : List (List ℕ)) (u : List ℕ) (m : ℕ) :
    wActK cs u m = CFSG.Quasithin.H.Coc.wAct cs u m := by rw [wActK_eq]

theorem rec_or (b y : Bool) : Bool.rec (motive := fun _ => Bool) y true b = (b || y) := by
  cases b <;> rfl

theorem chiefCheck_eq (cs : List (List ℕ)) (bx by_ : List ℕ) (words : List (List ℕ)) :
    chiefCheck cs bx by_ words = chiefK cs bx by_ words := by
  unfold chiefCheck chiefK echelon
  simp only [allK_eq, redK_apply, wActK_apply, echK_eq, rec_or, ← beq_nat]

theorem redB_spec {E : List ℕ} {m : ℕ} (h : redB E m = true) (hq : parK 11 (m &&& 1192) = false) :
    reduceBy E m = 0 := by
  have h' : Bool.rec (Nat.beq (reduceBy E m) 0) true (parK 11 (m &&& 1192)) = true := h
  rw [hq] at h'
  exact Nat.eq_of_beq_eq_true h'

end CFSG.ASVolI.H16.SxPack
