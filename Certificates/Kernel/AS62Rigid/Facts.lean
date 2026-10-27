module

public import Certificates.Kernel.AS62Rigid.Checks
public import CFSG.Certificates.Kernel.AS62RigidSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAS62

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.AS62 CFSG.LargeExtraspecial.AS62
  CFSG.LargeExtraspecial.AS62.Rigid CFSG.LargeExtraspecial.AS62.Sem CFSG.Quasithin.H13.F431.U42Aut

local notation "U" => unpack 45 6

theorem idOK45 : idK 45 6 (mask 6) = true := by quickRfl

theorem bAnd_iff2 {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true :=
  (CFSG.KS.bAnd_iff a b).1 h

theorem allK_spec {n : Nat} {f : Nat → Bool} (h : allK n f = true) : ∀ i < n, f i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    change bAnd(f n, allK n f) = true at h
    have h' := bAnd_iff2 h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih h'.2 i hi
    · exact h'.1

theorem le_of_blt_false {a b : Nat} (h : Nat.blt a b = false) : b ≤ a := by
  by_contra h'
  rw [Nat.blt_eq.mpr (by omega)] at h
  exact Bool.false_ne_true h.symm

theorem anyK_spec {n : Nat} {f : Nat → Bool} (h : anyK n f = true) : ∃ i < n, f i = true := by
  induction n with
  | zero => exact absurd h Bool.false_ne_true
  | succ n ih =>
    change bIf(f n, true, anyK n f) = true at h
    cases hf : f n
    · rw [hf] at h
      obtain ⟨i, hi, e⟩ := ih h
      exact ⟨i, by omega, e⟩
    · exact ⟨n, by omega, hf⟩

theorem bIf_true {c x : Bool} (h : bIf(c, x, true) = true) (hc : c = true) : x = true := by
  rw [hc] at h
  exact h

theorem cn_facts : Cn PID ∧ Cn FH ∧ (∀ k < 6, Cn (GK k) ∧ Cn (GKI k)) ∧
    (∀ k < 192, Cn (BK k) ∧ Cn (BKI k)) ∧ (∀ k < 960, Cn (P2K k) ∧ Cn (P2KI k)) := by
  have h := ckCanon
  simp only [ckCanonB, CFSG.KS.bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, fun k hk => bAnd_iff2 (allK_spec h3 k hk),
    fun k hk => bAnd_iff2 (allK_spec h4 k hk), fun k hk => bAnd_iff2 (allK_spec h5 k hk)⟩

theorem cnPID : Cn PID := cn_facts.1
theorem cnFH : Cn FH := cn_facts.2.1
theorem cnG {k : Nat} (hk : k < 6) : Cn (GK k) ∧ Cn (GKI k) := cn_facts.2.2.1 k hk
theorem cnB {k : Nat} (hk : k < 192) : Cn (BK k) ∧ Cn (BKI k) := cn_facts.2.2.2.1 k hk
theorem cnP2 {k : Nat} (hk : k < 960) : Cn (P2K k) ∧ Cn (P2KI k) := cn_facts.2.2.2.2 k hk

theorem cnY {j : Nat} (hj : j < 3) : Cn (YP j) ∧ Cn (YPI j) := by
  have c4 := cnG (k := 4) (by norm_num)
  interval_cases j
  · exact ⟨cnPID, cnPID⟩
  · exact c4
  · exact ⟨cn_pc c4.1 c4.1, cn_pc c4.2 c4.2⟩

theorem cnP1 {i : Nat} (hi : i < 576) : Cn (P1E i) ∧ Cn (P1I i) := by
  have hy := cnY (j := i / 192) (by omega)
  have hb := cnB (k := i % 192) (by omega)
  exact ⟨cn_pc hy.1 hb.1, cn_pc hb.2 hy.2⟩

theorem cnBH {f : Nat} (hf : f < 384) : Cn (BHE f) ∧ Cn (BHI f) := by
  unfold BHE BHI
  cases h : Nat.blt f 192
  · have hb := cnB (k := f - 192) (by have := le_of_blt_false h; omega)
    exact ⟨cn_pc hb.1 cnFH, cn_pc cnFH hb.2⟩
  · exact cnB (Nat.blt_eq.mp h)

theorem list_toArray_eq (l : List Nat) (P : Nat) (hl : l.length = 45)
    (h : ∀ i < 45, l.getD i 0 = pg 6 (mask 6) P i) : l.toArray = U P := by
  apply Array.ext
  · simp [hl, unpack_size45]
  · intro i h1 h2
    have hi : i < 45 := by simpa [hl] using h1
    rw [List.getElem_toArray, ← List.getD_eq_getElem l 0, h i hi]
    simp only [unpack, Array.getElem_ofFn]

theorem gen_eq {k : Nat} (hk : k < 6) : genA k = U (GK k) ∧ genInvA k = U (GKI k) := by
  have h := allK_spec ckG k hk
  obtain ⟨h1, h⟩ := bAnd_iff2 h
  obtain ⟨h2, h⟩ := bAnd_iff2 h
  have h3 := allK_spec h
  exact ⟨list_toArray_eq _ _ (Nat.eq_of_beq_eq_true h1) fun i hi =>
      Nat.eq_of_beq_eq_true (bAnd_iff2 (h3 i hi)).1,
    list_toArray_eq _ _ (Nat.eq_of_beq_eq_true h2) fun i hi =>
      Nat.eq_of_beq_eq_true (bAnd_iff2 (h3 i hi)).2⟩

theorem fhat_eq : fhatA' = U FH := by
  have h := ckFH
  simp only [ckFHB, CFSG.KS.bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  exact list_toArray_eq _ _ (Nat.eq_of_beq_eq_true h1) fun i hi =>
    Nat.eq_of_beq_eq_true (allK_spec h2 i hi)

theorem idA_eq : idA = U PID := idA_unpack idOK45

theorem letA_eq {k : Nat} {code : Fin k → Nat} (hc : ∀ i, code i < 6) (a : Fin k × Bool) :
    letA (code a.1, a.2) = U (Bool.rec (motive := fun _ => Nat) (GKI (code a.1)) (GK (code a.1))
      a.2) := by
  have := gen_eq (hc a.1)
  unfold letA
  cases a.2
  · exact this.2
  · exact this.1

theorem cnGc {k : Nat} {code : Fin k → Nat} (hc : ∀ i, code i < 6) :
    ∀ l, Cn (GK (code l)) ∧ Cn (GKI (code l)) := fun l => cnG (hc l)

theorem bTab_eq : bTab () = Array.ofFn (n := 192) fun k => (U (BK k.val), U (BKI k.val)) := by
  unfold bTab
  refine congrArg (Array.ofFn (n := 192)) (funext fun k => ?_)
  have h := List.all_eq_true.1 ckBW k (List.mem_finRange k)
  obtain ⟨h1, h2⟩ := bAnd_iff2 h
  have hc : ∀ i : Fin 4, (fun i : Fin 4 => i.val) i < 6 := fun i => by have := i.2; simp; omega
  unfold bPair
  rw [evalA_eq (code := fun i : Fin 4 => i.val) idOK45 cnPID (cnGc hc) (letA_eq hc),
    evalA_eq (code := fun i : Fin 4 => i.val) idOK45 cnPID (cnGc hc) (letA_eq hc),
    Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]

theorem code2_lt (i : Fin 5) : code2 i < 6 := by
  unfold code2
  split <;> omega

theorem p2Tab_eq : p2Tab () = Array.ofFn (n := 960) fun k => (U (P2K k.val), U (P2KI k.val)) := by
  unfold p2Tab
  refine congrArg (Array.ofFn (n := 960)) (funext fun k => ?_)
  have h := List.all_eq_true.1 ckP2W k (List.mem_finRange k)
  obtain ⟨h1, h2⟩ := bAnd_iff2 h
  unfold p2Pair
  rw [evalA_eq (code := code2) idOK45 cnPID (cnGc code2_lt) (letA_eq code2_lt),
    evalA_eq (code := code2) idOK45 cnPID (cnGc code2_lt) (letA_eq code2_lt),
    Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]

theorem yPow_eq {j : Nat} (hj : j < 3) : yPow j = (U (YP j), U (YPI j)) := by
  have g4 := gen_eq (k := 4) (by norm_num)
  have c4 := cnG (k := 4) (by norm_num)
  interval_cases j
  · rw [yPow, if_pos rfl, idA_eq]
    rfl
  · rw [yPow, if_neg (by omega), if_pos rfl, g4.1, g4.2]
    rfl
  · rw [yPow, if_neg (by omega), if_neg (by omega), g4.1, g4.2, cmpA_unpack c4.1 c4.1,
      cmpA_unpack c4.2 c4.2]
    rfl

theorem bget_eq {i : Nat} (hi : i < 192) :
    (bTab ()).getD i (idA, idA) = (U (BK i), U (BKI i)) := by
  rw [bTab_eq, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hi)]
  simp

theorem p1Tab_eq : p1Tab () = Array.ofFn (n := 576) fun i => (U (P1E i.val), U (P1I i.val)) := by
  unfold p1Tab
  refine congrArg (Array.ofFn (n := 576)) (funext fun i => ?_)
  have hy := yPow_eq (j := i.val / 192) (by omega)
  have hb := bget_eq (i := i.val % 192) (by omega)
  have cy := cnY (j := i.val / 192) (by omega)
  have cb := cnB (k := i.val % 192) (by omega)
  rw [hy, hb]
  simp only []
  rw [cmpA_unpack cy.1 cb.1, cmpA_unpack cb.2 cy.2]
  rfl

theorem bh_mem {f : Nat} (hf : f < 384) : (U (BHE f), U (BHI f)) ∈ bhTab () := by
  unfold bhTab
  simp only []
  rw [Array.mem_append]
  unfold BHE BHI
  cases h : Nat.blt f 192
  · right
    have hf' : f - 192 < 192 := by have := le_of_blt_false h; omega
    rw [Array.mem_map]
    refine ⟨(U (BK (f - 192)), U (BKI (f - 192))), ?_, ?_⟩
    · rw [bTab_eq, Array.mem_ofFn]
      exact ⟨⟨f - 192, hf'⟩, rfl⟩
    · have cb := cnB hf'
      simp only []
      rw [fhat_eq, cmpA_unpack cb.1 cnFH, cmpA_unpack cnFH cb.2]
      rfl
  · left
    rw [bTab_eq, Array.mem_ofFn]
    exact ⟨⟨f, Nat.blt_eq.mp h⟩, rfl⟩

theorem cnTup {a b c d e : Nat} (ha : Cn a) (hb : Cn b) (hc : Cn c) (hd : Cn d) (he : Cn e)
    {a' b' c' d' e' : Nat} (ha' : Cn a') (hb' : Cn b') (hc' : Cn c') (hd' : Cn d') (he' : Cn e') :
    ∀ l, Cn (tup5 a b c d e l) ∧ Cn (tup5 a' b' c' d' e' l) :=
  fun l => ⟨cn_tup5 ha hb hc hd he l, cn_tup5 ha' hb' hc' hd' he' l⟩

theorem relB_eq {a b c d a' b' c' d' : Nat} (ha : Cn a) (hb : Cn b) (hc : Cn c) (hd : Cn d)
    (ha' : Cn a') (hb' : Cn b') (hc' : Cn c') (hd' : Cn d') (w : List (Fin 4 × Bool)) :
    relOK4 ![(U a, U a'), (U b, U b'), (U c, U c'), (U d, U d')] w =
      relK (tup5 a b c d PID) (tup5 a' b' c' d' PID) w := by
  unfold relOK4
  refine relOK_eq idOK45 cnPID (cnTup ha hb hc hd cnPID ha' hb' hc' hd' cnPID) (fun i => ?_) w
  fin_cases i <;> rfl

theorem rel5_eq {a b c d e a' b' c' d' e' : Nat} (ha : Cn a) (hb : Cn b) (hc : Cn c) (hd : Cn d)
    (he : Cn e) (ha' : Cn a') (hb' : Cn b') (hc' : Cn c') (hd' : Cn d') (he' : Cn e')
    (w : List (Fin 5 × Bool)) :
    relOK5 ![(U a, U a'), (U b, U b'), (U c, U c'), (U d, U d'), (U e, U e')] w =
      relK (tup5 a b c d e) (tup5 a' b' c' d' e') w := by
  unfold relOK5
  refine relOK_eq idOK45 cnPID (cnTup ha hb hc hd he ha' hb' hc' hd' he') (fun i => ?_) w
  fin_cases i <;> rfl

theorem relK_tup {k : Nat} {w : List (Fin k × Bool)} (S : List Nat)
    (hw : ∀ l ∈ w, l.1.val ∈ S) {E EI E' EI' : Nat → Nat}
    (h : ∀ j ∈ S, E j = E' j ∧ EI j = EI' j) : relK E EI w = relK E' EI' w := by
  unfold relK
  rw [relK_congr w fun l hl => h _ (hw l hl)]

theorem mem_filter_range {n : Nat} {p : Nat → Bool} {i : Nat} (hi : i < n) (h : p i = true) :
    i ∈ (List.range n).filter p :=
  List.mem_filter.2 ⟨List.mem_range.2 hi, h⟩

theorem un_spec {i : Nat} (hi : i < 192) : bitK (UN 0) i = u0K i ∧ bitK (UN 1) i = u1K i ∧
    bitK (UN 2) i = u2K i ∧ bitK (UN 3) i = u3K i := by
  have h := allK_spec ckU i hi
  obtain ⟨h0, h⟩ := bAnd_iff2 h
  obtain ⟨h1, h⟩ := bAnd_iff2 h
  obtain ⟨h2, h3⟩ := bAnd_iff2 h
  exact ⟨bitK_beqB h0, bitK_beqB h1, bitK_beqB h2, bitK_beqB h3⟩

theorem pair_spec {L1 L2 : List Nat} {T : Nat → Nat} {p : Nat → Nat → Bool}
    (h : L1.all (fun a => L2.all fun b => beqB (bitK (T a) b) (p a b)) = true)
    {a b : Nat} (ha : a ∈ L1) (hb : b ∈ L2) : bitK (T a) b = p a b :=
  bitK_beqB (List.all_eq_true.1 (List.all_eq_true.1 h a ha) b hb)

theorem bimp {x y : Bool} : ((!x) || y) = true ↔ (x = true → y = true) := by
  cases x <;> simp

theorem band_iff {x y : Bool} : (x && y) = true ↔ x = true ∧ y = true := by
  cases x <;> simp

theorem conjA_eq {f : Nat} (hf : f < 384) {k : Nat} (hk : k < 6) :
    conjA (U (BHE f), U (BHI f)) (genA k) = U (cj f (GK k)) := by
  obtain ⟨c1, c2⟩ := cnBH hf
  have cg := (cnG hk).1
  unfold conjA
  rw [(gen_eq hk).1, cmpA_unpack c1 cg, cmpA_unpack (cn_pc c1 cg) c2]
  rfl

theorem cn_cj {f : Nat} (hf : f < 384) {k : Nat} (hk : k < 6) : Cn (cj f (GK k)) := by
  obtain ⟨c1, c2⟩ := cnBH hf
  exact cn_pc (cn_pc c1 (cnG hk).1) c2

theorem conj_eq {f a b c d u v : Nat} (hf : f < 384) (ha : a < 192) (hb : b < 192)
    (hc : c < 192) (hd : d < 192) (hu : u < 576) (hv : v < 960) :
    conjMatch (U (BHE f), U (BHI f)) (U (BK a)) (U (BK b)) (U (BK c)) (U (BK d)) (U (P1E u))
      (U (P2K v)) = conjK f a b c d u v := by
  unfold conjMatch
  rw [conjA_eq hf (by norm_num : 0 < 6), conjA_eq hf (by norm_num : 1 < 6),
    conjA_eq hf (by norm_num : 2 < 6), conjA_eq hf (by norm_num : 3 < 6),
    conjA_eq hf (by norm_num : 4 < 6), conjA_eq hf (by norm_num : 5 < 6),
    beq_unpack (cn_cj hf (by norm_num)) (cnB ha).1, beq_unpack (cn_cj hf (by norm_num)) (cnB hb).1,
    beq_unpack (cn_cj hf (by norm_num)) (cnB hc).1, beq_unpack (cn_cj hf (by norm_num)) (cnB hd).1,
    beq_unpack (cn_cj hf (by norm_num)) (cnP1 hu).1, beq_unpack (cn_cj hf (by norm_num)) (cnP2 hv).1]
  unfold conjK
  cases Nat.beq (cj f (GK 0)) (BK a) <;> cases Nat.beq (cj f (GK 1)) (BK b) <;>
    cases Nat.beq (cj f (GK 2)) (BK c) <;> cases Nat.beq (cj f (GK 3)) (BK d) <;>
    cases Nat.beq (cj f (GK 4)) (P1E u) <;> rfl

theorem rigidCheck_true : rigidCheck () = true := by
  have hone : ((idA, idA) : Array Nat × Array Nat) = (U PID, U PID) := by rw [idA_eq]
  unfold rigidCheck
  simp only []
  rw [bTab_eq, p1Tab_eq, p2Tab_eq, hone]
  simp only [Array.all_eq_true', Array.any_eq_true', bimp, Array.mem_ofFn]
  rintro _ ⟨⟨a, ha⟩, rfl⟩ h0 _ ⟨⟨b, hb⟩, rfl⟩ h1 _ ⟨⟨c, hc⟩, rfl⟩ h2 _ ⟨⟨d, hd⟩, rfl⟩ h3
    _ ⟨⟨u, hu⟩, rfl⟩ h4 _ ⟨⟨v, hv⟩, rfl⟩ h5
  simp only [] at h0 h1 h2 h3 h4 h5 ⊢
  obtain ⟨ca, ca'⟩ := cnB ha
  obtain ⟨cb, cb'⟩ := cnB hb
  obtain ⟨cc, cc'⟩ := cnB hc
  obtain ⟨cd, cd'⟩ := cnB hd
  obtain ⟨cu, cu'⟩ := cnP1 hu
  obtain ⟨cv, cv'⟩ := cnP2 hv
  have P := cnPID
  simp only [lvlOK, List.all_cons, List.all_nil, Bool.and_true, band_iff] at h0 h1 h2 h3
  rw [relB_eq ca P P P ca' P P P] at h0
  rw [relB_eq ca cb P P ca' cb' P P, relB_eq ca cb P P ca' cb' P P] at h1
  rw [relB_eq ca cb cc P ca' cb' cc' P, relB_eq ca cb cc P ca' cb' cc' P,
    relB_eq ca cb cc P ca' cb' cc' P] at h2
  rw [relB_eq ca cb cc cd ca' cb' cc' cd', relB_eq ca cb cc cd ca' cb' cc' cd',
    relB_eq ca cb cc cd ca' cb' cc' cd', relB_eq ca cb cc cd ca' cb' cc' cd',
    relB_eq ca cb cc cd ca' cb' cc' cd'] at h3
  simp only [List.all_eq_true] at h4 h5
  have h4' : ∀ k < 4, relOK5 ![(U (BK a), U (BKI a)), (U (BK b), U (BKI b)), (U (BK c), U (BKI c)),
      (U (BK d), U (BKI d)), (U (P1E u), U (P1I u))] (rels1Extra.getD k []) = true := by
    intro k hk
    have hk' : k < rels1Extra.length := by simp [rels1Extra]; omega
    rw [List.getD_eq_getElem _ _ hk']
    exact h4 _ (List.getElem_mem hk')
  have h5' : ∀ k < 5, relOK5 ![(U (BK a), U (BKI a)), (U (BK b), U (BKI b)), (U (BK c), U (BKI c)),
      (U (BK d), U (BKI d)), (U (P2K v), U (P2KI v))] (rels2Extra.getD k []) = true := by
    intro k hk
    have hk' : k < rels2Extra.length := by simp [rels2Extra]; omega
    rw [List.getD_eq_getElem _ _ hk']
    exact h5 _ (List.getElem_mem hk')
  have e4 := fun k hk => (rel5_eq ca cb cc cd cu ca' cb' cc' cd' cu' _).symm.trans (h4' k hk)
  have e5 := fun k hk => (rel5_eq ca cb cc cd cv ca' cb' cc' cd' cv' _).symm.trans (h5' k hk)
  have g0 : u0K a = true := by
    unfold u0K rB
    have hne := h0.2
    rw [idA_eq, bne, beq_unpack ca P] at hne
    rw [h0.1]
    cases hb : Nat.beq (BK a) PID
    · rfl
    · rw [hb] at hne
      exact absurd hne (by decide)
  have g1 : u1K b = true := (relK_tup [1] (by decide) fun j hj => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    subst hj; exact ⟨rfl, rfl⟩).trans h1.1
  have g5 : p5K a b = true := h1.2
  have g2 : u2K c = true := (relK_tup [2] (by decide) fun j hj => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    subst hj; exact ⟨rfl, rfl⟩).trans h2.1
  have g6 : p6K a c = true := (relK_tup [0, 2] (by decide) fun j hj => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl <;> exact ⟨rfl, rfl⟩).trans h2.2.1
  have g9 : p9K b c = true := (relK_tup [1, 2] (by decide) fun j hj => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl <;> exact ⟨rfl, rfl⟩).trans h2.2.2
  have g3 : u3K d = true := (relK_tup [3] (by decide) fun j hj => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    subst hj; exact ⟨rfl, rfl⟩).trans h3.1
  have g4 : p4K c d = true := (relK_tup [2, 3] (by decide) fun j hj => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl <;> exact ⟨rfl, rfl⟩).trans h3.2.1
  have g7 : p7K a d = true := (relK_tup [0, 3] (by decide) fun j hj => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl <;> exact ⟨rfl, rfl⟩).trans h3.2.2.1
  have g8 : p8K b d = true := (relK_tup [1, 3] (by decide) fun j hj => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl <;> exact ⟨rfl, rfl⟩).trans h3.2.2.2.1
  have g10 : r10K a b c d = true := h3.2.2.2.2
  have gy : uyK u = true := (relK_tup [4] (by decide) fun j hj => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    subst hj; exact ⟨rfl, rfl⟩).trans (e4 0 (by norm_num))
  have gq1 : q1K d u = true := (relK_tup [3, 4] (by decide) fun j hj => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl <;> exact ⟨rfl, rfl⟩).trans (e4 1 (by norm_num))
  have gq2 : q2K b u = true := (relK_tup [1, 4] (by decide) fun j hj => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl <;> exact ⟨rfl, rfl⟩).trans (e4 2 (by norm_num))
  have gy3 : ry3K a b c u = true := (relK_tup [0, 1, 2, 4] (by decide) fun j hj => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩).trans (e4 3 (by norm_num))
  have gs : usK v = true := (relK_tup [4] (by decide) fun j hj => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    subst hj; exact ⟨rfl, rfl⟩).trans (e5 0 (by norm_num))
  have gs1 : s1K d v = true := (relK_tup [3, 4] (by decide) fun j hj => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl <;> exact ⟨rfl, rfl⟩).trans (e5 1 (by norm_num))
  have gs2 : s2K c v = true := (relK_tup [2, 4] (by decide) fun j hj => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl <;> exact ⟨rfl, rfl⟩).trans (e5 2 (by norm_num))
  have gs3 : rs3K c d v = true := (relK_tup [2, 3, 4] (by decide) fun j hj => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩).trans (e5 3 (by norm_num))
  have gs4 : rs4K a b v = true := (relK_tup [0, 1, 4] (by decide) fun j hj => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩).trans (e5 4 (by norm_num))
  have mA : a ∈ AL := mem_filter_range ha ((un_spec ha).1.trans g0)
  have mT : b ∈ T2L := mem_filter_range hb ((un_spec hb).2.1.trans g1)
  have mE : c ∈ E2L := mem_filter_range hc ((un_spec hc).2.2.1.trans g2)
  have mD : d ∈ D3L := mem_filter_range hd ((un_spec hd).2.2.2.trans g3)
  have mU : u ∈ U3L := mem_filter_range hu ((bitK_beqB (allK_spec ckUY u hu)).trans gy)
  have mV : v ∈ V2L := mem_filter_range hv ((bitK_beqB (allK_spec ckUS v hv)).trans gs)
  have s := List.all_eq_true.1 rigidK a mA
  have s := List.all_eq_true.1 s b mT
  have s := bIf_true s ((pair_spec ckP5 mA mT).trans g5)
  have s := List.all_eq_true.1 s c mE
  have s := bIf_true s (by
    rw [(pair_spec ckP6 mA mE).trans g6, (pair_spec ckP9 mT mE).trans g9])
  have s := List.all_eq_true.1 s d mD
  have s := bIf_true s (by
    rw [(pair_spec ckP4 mE mD).trans g4, (pair_spec ckP7 mA mD).trans g7,
      (pair_spec ckP8 mT mD).trans g8, g10])
  have s := List.all_eq_true.1 s u mU
  have s := bIf_true s (by
    rw [(pair_spec ckQ1 mD mU).trans gq1, (pair_spec ckQ2 mT mU).trans gq2, gy3])
  have s := List.all_eq_true.1 s v mV
  have s := bIf_true s (by
    rw [(pair_spec ckR1 mD mV).trans gs1, (pair_spec ckR2 mE mV).trans gs2, gs3, gs4])
  obtain ⟨f, hf, hfc⟩ := anyK_spec s
  have hfc := (bAnd_iff2 (bAnd_iff2 hfc).2).2
  refine ⟨(U (BHE f), U (BHI f)), bh_mem hf, ?_⟩
  exact (conj_eq hf ha hb hc hd hu hv).trans hfc

theorem distinct_of {n : Nat} {K : Nat → Nat} (hc : ∀ k < n, Cn (K k))
    (h : nodupK ((List.range n).map K) = true) :
    (List.ofFn (fun k : Fin n => U (K k.val))).Nodup := by
  rw [List.nodup_ofFn]
  intro i j hij
  have hinj := List.inj_on_of_nodup_map (nodupK_sound h)
  have e := beq_unpack (hc i i.2) (hc j j.2)
  simp only at hij
  rw [hij, beq_self_eq_true] at e
  exact Fin.ext (hinj (List.mem_range.2 i.2) (List.mem_range.2 j.2) (Nat.eq_of_beq_eq_true e.symm))

theorem dist_parts : nodupK ((List.range 192).map BK) = true ∧
    nodupK ((List.range 576).map P1E) = true ∧ nodupK ((List.range 960).map P2K) = true := by
  have h := ckDistinct
  simp only [CFSG.KS.bAnd_iff] at h
  exact h

theorem eB : (bTab ()).toList.map Prod.fst = List.ofFn (fun k : Fin 192 => U (BK k.val)) := by
  rw [bTab_eq, Array.toList_ofFn, List.map_ofFn]
  exact congrArg List.ofFn (funext fun k => rfl)

theorem e1 : (p1Tab ()).toList.map Prod.fst = List.ofFn (fun k : Fin 576 => U (P1E k.val)) := by
  rw [p1Tab_eq, Array.toList_ofFn, List.map_ofFn]
  exact congrArg List.ofFn (funext fun k => rfl)

theorem e2 : (p2Tab ()).toList.map Prod.fst = List.ofFn (fun k : Fin 960 => U (P2K k.val)) := by
  rw [p2Tab_eq, Array.toList_ofFn, List.map_ofFn]
  exact congrArg List.ofFn (funext fun k => rfl)

theorem nodupB : ((bTab ()).toList.map Prod.fst).Nodup := by
  rw [eB]
  exact distinct_of (fun k hk => (cnB hk).1) dist_parts.1

theorem nodup1 : ((p1Tab ()).toList.map Prod.fst).Nodup := by
  rw [e1]
  exact distinct_of (fun k hk => (cnP1 hk).1) dist_parts.2.1

theorem nodup2 : ((p2Tab ()).toList.map Prod.fst).Nodup := by
  rw [e2]
  exact distinct_of (fun k hk => (cnP2 hk).1) dist_parts.2.2

theorem distinctTab_true {T : Array (Array Nat × Array Nat)}
    (h : (T.toList.map Prod.fst).Nodup) : distinctTab T = true := by
  unfold distinctTab
  exact decide_eq_true h

theorem bDistinct_true : bDistinct () = true := distinctTab_true nodupB

theorem p1Distinct_true : p1Distinct () = true := distinctTab_true nodup1

theorem p2Distinct_true : p2Distinct () = true := distinctTab_true nodup2

end CertificateChecks.KernelAS62

end
