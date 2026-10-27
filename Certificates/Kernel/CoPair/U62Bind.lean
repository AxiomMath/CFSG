module

public import CFSG.Fischer.UnitaryPerm
public import Certificates.Kernel.Misc.Unitary
public import Certificates.Certificate1003
public import Certificates.Data.CFSGNative.F4.T46Simple
public import CFSG.Certificates.Kernel.CoPairSound
public import CFSG.Certificates.Kernel.Common.HexNat
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCoPair

open CFSG.KC.CoPair CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Fi22.Native CFSG.KD.Misc.Unitary

set_option maxRecDepth 100000
set_option Elab.async false

@[expose] def ULText : String := include_str "u62ul.hex"

@[expose] def GText : String := include_str "u62g.hex"

@[expose] noncomputable def ULP : Nat := by hex_nat ULText 2079 2292961881365739244

@[expose] noncomputable def GTab : Nat := by hex_nat GText 19057 8187858344558264223

@[expose] noncomputable def f12 (X i : Nat) : Nat := Nat.land (Nat.shiftRight X (Nat.mul i 12)) 4095

@[expose] noncomputable def gl (k p : Nat) : Nat :=
  Nat.land (Nat.shiftRight GTab (Nat.mul (Nat.add (Nat.mul 693 k) p) 10)) 1023

@[expose] noncomputable def genOK (v k : Nat) : Bool :=
  allN 693 fun p => letB (gl k p) fun q =>
    andB (Nat.blt q 693) (Nat.beq (f12 ULP q) (normC (tvC v (f12 ULP p))))

@[expose] noncomputable def walkOK (L : List Nat) (P : Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih i => andB (Nat.beq x (f12 P i)) (letB (Nat.succ i) ih)) L

theorem walkOK_spec (P : Nat) : ∀ (L : List Nat) (i : Nat), walkOK L P i = true →
    ∀ k < L.length, L.getD k 0 = f12 P (i + k)
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | x :: L, i, h, k, hk => by
    change andB (Nat.beq x (f12 P i)) (letB (Nat.succ i) (walkOK L P)) = true at h
    rw [andB_eq, letB_eq, Bool.and_eq_true, Nat.beq_eq] at h
    cases k with
    | zero => simpa using h.1
    | succ k =>
      rw [List.getD_cons_succ, walkOK_spec P L (i + 1) h.2 k (by simpa using hk)]
      congr 1
      omega

theorem kUL : walkOK UL ULP 0 = true := by quickRfl

theorem kLen : UL.length = 693 := by decide +kernel

theorem kSorted : allN 692 (fun k => Nat.blt (f12 ULP k) (f12 ULP (Nat.succ k))) = true := by
  quickRfl

theorem ul_get {k : Nat} (hk : k < 693) : UL.getD k 0 = f12 ULP k := by
  rw [walkOK_spec ULP UL 0 kUL k (by rw [kLen]; exact hk), Nat.zero_add]

theorem kNodup : UL.Nodup := by
  have hmono : ∀ i j, i < j → j < 693 → f12 ULP i < f12 ULP j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      have hstep := Nat.blt_eq.mp ((allN_iff _ _).1 kSorted j (by omega))
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
      · exact Nat.lt_trans (ih h' (by omega)) hstep
      · exact hstep
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [kLen] at hi hj
  rw [← List.getD_eq_getElem UL 0, ← List.getD_eq_getElem UL 0, ul_get hi, ul_get hj]
  exact Nat.ne_of_lt (hmono i j hij hj)

theorem kGens : tvGens () = #[5, 9, 13, 17, 20, 33, 36, 49, 52, 65, 68, 80, 129, 132, 144, 193, 196,
    208, 257, 260, 272, 320, 513, 516, 528, 576, 769, 772, 784, 832, 1025, 1028, 1040, 1088, 1280,
    2049, 2052, 2064, 2112, 2304, 3073, 3076, 3088, 3136, 3328, 85] := by
  rw [gE]
  decide +kernel

theorem kG0 : genOK 52 0 = true := by quickRfl
theorem kG1 : genOK 80 1 = true := by quickRfl
theorem kG2 : genOK 193 2 = true := by quickRfl
theorem kG3 : genOK 272 3 = true := by quickRfl
theorem kG4 : genOK 513 4 = true := by quickRfl
theorem kG5 : genOK 832 5 = true := by quickRfl
theorem kG6 : genOK 1040 6 = true := by quickRfl
theorem kG7 : genOK 2049 7 = true := by quickRfl
theorem kG8 : genOK 2112 8 = true := by quickRfl
theorem kG9 : genOK 3073 9 = true := by quickRfl
theorem kG10 : genOK 85 10 = true := by quickRfl

theorem f12_lt (X i : Nat) : f12 X i < 4096 := Nat.and_lt_two_pow _ (by decide : 4095 < 2 ^ 12)

theorem uPts_get {p : Nat} (hp : p < 693) : (uPts ())[p]! = f12 ULP p := by
  rw [hU, getE]
  exact ul_get hp

theorem ap_tvTable_gl {v k : Nat} (h : genOK v k = true) :
    ∀ p < 693, ap (tvTable v) p = gl k p ∧ gl k p < 693 := by
  intro p hp
  have hk := (allN_iff _ _).1 h p hp
  simp only [letB_eq, andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hk
  obtain ⟨hq, he⟩ := hk
  refine ⟨?_, hq⟩
  rw [CFSG.Fischer.ap_tvTable v hp (m := f12 ULP (gl k p)) (by rw [uPts_get hp, he]) (f12_lt _ _),
    hU, List.toList_toArray]
  have hget : UL[gl k p]'(by rw [kLen]; exact hq) = f12 ULP (gl k p) := by
    rw [← List.getD_eq_getElem UL 0]
    exact ul_get hq
  rw [← hget, kNodup.idxOf_getElem]

theorem ap_wordT_of {n : Nat} (hn : n < 2 ^ 32) {gens : ℤ → Table} {f : ℤ → Nat → Nat} :
    ∀ w : List ℤ, (∀ l ∈ w, ∀ j < n, ap (gens l) j = f l j ∧ f l j < n) →
      ∀ i < n, ap (wordT n gens w) i = w.foldr f i ∧ w.foldr f i < n
  | [], _, i, hi => by
    refine ⟨?_, hi⟩
    unfold wordT idT
    rw [List.foldr_nil, ap_ofFn _ hi, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (hi.trans hn)]
    rfl
  | l :: w, h, i, hi => by
    obtain ⟨ih1, ih2⟩ := ap_wordT_of hn w (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')) i hi
    obtain ⟨hl1, hl2⟩ := h l List.mem_cons_self _ ih2
    have hsz := wordT_size n gens w
    have e : wordT n gens (l :: w) = (wordT n gens w).map (fun t => (gens l)[t.toNat]!) := rfl
    refine ⟨?_, by rw [List.foldr_cons]; exact hl2⟩
    rw [e, List.foldr_cons, ← hl1, ← ih1]
    unfold ap
    rw [getElem!_pos (Array.map _ (wordT n gens w)) i (by simp [hsz, hi]),
      Array.getElem_map, getElem!_pos (wordT n gens w) i (by simp [hsz, hi])]

theorem ap_powT_of {n : Nat} (hn : n < 2 ^ 32) {P : Table} {g : Nat → Nat}
    (h : ∀ j < n, ap P j = g j ∧ g j < n) :
    ∀ e, ∀ i < n, ap (powT n e P) i = g^[e] i ∧ g^[e] i < n
  | 0, i, hi => by
    refine ⟨?_, hi⟩
    unfold powT idT
    rw [ap_ofFn _ hi, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (hi.trans hn)]
    rfl
  | e + 1, i, hi => by
    obtain ⟨ih1, ih2⟩ := ap_powT_of hn h e i hi
    obtain ⟨h1, h2⟩ := h _ ih2
    refine ⟨?_, by rw [Function.iterate_succ_apply']; exact h2⟩
    unfold powT compT
    rw [ap_ofFn _ hi, Function.iterate_succ_apply', ← h1, ← ih1]
    rfl

@[expose] def letIdx (z : ℤ) : Nat := [9, 12, 16, 21, 23, 30, 33, 36, 39, 41, 46].idxOf z.natAbs

theorem ap_t46Gen : ∀ z ∈ ([30, 33, 16, 12, 9, 39, 41, 46, 21, 23, 36] : List ℤ), ∀ j < 693,
    ap (t46Gen z) j = gl (letIdx z) j ∧ gl (letIdx z) j < 693 := by
  intro z hz j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold t46Gen
  rw [kGens]
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ap_tvTable_gl kG5 j hj
  · exact ap_tvTable_gl kG6 j hj
  · exact ap_tvTable_gl kG2 j hj
  · exact ap_tvTable_gl kG1 j hj
  · exact ap_tvTable_gl kG0 j hj
  · exact ap_tvTable_gl kG8 j hj
  · exact ap_tvTable_gl kG9 j hj
  · exact ap_tvTable_gl kG10 j hj
  · exact ap_tvTable_gl kG3 j hj
  · exact ap_tvTable_gl kG4 j hj
  · exact ap_tvTable_gl kG7 j hj

@[expose] noncomputable def xw (i : Nat) : Nat := gl 5 (gl 6 (gl 2 (gl 1 (gl 0 (gl 8 (gl 8 i))))))

@[expose] noncomputable def yw (i : Nat) : Nat := gl 9 (gl 10 (gl 3 (gl 4 (gl 7 i))))

theorem ap_t46XT : ∀ i < 693, ap (t46XT ()) i = xw (xw (xw i)) := by
  have hw := ap_wordT_of (n := 693) (by norm_num) (gens := t46Gen) (f := fun z j => gl (letIdx z) j)
    [30, 33, 16, 12, 9, 39, 39] (fun l hl j hj => ap_t46Gen l (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
      rcases hl with h | h | h | h | h | h | h <;> simp [h]) j hj)
  intro i hi
  rw [show t46XT () = powT 693 3 (wordT 693 t46Gen [30, 33, 16, 12, 9, 39, 39]) from rfl,
    (ap_powT_of (by norm_num) hw 3 i hi).1]
  rfl

theorem ap_t46YT : ∀ i < 693, ap (t46YT ()) i = yw (yw i) := by
  have hw := ap_wordT_of (n := 693) (by norm_num) (gens := t46Gen) (f := fun z j => gl (letIdx z) j)
    [41, 46, 21, 23, 36] (fun l hl j hj => ap_t46Gen l (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
      rcases hl with h | h | h | h | h <;> simp [h]) j hj)
  intro i hi
  rw [show t46YT () = powT 693 2 (wordT 693 t46Gen [41, 46, 21, 23, 36]) from rfl,
    (ap_powT_of (by norm_num) hw 2 i hi).1]
  rfl

end CertificateChecks.KernelCoPair

end
