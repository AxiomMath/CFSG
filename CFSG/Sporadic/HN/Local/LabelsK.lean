module

public import CFSG.Sporadic.HN.Local.Partitions
public import CFSG.Certificates.Kernel.HNLocalSound

public section

namespace CFSG.Sporadic.HN.Local.LabelsK

open Equiv Finset

@[expose] noncomputable def bitN (m i : ℕ) : ℕ := Nat.land (Nat.shiftRight m i) 1

@[expose] noncomputable def xn (x y : ℕ) : ℕ := Nat.xor (Nat.xor x y) 1

@[expose] noncomputable def bForce (y : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def labOK (a b : ℕ) (q : ℕ → ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j ih =>
    bAnd(Nat.beq (bitN a j) (xn (bitN b (q j)) (bitN b (q 0))), ih)) 12

@[expose] noncomputable def popc (m n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun j ih => Nat.add (bitN m j) ih) n

@[expose] noncomputable def canonB (m : ℕ) : Bool :=
  bAnd(Nat.beq (bitN m 0) 1, Nat.beq (popc m 12) 6)

@[expose] noncomputable def ltW (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(Nat.blt x 4096, ih)) l

@[expose] noncomputable def ndW (l : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true) (fun x _ ih s =>
    bAnd(Nat.beq (Nat.land s (Nat.shiftLeft 1 x)) 0,
      bForce (Nat.lor s (Nat.shiftLeft 1 x)) ih)) l

theorem bAnd_tt {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem bForce_eq (y : ℕ) (k : ℕ → Bool) : bForce y k = k y := by
  cases y <;> rfl

theorem bitN_eq (m i : ℕ) : bitN m i = m / 2 ^ i % 2 := by
  unfold bitN
  rw [← Nat.shiftRight_eq_div_pow]
  exact Nat.and_one_is_mod _

theorem bitN_le (m i : ℕ) : bitN m i = 0 ∨ bitN m i = 1 := by
  rw [bitN_eq]; omega

theorem testBit_iff (m i : ℕ) : m.testBit i = true ↔ bitN m i = 1 := by
  rw [bitN_eq, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]

theorem ite_testBit (m i : ℕ) : (if m.testBit i = true then 1 else 0) = bitN m i := by
  rcases bitN_le m i with h | h
  · have : m.testBit i ≠ true := fun e => by rw [(testBit_iff m i).1 e] at h; exact absurd h (by decide)
    rw [if_neg this, h]
  · rw [if_pos ((testBit_iff m i).2 h), h]

theorem rec_all {n : ℕ} {f : ℕ → Bool}
    (h : Nat.rec (motive := fun _ => Bool) true (fun j ih => bAnd(f j, ih)) n = true) :
    ∀ j < n, f j = true := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    obtain ⟨h1, h2⟩ := bAnd_tt h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact ih h2 j hj
    · exact h1

theorem lab_sound {a b : ℕ} {p : Perm (Fin 12)} {q : ℕ → ℕ}
    (hq : ∀ j : Fin 12, (p.symm j).val = q j.val) (h : labOK a b q = true) :
    (Finset.univ.filter fun i : Fin 12 => a.testBit i.val) =
      canon ((Finset.univ.filter fun i : Fin 12 => b.testBit i.val).map p.toEmbedding) := by
  have hj := rec_all (n := 12)
    (f := fun j => Nat.beq (bitN a j) (xn (bitN b (q j)) (bitN b (q 0)))) h
  have key : ∀ j : Fin 12, a.testBit j.val = true ↔
      (b.testBit (p.symm j).val = true ↔ b.testBit (p.symm 0).val = true) := by
    intro j
    have e := Nat.eq_of_beq_eq_true (hj j.val j.2)
    have hq0 : (p.symm 0).val = q 0 := hq 0
    rw [hq, hq0, testBit_iff, testBit_iff, testBit_iff, e]
    unfold xn
    rcases bitN_le b (q j.val) with h1 | h1 <;> rcases bitN_le b (q 0) with h2 | h2 <;>
      rw [h1, h2] <;> decide
  have hm : ∀ i : Fin 12, i ∈ (Finset.univ.filter fun i : Fin 12 => b.testBit i.val).map
      p.toEmbedding ↔ b.testBit (p.symm i).val = true := by
    intro i
    rw [Finset.mem_map_equiv, Finset.mem_filter]
    simp
  ext j
  have ha : j ∈ (Finset.univ.filter fun i : Fin 12 => a.testBit i.val) ↔ a.testBit j.val = true := by
    simp
  unfold canon
  rw [ha]
  split_ifs with h0
  · rw [hm, key j]
    rw [hm] at h0
    tauto
  · rw [Finset.mem_compl, hm, key j]
    rw [hm] at h0
    tauto

theorem popc_eq (m n : ℕ) : popc m n = ∑ j ∈ Finset.range n, bitN m j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    change Nat.add (bitN m n) (popc m n) = _
    rw [Nat.add_eq, Nat.add_comm]

theorem canonB_sound {m : ℕ} (h : canonB m = true) :
    IsCanon (Finset.univ.filter fun i : Fin 12 => m.testBit i.val) := by
  obtain ⟨h0, h6⟩ := bAnd_tt h
  refine ⟨?_, ?_⟩
  · rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun j => if m.testBit j = true then 1 else 0)]
    simp only [ite_testBit]
    rw [← popc_eq]
    exact Nat.eq_of_beq_eq_true h6
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (testBit_iff m 0).2 (Nat.eq_of_beq_eq_true h0)⟩

theorem ltW_sound {l : List ℕ} (h : ltW l = true) : ∀ m ∈ l, m < 4096 := by
  induction l with
  | nil => intro m hm; simp at hm
  | cons x l ih =>
    intro m hm
    obtain ⟨h1, h2⟩ := bAnd_tt h
    rcases List.mem_cons.1 hm with rfl | hm
    · rw [Nat.blt_eq] at h1
      exact h1
    · exact ih h2 m hm

theorem land_shift_eq_zero {s x : ℕ} (h : Nat.land s (Nat.shiftLeft 1 x) = 0) :
    s.testBit x = false := by
  have e : s &&& 2 ^ x = 0 := by rw [← Nat.one_shiftLeft]; exact h
  have := congrArg (fun t => t.testBit x) e
  simp only [Nat.testBit_and, Nat.testBit_two_pow_self, Bool.and_true, Nat.zero_testBit] at this
  exact this

theorem testBit_lor_shift (s x y : ℕ) :
    (Nat.lor s (Nat.shiftLeft 1 x)).testBit y = (s.testBit y || decide (x = y)) := by
  have e : Nat.lor s (Nat.shiftLeft 1 x) = s ||| 2 ^ x := by rw [← Nat.one_shiftLeft]; rfl
  rw [e, Nat.testBit_or, Nat.testBit_two_pow]

theorem ndW_sound {l : List ℕ} : ∀ s, ndW l s = true → l.Nodup ∧ ∀ y ∈ l, s.testBit y = false := by
  induction l with
  | nil => intro s _; exact ⟨List.nodup_nil, fun y hy => by simp at hy⟩
  | cons x l ih =>
    intro s h
    obtain ⟨h1, h2⟩ := bAnd_tt h
    have h2' : ndW l (Nat.lor s (Nat.shiftLeft 1 x)) = true := by
      rw [bForce_eq] at h2
      exact h2
    obtain ⟨hnd, hy⟩ := ih _ h2'
    have hx := land_shift_eq_zero (Nat.eq_of_beq_eq_true h1)
    refine ⟨List.nodup_cons.2 ⟨fun hm => ?_, hnd⟩, fun y hm => ?_⟩
    · have := hy x hm
      rw [testBit_lor_shift] at this
      simp at this
    · rcases List.mem_cons.1 hm with rfl | hm
      · exact hx
      · have := hy y hm
        rw [testBit_lor_shift] at this
        simp only [Bool.or_eq_false_iff] at this
        exact this.1

@[expose] noncomputable def ltB (b : ℕ) (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(Nat.blt x b, ih)) l

@[expose] noncomputable def packW (w : ℕ) (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun x _ ih => Nat.add x (Nat.shiftLeft ih w)) l

@[expose] noncomputable def rdW (w M T k : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul w k)) M

theorem ltB_sound {b : ℕ} {l : List ℕ} (h : ltB b l = true) : ∀ x ∈ l, x < b := by
  induction l with
  | nil => intro x hx; simp at hx
  | cons y l ih =>
    intro x hx
    obtain ⟨h1, h2⟩ := bAnd_tt h
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [Nat.blt_eq] at h1
      exact h1
    · exact ih h2 x hx

theorem packW_cons (w x : ℕ) (l : List ℕ) : packW w (x :: l) = x + 2 ^ w * packW w l := by
  have e1 : packW w (x :: l) = Nat.add x (Nat.shiftLeft (packW w l) w) := rfl
  have e2 : Nat.shiftLeft (packW w l) w = packW w l * 2 ^ w := Nat.shiftLeft_eq _ _
  rw [e1, e2, Nat.add_eq, Nat.mul_comm]

theorem rdW_eq (w T k : ℕ) : rdW w (2 ^ w - 1) T k = T / 2 ^ (w * k) % 2 ^ w := by
  have e : rdW w (2 ^ w - 1) T k = (T >>> (w * k)) &&& (2 ^ w - 1) := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem div_step (w x P k : ℕ) (hx : x < 2 ^ w) :
    (x + 2 ^ w * P) / 2 ^ (w * (k + 1)) = P / 2 ^ (w * k) := by
  rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (w * k)) (2 ^ w), ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt hx, Nat.zero_add]

theorem rdW_packW (w : ℕ) {l : List ℕ} (hl : ∀ x ∈ l, x < 2 ^ w) :
    ∀ k < l.length, rdW w (2 ^ w - 1) (packW w l) k = l.getD k 0 := by
  induction l with
  | nil =>
    intro k hk
    exact absurd hk (Nat.not_lt_zero k)
  | cons x l ih =>
    intro k hk
    have hx : x < 2 ^ w := hl x (List.mem_cons_self ..)
    rw [rdW_eq, packW_cons]
    rcases k with _ | k
    · rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one, List.getD_cons_zero, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hx]
    · have hk' : k < l.length := Nat.lt_of_succ_lt_succ hk
      rw [List.getD_cons_succ, ← ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) k hk', rdW_eq,
        div_step w x _ k hx]

theorem e4095 : (4095 : ℕ) = 2 ^ 12 - 1 := by norm_num
theorem e4096 : (4096 : ℕ) = 2 ^ 12 := by norm_num
theorem e511 : (511 : ℕ) = 2 ^ 9 - 1 := by norm_num
theorem e512 : (512 : ℕ) = 2 ^ 9 := by norm_num

theorem getElem!_eq_getD {L : Array ℕ} {k : ℕ} (hk : k < L.size) : L[k]! = L.toList.getD k 0 := by
  rw [getElem!_pos L k hk, List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

@[expose] noncomputable def labAllB (L P : Array ℕ) (q : ℕ → ℕ) : Bool :=
  bAnd(ltB 4096 L.toList, bAnd(ltB 512 P.toList,
    bForce (packW 12 L.toList) (fun T => bForce (packW 9 P.toList) (fun U =>
      CFSG.KC.Loop.allBelow 462 8 (fun k =>
        labOK (rdW 12 4095 T (rdW 9 511 U k % 462)) (rdW 12 4095 T k) q)))))

theorem labAll_sound {L P : Array ℕ} {p : Perm (Fin 12)} {q : ℕ → ℕ}
    (hq : ∀ j : Fin 12, (p.symm j).val = q j.val) (hL : L.size = 462) (hP : P.size = 462)
    (h : labAllB L P q = true) (k : Fin 462) :
    (Finset.univ.filter fun i : Fin 12 => L[P[k.val]! % 462]!.testBit i.val) =
      canon ((Finset.univ.filter fun i : Fin 12 => L[k.val]!.testBit i.val).map p.toEmbedding) := by
  obtain ⟨h1, h2⟩ := bAnd_tt h
  obtain ⟨h2, h3⟩ := bAnd_tt h2
  rw [bForce_eq] at h3
  beta_reduce at h3
  rw [bForce_eq] at h3
  beta_reduce at h3
  have hc := CFSG.KS.HNLocal.allBelow_spec h3 k.val k.2 (by omega)
  have hLl : L.toList.length = 462 := by simpa using hL
  have hPl : P.toList.length = 462 := by simpa using hP
  have rL : ∀ i < 462, rdW 12 4095 (packW 12 L.toList) i = L[i]! := fun i hi => by
    rw [getElem!_eq_getD (by omega), e4095]
    exact rdW_packW 12 (fun x hx => by rw [← e4096]; exact ltB_sound h1 x hx) i (by omega)
  have rP : rdW 9 511 (packW 9 P.toList) k.val = P[k.val]! := by
    rw [getElem!_eq_getD (by omega), e511]
    exact rdW_packW 9 (fun x hx => by rw [← e512]; exact ltB_sound h2 x hx) k.val (by omega)
  rw [rP, rL (P[k.val]! % 462) (Nat.mod_lt _ (by norm_num)), rL k.val k.2] at hc
  exact lab_sound hq hc

@[expose] noncomputable def canonAllB (L : Array ℕ) : Bool :=
  bAnd(ltB 4096 L.toList, bForce (packW 12 L.toList) (fun T =>
    CFSG.KC.Loop.allBelow 462 8 (fun k => canonB (rdW 12 4095 T k))))

theorem canonAll_sound {L : Array ℕ} (hL : L.size = 462) (h : canonAllB L = true) (k : Fin 462) :
    IsCanon (Finset.univ.filter fun i : Fin 12 => L[k.val]!.testBit i.val) := by
  obtain ⟨h1, h2⟩ := bAnd_tt h
  rw [bForce_eq] at h2
  beta_reduce at h2
  have hc := CFSG.KS.HNLocal.allBelow_spec h2 k.val k.2 (by omega)
  have hLl : L.toList.length = 462 := by simpa using hL
  have rL : rdW 12 4095 (packW 12 L.toList) k.val = L[k.val]! := by
    rw [getElem!_eq_getD (by omega), e4095]
    exact rdW_packW 12 (fun x hx => by rw [← e4096]; exact ltB_sound h1 x hx) k.val (by omega)
  rw [rL] at hc
  exact canonB_sound hc

@[expose] def stepW (p₁ p₂ : Perm (Fin 12)) : List Bool → Fin 12 × Fin 12 → Fin 12 × Fin 12
  | [], q => q
  | b :: w, q =>
    let r := stepW p₁ p₂ w q
    if b then (p₂ r.1, p₂ r.2) else (p₁ r.1, p₁ r.2)

@[expose] def reachWords : List (List Bool) :=
  [[], [], [true, false, true, true, false, true, false],
    [false, true, false, true, true, false, true, true, false],
    [false, true, false, true, false, true, false, true, false, true, true],
    [true, false, true, false, true, false, true, false, true, false],
    [true, true, false, true, false, true],
    [false, true, false, true, true, false, true, false, true, false, true, true],
    [true, true, false, true, false, true, false, true, false, true, true, false, true, true, false],
    [true, false, true, true, false, true, true, false, true, true, false, true, false, true, false,
      true, true],
    [false, true, true, false, true, false, true, false, true, false, true, true, false, true, false,
      true, false, true, false, true, false],
    [true, true, false, true, false, true, true, false, true, false, true, false, true, false, true,
      false],
    [false, true, false, true, true, false], [],
    [true, true, false, true, false, true, false, true, false, true, false, true, false],
    [true, false, true, false, true, true],
    [true, false, true, true, false, true, true, false, true, true, false, true, false, true, false,
      true],
    [false, true, false, true, false, true, false, true, true],
    [true, true, false, true, true, false, true, false, true, false, true, false, true, true, false,
      true, true, false],
    [true, true, false],
    [true, false, true, false, true, true, false, true, false, true, true, false, true, false, true,
      false, true, true],
    [false, true, true, false, true, true, false],
    [false, true, true, false, true, false, true, false, true, true],
    [true, false, true, false, true, false, true, false, true, true, false, true, false, true, false,
      true, false, true, false],
    [true, true, false, true, false, true, false, true],
    [true, false, true, false, true, false, true, false, true, false, true, false, true, false],
    [],
    [true, true, false, true, false, true, false, true, true, false, true, false, true, false, true,
      false, true, false],
    [true, false, true, false],
    [true, false, true, false, true, true, false, true, false, true, false, true, false, true, true,
      false, true, true, false],
    [false, true, false, true, false, true, false],
    [false, true, true, false, true, true, false, true, false, true, false, true],
    [true, false, true, true, false, true, true, false, true, false, true, false, true, true],
    [true, false, true, true, false, true, false, true, true, false],
    [true, true, false, true, true, false, true, false, true, true, false, true, false, true, false,
      true, true],
    [true, true, false, true, true], [false, true, false, true, false],
    [true, true, false, true, true, false, true, false, true, false, true],
    [false, true, true, false, true, false, true, false, true, true, false, true, false, true, false,
      true, false, true, false],
    [], [false, true, true, false, true, false, true, false, true],
    [false, true, true, false, true, true],
    [false, true, false, true, true, false, true, true, false, true, false, true, false, true, true],
    [false, true, false, true, false, true, false, true, false, true, false, true, false, true, false],
    [true, false, true, false, true, false],
    [false, true, true, false, true, true, false, true, false, true, true, false, true, false, true,
      false, true, true],
    [true, false, true, true, false, true, false, true, false, true],
    [true, false, true, true, false, true, false, true, false, true, true, false, true, false, true,
      false, true, false, true, false],
    [true, false, true, false, true, false, true, false, true, true],
    [true, false, true, true, false, true, false, true, false, true, true],
    [true, false, true, true, false, true, true, false],
    [true, true, false, true, false, true, true], [],
    [false, true, true, false, true, false, true, true, false, true, false, true, false, true, false,
      true, false],
    [false, true, true, false, true, false, true, false, true, false, true, true, false, true, true,
      false],
    [false], [true, false, true, false, true, true, false],
    [true, true, false, true, false, true, false, true, false, true, true, false, true, false, true,
      false, true, false, true, false],
    [true, true, false, true, true, false, true, true, false, true, true, false, true, false, true,
      false, true],
    [false, true, false, true, false, true, false, true, false, true, false],
    [true, false, true, false, true, false, true, false, true, true, false, true, true, false],
    [true, true, false, true, false, true, false, true, false, true, false, true, true],
    [true, false, true, false, true, true, false, true, false, true, false, true, false, true, false],
    [true, true, false, true, false, true, true, false, true, true, false],
    [false, true, true, false, true, false, true, true, false, true, false, true, false, true, false,
      true, true, false, true, true, false],
    [], [true, false, true, false, true],
    [true, true, false, true, false, true, true, false, true, false, true, false, true, true],
    [false, true, false, true, false, true, false, true, false],
    [false, true, true, false, true, false], [true, true],
    [false, true, true, false, true, true, false, true, true, false, true, false, true, false, true,
      true],
    [false, true],
    [true, true, false, true, true, false, true, false, true, false, true, false, true, false],
    [false, true, false, true, false, true, true, false, true, true, false],
    [false, true, true, false, true, true, false, true, true, false, true, true, false, true, false,
      true, false, true, true],
    [false, true, true, false, true, false, true, false, true, false, true, false],
    [true, true, false, true], [],
    [false, true, false, true, true, false, true, false, true, false, true, false, true, true, false,
      true, false, true, false, true, false, true, false],
    [true, false, true],
    [true, true, false, true, false, true, false, true, true, false, true, true, false],
    [true, false, true, true, false, true, false, true, false, true, false, true, false],
    [true, false, true, false, true, false, true, true, false, true, true, false],
    [false, true, false, true, true, false, true, true, false, true, true, false, true, false, true,
      false, true],
    [false, true, true, false], [false, true, false, true, false, true, true],
    [false, true, true, false, true, false, true, false, true, false, true, false, true, false],
    [true, false, true, true, false],
    [true, true, false, true, false, true, true, false, true, true, false, true, true, false, true,
      false, true, false, true],
    [false, true, false, true, false, true, true, false, true, false, true, true, false, true, false,
      true, false, true, true],
    [],
    [true, false, true, false, true, true, false, true, true, false, true, true, false, true, false,
      true, false, true],
    [true, true, false, true, false, true, false, true, true],
    [true, true, false, true, true, false], [true, false, true, false, true, false, true, true],
    [true, true, false, true, false, true, false, true, false, true, false],
    [true, false, true, true, false, true, false, true, false, true, false, true, true, false, true,
      false, true, false, true, false, true, false],
    [true, true, false, true, true, false, true, true, false, true, true, false, true, false, true,
      false, true, true],
    [true, false, true, false, true, true, false, true, true, false], [true],
    [false, true, false, true, false, true, false, true, true, false, true, true, false],
    [false, true, false, true],
    [true, false, true, false, true, true, false, true, false, true, false, true, true], [],
    [false, true, false, true, true, false, true, false, true, false, true, false, true, false],
    [true, false, true, false, true, false, true, false, true, false, true, true],
    [false, true, true, false, true],
    [false, true, true, false, true, true, false, true, false, true, false, true, true],
    [false, true, false], [true, false, true, true],
    [true, false, true, false, true, false, true, true, false, true, false, true, false, true, false,
      true, false],
    [true, false, true, true, false, true, false, true, true, false, true, false, true, false, true,
      true],
    [true, false, true, false, true, false, true],
    [true, true, false, true, false, true, false, true, false],
    [true, true, false, true, true, false, true, true, false, true, false, true, false, true],
    [false, true, false, true, true, false, true, false, true, false, true, false, true, true, false,
      true, true, false],
    [], [false, true, false, true, false, true, false, true, false, true, false, true, false],
    [false, true, true, false, true, false, true, true, false],
    [false, true, false, true, true, false, true, false, true, true, false, true, false, true, false,
      true, true],
    [false, true, true, false, true, true, false, true, true, false, true, false, true, false, true],
    [false, true, false, true, false, true, false, true, true, false, true, false, true, false, true,
      false, true, false],
    [false, true, false, true, true],
    [true, true, false, true, true, false, true, false, true, false, true, true],
    [true, true, false, true, false, true, true, false],
    [true, false, true, true, false, true, false, true, false, true, false, true, true, false, true,
      true, false],
    [true, false], [false, true, true, false, true, false, true, false, true, false],
    [true, false, true, false, true, false, true, false, true, false, true, false], [],
    [false, true, false, true, false, true, false, true],
    [true, true, false, true, false, true, true, false, true, false, true, false, true, false, true,
      true, false, true, true, false],
    [false, true, true, false, true, false, true, true, false, true, false, true, false, true, true],
    [true, true, false, true, true, false, true, false, true, true, false],
    [false, true, false, true, false, true, true, false, true, false, true, false, true, false, true,
      false],
    [true, true, false, true, false, true, false, true, false, true, false, true, false, true, false],
    [true, true, false, true, true, false, true, true, false, true, false, true, false, true, true],
    [true, false, true, false, true, false, true, false],
    [true, false, true, true, false, true, true, false, true, false, true, false, true],
    [false, true, false, true, false, true], [false, true, true],
    [true, true, false, true, false], []]

@[expose] def wordAt (a b : Fin 12) : List Bool := reachWords.getD (a.val * 12 + b.val) []

section Reach

variable {p₁ p₂ : Perm (Fin 12)} {R : ℕ → Finset (Fin 12 × Fin 12)}
  (h0 : R 0 = {(0, 1)})
  (hs : ∀ n, R (n + 1) = R n ∪ (R n).image (fun q => (p₁ q.1, p₁ q.2)) ∪
      (R n).image (fun q => (p₂ q.1, p₂ q.2)))
include h0 hs

theorem R_mono {m n : ℕ} (h : m ≤ n) : R m ⊆ R n := by
  induction n with
  | zero => rw [Nat.le_zero.1 h]
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le h with h' | rfl
    · rw [hs]
      exact (ih (Nat.lt_succ_iff.1 h')).trans
        (Finset.subset_union_left.trans Finset.subset_union_left)
    · exact le_rfl

theorem mem_word (w : List Bool) : stepW p₁ p₂ w (0, 1) ∈ R w.length := by
  induction w with
  | nil => rw [List.length_nil, h0]; exact Finset.mem_singleton_self _
  | cons b w ih =>
    rw [List.length_cons, hs]
    cases b
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ih))
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ ih)

theorem R_ne : ∀ n, ∀ q ∈ R n, q.1 ≠ q.2 := by
  intro n
  induction n with
  | zero => intro q hq; rw [h0, Finset.mem_singleton] at hq; subst hq; decide
  | succ n ih =>
    intro q hq
    rw [hs] at hq
    simp only [Finset.mem_union, Finset.mem_image] at hq
    rcases hq with (hq | ⟨r, hr, rfl⟩) | ⟨r, hr, rfl⟩
    · exact ih q hq
    · exact fun e => ih r hr (p₁.injective e)
    · exact fun e => ih r hr (p₂.injective e)

theorem card_of_words {N : ℕ} (W : Fin 12 → Fin 12 → List Bool)
    (hW : ∀ a b : Fin 12, a ≠ b → stepW p₁ p₂ (W a b) (0, 1) = (a, b) ∧ (W a b).length ≤ N) :
    (R N).card = 132 := by
  have e : R N = (Finset.univ : Finset (Fin 12 × Fin 12)).filter (fun q => q.1 ≠ q.2) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨R_ne h0 hs N q, fun hq => ?_⟩
    obtain ⟨e1, e2⟩ := hW q.1 q.2 hq
    have := R_mono h0 hs e2 (mem_word h0 hs (W q.1 q.2))
    rwa [e1] at this
  rw [e]
  decide +kernel

end Reach

end CFSG.Sporadic.HN.Local.LabelsK
