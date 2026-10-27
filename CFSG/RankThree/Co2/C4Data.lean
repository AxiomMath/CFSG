module

public import CFSG.RankThree.Co2.C4Cert
public import CFSG.RankThree.Co2.C4CertInputs
public import CFSG.RankThree.Co2.Pairs
public import CFSG.RankThree.Co2.SylM

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Co2Inv

theorem rep8_eq : rep 7 * rCr = rep 8 := by
  rw [← rep_zero, rep, rep, rep, ← wordCr_append]
  rfl

theorem rep3_eq : rCr * rep 2 = rep 3 := by
  have e : rep 2 * rCr = rep 3 := by
    rw [← rep_zero, rep, rep, rep, ← wordCr_append]
    rfl
  rw [← e, ← mul_inv_eq_iff_eq_mul.1 (conj_rCr (rep 2))]

theorem eq_rep7_of_lam {y : Cr} {c : ℕ} (hc : c = 2 ∨ c = 7) (hy : IsConj (rep c) y)
    (hcomm : y * rep 8 = rep 8 * y)
    (hA : y * rep 8 = rCr ∨ IsConj (rep 2) (y * rep 8) ∨ IsConj (rep 7) (y * rep 8)) :
    y = rep 7 := by
  have h8 : crMat (rep 8) = repMat 8 := crMat_rep (by norm_num)
  have hy' : CrConj (repMat 2) (crMat y) ∨ CrConj (repMat 7) (crMat y) := by
    rcases hc with rfl | rfl
    · exact Or.inl ((isConj_iff_crConj (by norm_num)).1 hy)
    · exact Or.inr ((isConj_iff_crConj (by norm_num)).1 hy)
  have hcomm' : crMat y * repMat 8 = repMat 8 * crMat y := by
    rw [← h8, ← map_mul, ← map_mul, hcomm]
  have hA' : crMat y * repMat 8 = repMat 0 ∨ CrConj (repMat 2) (crMat y * repMat 8) ∨
      CrConj (repMat 7) (crMat y * repMat 8) := by
    rw [← h8, ← map_mul]
    rcases hA with e | e | e
    · left
      rw [e, ← rep_zero, crMat_rep (i := 0) (by norm_num)]
    · exact Or.inr (Or.inl ((isConj_iff_crConj (by norm_num)).1 e))
    · exact Or.inr (Or.inr ((isConj_iff_crConj (by norm_num)).1 e))
  apply crMat_injective
  rw [crMat_rep (i := 7) (by norm_num)]
  exact c4Facts_cert.lam _ hy' hcomm' hA'

theorem zuGenWords_letters : ∀ k < 4, ∀ l ∈ zuGenWords[k]!, l < 42 := by
  decide +kernel

theorem pWords8_letters : ∀ k < pWords8.size, ∀ l ∈ pWords8[k]!, l < 42 := by
  decide +kernel

theorem zuCls_lt {m : ℕ} (hm : m < 16) : zuCls[m]! < 10 := by
  have h : ∀ m < 16, zuCls[m]! < 10 := by decide
  exact h m hm

def zuBit (n m : ℕ) : Cr :=
  if m.testBit n then wordCr zuGenWords[n]! else 1

def zuPtN : ℕ → ℕ → Cr
  | 0, _ => 1
  | n + 1, m => zuPtN n m * zuBit n m

def zuPt (m : ℕ) : Cr := zuPtN 4 m

theorem crMat_zuPtN (m : ℕ) :
    ∀ n ≤ 4, crMat (zuPtN n m) = zuMatN n m
  | 0, _ => map_one crMat
  | n + 1, hn => by
    rw [zuPtN, zuMatN, map_mul, crMat_zuPtN m n (by omega), zuBit]
    split_ifs
    · rw [crMat_wordCr (zuGenWords_letters n (by omega))]
    · rw [map_one]

theorem crMat_zuPt (m : ℕ) : crMat (zuPt m) = zuMat m :=
  crMat_zuPtN m 4 le_rfl

theorem zuGen_sq {k : ℕ} (hk : k < 4) :
    wordCr zuGenWords[k]! * wordCr zuGenWords[k]! = 1 := by
  apply crMat_injective
  rw [map_mul, map_one, crMat_wordCr (zuGenWords_letters k hk)]
  exact c4Facts_cert.sq k hk

theorem zuBit_comm {k j : ℕ} (hk : k < 4) (hj : j < 4) (m m' : ℕ) :
    zuBit k m * zuBit j m' = zuBit j m' * zuBit k m := by
  unfold zuBit
  split_ifs
  · apply crMat_injective
    rw [map_mul, map_mul, crMat_wordCr (zuGenWords_letters k hk),
      crMat_wordCr (zuGenWords_letters j hj)]
    exact c4Facts_cert.comm k hk j hj
  all_goals simp only [mul_one, one_mul]

theorem zuBit_comm_zuPtN {k : ℕ} (hk : k < 4) (m m' : ℕ) :
    ∀ n ≤ 4, zuBit k m * zuPtN n m' = zuPtN n m' * zuBit k m
  | 0, _ => by rw [zuPtN, mul_one, one_mul]
  | n + 1, hn => by
    rw [zuPtN, ← mul_assoc, zuBit_comm_zuPtN hk m m' n (by omega), mul_assoc,
      zuBit_comm hk (by omega) m m', mul_assoc]

theorem zuPtN_mul (m m' : ℕ) :
    ∀ n ≤ 4, zuPtN n m * zuPtN n m' = zuPtN n (m ^^^ m')
  | 0, _ => by rw [zuPtN, zuPtN, zuPtN, mul_one]
  | n + 1, hn => by
    have hb : zuBit n m * zuBit n m' = zuBit n (m ^^^ m') := by
      unfold zuBit
      rw [Nat.testBit_xor]
      cases m.testBit n <;> cases m'.testBit n <;> simp [zuGen_sq (k := n) (by omega)]
    rw [zuPtN, zuPtN, zuPtN, mul_assoc, ← mul_assoc (zuBit n m),
      zuBit_comm_zuPtN (by omega) m m' n (by omega), mul_assoc, ← mul_assoc (zuPtN n m),
      zuPtN_mul m m' n (by omega), hb]

theorem zuPtN_zero : ∀ n, zuPtN n 0 = 1
  | 0 => rfl
  | n + 1 => by rw [zuPtN, zuPtN_zero n, zuBit, Nat.zero_testBit, if_neg Bool.false_ne_true, mul_one]

theorem zuPt_mul {m m' : ℕ} (_hm : m < 16) (_hm' : m' < 16) : zuPt m * zuPt m' = zuPt (m ^^^ m') :=
  zuPtN_mul m m' 4 le_rfl

theorem zuPt_zero : zuPt 0 = 1 := zuPtN_zero 4

theorem zuPt_eq (m : ℕ) :
    zuPt m = 1 * zuBit 0 m * zuBit 1 m * zuBit 2 m * zuBit 3 m := by
  rw [zuPt, zuPtN, zuPtN, zuPtN, zuPtN, zuPtN]

theorem zuPt_bit {k : ℕ} (hk : k < 4) :
    zuPt (2 ^ k) = wordCr zuGenWords[k]! := by
  have hb : ∀ n, zuBit n (2 ^ k) = if n = k then wordCr zuGenWords[k]! else 1 := by
    intro n
    unfold zuBit
    rw [Nat.testBit_two_pow]
    by_cases e : n = k
    · subst e
      simp
    · have e' : k ≠ n := fun h => e h.symm
      simp [e, e']
  rw [zuPt_eq, hb 0, hb 1, hb 2, hb 3]
  interval_cases k <;> simp

theorem zuPt_one : zuPt 1 = rCr := by
  rw [← rep_zero, rep]
  exact (zuPt_bit (k := 0) (by norm_num)).trans (congrArg wordCr (by decide))

theorem zuPt_two : zuPt 2 = rep 7 := by
  rw [rep]
  exact (zuPt_bit (k := 1) (by norm_num)).trans (congrArg wordCr (by decide))

theorem zuPt_isConj {m : ℕ} (hm : m < 16) (hm0 : m ≠ 0) : IsConj (rep zuCls[m]!) (zuPt m) := by
  rw [isConj_iff_crConj (zuCls_lt hm), crMat_zuPt]
  exact c4Facts_cert.cls m (Nat.pos_of_ne_zero hm0) hm

theorem zuPt_ne_one {m : ℕ} (hm : m < 16) (hm0 : m ≠ 0) : zuPt m ≠ 1 := by
  intro e
  have h := zuPt_isConj hm hm0
  rw [e, isConj_one_left] at h
  exact rep_ne_one (zuCls_lt hm) h

theorem zuPt_inj {m m' : ℕ} (hm : m < 16) (hm' : m' < 16) (e : zuPt m = zuPt m') : m = m' := by
  have hx : m ^^^ m' < 16 := Nat.xor_lt_two_pow (n := 4) hm hm'
  by_contra hne
  have h0 : m ^^^ m' ≠ 0 := by
    have key : ∀ a < 16, ∀ b < 16, a ^^^ b = 0 → a = b := by decide
    exact fun h => hne (key m hm m' hm' h)
  apply zuPt_ne_one hx h0
  rw [← zuPt_mul hm hm', e, zuPt_mul hm' hm', Nat.xor_self, zuPt_zero]

theorem zuPt_mem {m : ℕ} (hm : m < 16) : zuPt m ∈ subW pWords8 := by
  obtain ⟨x, hx, e⟩ := matGrp_le_map pWords8_letters (c4Facts_cert.mem m hm).1
  rw [← crMat_zuPt] at e
  rw [← crMat_injective e]
  exact hx

theorem zuPt_central {m : ℕ} (hm : m < 16) {u : Cr} (hu : u ∈ subW pWords8) :
    zuPt m * u = u * zuPt m := by
  apply crMat_injective
  rw [map_mul, map_mul, crMat_zuPt]
  exact (c4Facts_cert.mem m hm).2 _ (map_subW_le pWords8_letters ⟨u, hu, rfl⟩)

theorem exists_zuPt {y : Cr} (hy : y ∈ subW pWords8)
    (hc : ∀ u ∈ subW pWords8, y * u = u * y) : ∃ m < 16, y = zuPt m := by
  have hcard : Nat.card (matGrp pWords8) ≤ 2 ^ 14 :=
    (card_matGrp_le pWords8_letters).trans (le_of_eq sylCard8)
  have hz : ∀ z ∈ matGrp pWords8, crMat y * z = z * crMat y := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := matGrp_le_map pWords8_letters hz
    rw [← map_mul, ← map_mul, hc x hx]
  obtain ⟨m, hm, e⟩ := c4Facts_cert.all hcard _ (map_subW_le pWords8_letters ⟨y, hy, rfl⟩) hz
  exact ⟨m, hm, crMat_injective (by rw [e, crMat_zuPt])⟩

@[expose] def zuLab (m : ℕ) : ℕ := if m = 0 then 0 else gLab zuCls[m]!

theorem xor_lt16 {a b : ℕ} (ha : a < 16) (hb : b < 16) : a ^^^ b < 16 :=
  Nat.xor_lt_two_pow (n := 4) ha hb

theorem zu_aut : ∀ t₂ < 16, ∀ t₃ < 16, (∀ m < 16, sigma t₂ t₃ (sigma t₂ t₃ m) = m ∧
    zuLab (sigma t₂ t₃ m) = zuLab m) → ∃ m < 16, zuLab (m ^^^ sigma t₂ t₃ m) = 1 := by
  decide +kernel

theorem eq_sigma {p : ℕ → ℕ} (hp : ∀ a < 16, ∀ b < 16, p (a ^^^ b) = p a ^^^ p b)
    (h0 : p 0 = 0) (h1 : p 1 = 2) (h2 : p 2 = 1) {m : ℕ} (hm : m < 16) :
    p m = sigma (p 4) (p 8) m := by
  have key : ∀ m < 16, m = (if m.testBit 0 then 1 else 0) ^^^ (if m.testBit 1 then 2 else 0) ^^^
      (if m.testBit 2 then 4 else 0) ^^^ (if m.testBit 3 then 8 else 0) := by decide
  have hb : ∀ (b : Bool) (v : ℕ), p (if b then v else 0) = if b then p v else 0 := by
    intro b v
    cases b <;> simp [h0]
  have hlt : ∀ (b : Bool) (v : ℕ), v < 16 → (if b then v else 0) < 16 := by
    intro b v hv
    cases b <;> simp [hv]
  have x1 := hlt (m.testBit 0) 1 (by norm_num)
  have x2 := hlt (m.testBit 1) 2 (by norm_num)
  have x3 := hlt (m.testBit 2) 4 (by norm_num)
  have x4 := hlt (m.testBit 3) 8 (by norm_num)
  have y12 := xor_lt16 x1 x2
  have y123 := xor_lt16 y12 x3
  calc p m = p ((if m.testBit 0 then 1 else 0) ^^^ (if m.testBit 1 then 2 else 0) ^^^
        (if m.testBit 2 then 4 else 0) ^^^ (if m.testBit 3 then 8 else 0)) :=
        congrArg p (key m hm)
    _ = sigma (p 4) (p 8) m := by
      rw [hp _ y123 _ x4, hp _ y12 _ x3, hp _ x1 _ x2, hb, hb, hb, hb, h1, h2]
      rfl

end CFSG.RankThree.Co2
