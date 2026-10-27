module

public import CFSG.Monster.VisCert.FrameRows
public import CFSG.Monster.VisCert.FrameWords
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
import Batteries.Data.Nat.Bitwise.Lemmas

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisCert

open CFSG.KC.VisFrame CFSG.KC.AxisPlane

theorem native_frameRows_eq : Native.frameRows = frameMatrices := by decide +kernel

theorem cover_actGo_eq (rows : Array ℕ) (v : ℕ) :
    ∀ n acc, CFSG.Monster.AxisCount.Native.Cover.actGo rows v n acc = actGo rows v n acc
  | 0, _ => rfl
  | n + 1, acc => by
    rw [CFSG.Monster.AxisCount.Native.Cover.actGo, actGo, cover_actGo_eq rows v n]

theorem cover_actRows_eq (rows : Array ℕ) (v : ℕ) :
    CFSG.Monster.AxisCount.Native.Cover.actRows rows v = actRows rows v :=
  cover_actGo_eq rows v 24 0

theorem actGo_eq_xor_acc (rows : Array ℕ) (v : ℕ) :
    ∀ n acc, actGo rows v n acc = acc ^^^ actGo rows v n 0
  | 0, acc => by simp [actGo]
  | n + 1, acc => by
    simp only [actGo]
    rw [actGo_eq_xor_acc rows v n (if v.testBit n then acc ^^^ rows[n]! else acc),
      actGo_eq_xor_acc rows v n (if v.testBit n then 0 ^^^ rows[n]! else 0)]
    cases v.testBit n <;> simp [Nat.xor_assoc]

theorem actGo_xor_vec (rows : Array ℕ) (a b : ℕ) :
    ∀ n, actGo rows (a ^^^ b) n 0 = actGo rows a n 0 ^^^ actGo rows b n 0
  | 0 => by simp [actGo]
  | n + 1 => by
    simp only [actGo]
    rw [actGo_eq_xor_acc rows (a ^^^ b) n, actGo_eq_xor_acc rows a n, actGo_eq_xor_acc rows b n,
      actGo_xor_vec rows a b n, Nat.testBit_xor]
    cases a.testBit n <;> cases b.testBit n <;>
      simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

theorem actRows_xor_vec (rows : Array ℕ) (a b : ℕ) :
    actRows rows (a ^^^ b) = actRows rows a ^^^ actRows rows b :=
  actGo_xor_vec rows a b 24

theorem cover_actRows_xor (rows : Array ℕ) (a b : ℕ) :
    CFSG.Monster.AxisCount.Native.Cover.actRows rows (a ^^^ b) =
      CFSG.Monster.AxisCount.Native.Cover.actRows rows a ^^^
        CFSG.Monster.AxisCount.Native.Cover.actRows rows b := by
  rw [cover_actRows_eq, cover_actRows_eq, cover_actRows_eq, actRows_xor_vec]

theorem actWord_xor (gs : Array (Array ℕ)) :
    ∀ (w : List ℕ) (a b : ℕ), actWord gs w (a ^^^ b) = actWord gs w a ^^^ actWord gs w b
  | [], _, _ => rfl
  | g :: w, a, b => by
    simp only [actWord]
    rw [actRows_xor_vec, actWord_xor gs w]

theorem mod_two_pow_succ_eq_xor (x n : ℕ) :
    x % 2 ^ (n + 1) = x % 2 ^ n ^^^ (if x.testBit n then 2 ^ n else 0) := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hj : j = n
  · subst hj
    cases hb : x.testBit j <;> simp
  · have hlt : decide (j < n + 1) = decide (j < n) := by
      simp only [decide_eq_decide]
      omega
    have h2 : (if x.testBit n then 2 ^ n else 0).testBit j = false := by
      split_ifs
      · exact Nat.testBit_two_pow_of_ne (Ne.symm hj)
      · exact Nat.zero_testBit j
    rw [h2, Bool.xor_false, hlt]

theorem xor_ext24 {F G : ℕ → ℕ} (hF : ∀ a b, F (a ^^^ b) = F a ^^^ F b)
    (hG : ∀ a b, G (a ^^^ b) = G a ^^^ G b) (hp : ∀ i < 24, F (2 ^ i) = G (2 ^ i)) {x : ℕ}
    (hx : x < 2 ^ 24) : F x = G x := by
  have z : ∀ H : ℕ → ℕ, (∀ a b, H (a ^^^ b) = H a ^^^ H b) → H 0 = 0 := fun H hH => by
    have := hH 0 0
    rwa [Nat.xor_self, Nat.xor_self] at this
  have key : ∀ n ≤ 24, F (x % 2 ^ n) = G (x % 2 ^ n) := by
    intro n
    induction n with
    | zero => intro _; rw [pow_zero, Nat.mod_one, z F hF, z G hG]
    | succ n ih =>
      intro hn
      rw [mod_two_pow_succ_eq_xor, hF, hG, ih (by omega)]
      congr 1
      split_ifs
      · exact hp n (by omega)
      · rw [z F hF, z G hG]
  have := key 24 le_rfl
  rwa [Nat.mod_eq_of_lt hx] at this

theorem frameWord_eq : ∀ (w : List ℕ) (v : ℕ), frameWord w v = actWord frameMatrices w v
  | [], _ => rfl
  | g :: w, v => by
    change frameWord w (CFSG.Monster.AxisCount.Native.Cover.actRows (Native.frameRows ())[g]! v) =
      actWord frameMatrices w (actRows frameMatrices[g]! v)
    rw [frameWord_eq w, cover_actRows_eq, native_frameRows_eq]

theorem frameWord_xor (w : List ℕ) (a b : ℕ) :
    frameWord w (a ^^^ b) = frameWord w a ^^^ frameWord w b := by
  rw [frameWord_eq, frameWord_eq, frameWord_eq, actWord_xor]

theorem wordAct_cons (g : ℕ) (w : List ℕ) (v : ℕ) :
    wordAct (g :: w) v = wordAct w (CFSG.Monster.AxisCount.Native.Cover.cvImg gens g v) := rfl

theorem wordAct_xor : ∀ (w : List ℕ) (a b : ℕ), wordAct w (a ^^^ b) = wordAct w a ^^^ wordAct w b
  | [], _, _ => rfl
  | g :: w, a, b => by
    rw [wordAct_cons, wordAct_cons, wordAct_cons]
    unfold CFSG.Monster.AxisCount.Native.Cover.cvImg
    rw [cover_actRows_xor, wordAct_xor w]

theorem wordOK_spec {j : ℕ} (hj : j < 14) : (∀ g ∈ words.getD j [], g < 2) ∧
    ∀ i < 24, wordAct (words.getD j []) (2 ^ i) =
      CFSG.Monster.AxisCount.Native.Cover.actRows (Native.frameRows ())[j + 1]! (2 ^ i) := by
  have h := frameWordsOK_eq_true
  rw [frameWordsOK, Bool.and_eq_true, List.all_eq_true] at h
  have h' := h.1 j (List.mem_range.2 hj)
  rw [frameWordOK, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h'
  exact ⟨fun g hg => by simpa using h'.1 g hg,
    fun i hi => by simpa using h'.2 i (List.mem_range.2 hi)⟩

theorem gensOK_spec {i : ℕ} (hi : i < 24) :
    CFSG.Monster.AxisCount.Native.Cover.actRows gen0.toArray (2 ^ i) =
        frameWord [1, 2, 3] (2 ^ i) ∧
      CFSG.Monster.AxisCount.Native.Cover.actRows gen1.toArray (2 ^ i) =
        frameWord [2, 3] (2 ^ i) := by
  have h := frameWordsOK_eq_true
  rw [frameWordsOK, Bool.and_eq_true, frameGensOK] at h
  have h2 := h.2
  rw [List.all_eq_true] at h2
  simpa using h2 i (List.mem_range.2 hi)

theorem dec_cvImg_gens {g : ℕ} (hg : g < 2) {v : ℕ} (hv : v < 2 ^ 24) :
    ∃ n ∈ Nvis, dec (CFSG.Monster.AxisCount.Native.Cover.cvImg gens g v) = n • dec v := by
  rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
  · refine ⟨wordGL [1, 2, 3], wordGL_mem_Nvis _ (by decide), ?_⟩
    rw [wordGL_smul_dec _ (by decide), ← frameWord_eq]
    have e : CFSG.Monster.AxisCount.Native.Cover.cvImg gens 0 v =
        CFSG.Monster.AxisCount.Native.Cover.actRows gen0.toArray v := rfl
    rw [e, xor_ext24 (cover_actRows_xor _) (frameWord_xor _) (fun i hi => (gensOK_spec hi).1) hv]
  · refine ⟨wordGL [2, 3], wordGL_mem_Nvis _ (by decide), ?_⟩
    rw [wordGL_smul_dec _ (by decide), ← frameWord_eq]
    have e : CFSG.Monster.AxisCount.Native.Cover.cvImg gens 1 v =
        CFSG.Monster.AxisCount.Native.Cover.actRows gen1.toArray v := rfl
    rw [e, xor_ext24 (cover_actRows_xor _) (frameWord_xor _) (fun i hi => (gensOK_spec hi).2) hv]

theorem kGenN_smul_dec_wordAct {j : ℕ} (hj1 : 1 ≤ j) (hj : j < 15) {v : ℕ} (hv : v < 2 ^ 24) :
    kGenN j • dec v = dec (wordAct (words.getD (j - 1) []) v) := by
  obtain ⟨-, h⟩ := wordOK_spec (j := j - 1) (by omega)
  rw [Nat.sub_add_cancel hj1] at h
  rw [kGenN_smul_dec' hj, ← native_frameRows_eq, ← cover_actRows_eq]
  exact congrArg dec
    (xor_ext24 (cover_actRows_xor _) (wordAct_xor _) (fun i hi => (h i hi).symm) hv)

theorem wordAct_mem_natOrbit {s : ℕ} : ∀ (w : List ℕ), (∀ g ∈ w, g < 2) → ∀ {v : ℕ},
    v ∈ natOrbit gens s → wordAct w v ∈ natOrbit gens s
  | [], _, _, hv => hv
  | g :: w, hw, v, hv => by
    rw [wordAct_cons]
    exact wordAct_mem_natOrbit w (fun g' hg' => hw g' (List.mem_cons_of_mem _ hg'))
      (Relation.ReflTransGen.tail hv ⟨g, hw g List.mem_cons_self, rfl⟩)

end CFSG.Monster.VisCert
