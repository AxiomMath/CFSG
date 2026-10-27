module

public import CFSG.Quasithin.Recognition.M12AmalAutData
public import CFSG.Quasithin.Recognition.CertPermList
public import CFSG.Sporadic.Bridge.Common
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Quasithin.M12AmalAut

open CFSG.Sporadic.Bridge Equiv

@[expose] def bA : Perm (Fin 24) :=
  List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11] *
    List.formPerm [12, 15] * List.formPerm [14, 21] * List.formPerm [16, 22] * List.formPerm [17, 23]

@[expose] def bB : Perm (Fin 24) :=
  List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
    List.formPerm [5, 9, 6] * List.formPerm [12, 17, 15] * List.formPerm [13, 20, 14] *
    List.formPerm [16, 19, 21] * List.formPerm [18, 22, 23]

@[expose] def bS : Perm (Fin 24) :=
  List.formPerm [0, 12] * List.formPerm [1, 13] * List.formPerm [2, 14] * List.formPerm [3, 15] *
    List.formPerm [4, 16] * List.formPerm [5, 17] * List.formPerm [6, 18] * List.formPerm [7, 19] *
    List.formPerm [8, 20] * List.formPerm [9, 21] * List.formPerm [10, 22] * List.formPerm [11, 23]

@[expose] def autM12Model : Subgroup (Perm (Fin 24)) := Subgroup.closure {bA, bB, bS}

abbrev AutG : Type := ↥autM12Model

@[expose] def bGen (i : ℕ) : Perm (Fin 24) := if i = 0 then bA else if i = 1 then bB else bS

@[expose] def genP (i : ℕ) : Perm (Fin 24) :=
  if i = 0 then
    List.formPerm [0, 14] * List.formPerm [1, 17] * List.formPerm [2, 20] * List.formPerm [3, 16] *
      List.formPerm [4, 19] * List.formPerm [5, 22] * List.formPerm [6, 13] * List.formPerm [7, 12] *
      List.formPerm [8, 21] * List.formPerm [9, 18] * List.formPerm [10, 15] * List.formPerm [11, 23]
  else if i = 1 then
    List.formPerm [0, 17, 3, 16] * List.formPerm [1, 14, 2, 20] * List.formPerm [4, 23] *
      List.formPerm [5, 18, 10, 13] * List.formPerm [6, 19, 9, 21] * List.formPerm [7, 15] *
      List.formPerm [8, 12] * List.formPerm [11, 22]
  else if i = 2 then
    List.formPerm [0, 1] * List.formPerm [5, 10] * List.formPerm [6, 7] * List.formPerm [9, 11] *
      List.formPerm [12, 18] * List.formPerm [13, 23] * List.formPerm [15, 22] *
      List.formPerm [16, 20]
  else if i = 3 then
    List.formPerm [0, 1, 2] * List.formPerm [4, 5, 9] * List.formPerm [6, 8, 10] *
      List.formPerm [13, 22, 19] * List.formPerm [14, 17, 16] * List.formPerm [15, 21, 18]
  else if i = 4 then
    List.formPerm [0, 11, 4] * List.formPerm [1, 7, 8] * List.formPerm [2, 9, 10] *
      List.formPerm [3, 6, 5] * List.formPerm [12, 21, 17] * List.formPerm [13, 22, 16] *
      List.formPerm [14, 23, 19] * List.formPerm [15, 20, 18]
  else 1

@[expose] def genMCodes : List (List Nat) :=
  [[2, 0, 4, 3],
   [2, 4, 2, 0, 4, 3, 0, 3, 0, 3, 0, 4, 3, 0, 3, 0],
   [3, 0, 2, 4, 2, 0, 3, 4, 2, 0, 2, 0, 2],
   [4, 3, 0, 2, 4, 3, 0, 3, 0, 2, 0, 3, 0],
   [0, 2, 4, 2, 0, 4, 3, 0, 2, 0, 4, 3, 0, 4, 3]]

@[expose] def mCodes : List (List Nat) :=
  [[7, 8, 6, 0, 8, 7, 3, 8, 7, 8],
   [4, 6, 8, 4, 6, 8, 6, 9, 7, 9],
   [8, 6, 2, 8, 7, 8, 7, 9]]

@[expose] def decode (c : List Nat) : List (Nat × Bool) :=
  c.map fun n => (n / 2, n % 2 == 0)

@[expose] def telW (i : ℕ) : List (ℕ × Bool) := decode (telCodes.getD i [])

@[expose] def dW (j : ℕ) : List (ℕ × Bool) := decode (dCodes.getD j [])

@[expose] def letterL (l : ℕ × Bool) : List ℕ :=
  if l.2 then genTab.getD l.1 [] else genInvTab.getD l.1 []

@[expose] def wordL : List (ℕ × Bool) → List ℕ
  | [] => List.range 24
  | l :: w => compL (letterL l) (wordL w)

@[expose] def letterL4 (j : ℕ) (l : ℕ × Bool) : List ℕ :=
  if l.1 < 3 then letterL l else if l.2 then dTab.getD j [] else dInvTab.getD j []

@[expose] def wordL4 (j : ℕ) : List (ℕ × Bool) → List ℕ
  | [] => List.range 24
  | l :: w => compL (letterL4 j l) (wordL4 j w)

theorem bGen_mem (i : ℕ) : bGen i ∈ autM12Model := by
  unfold bGen autM12Model
  split_ifs
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem genP_eq : ∀ k < 5, genP k = wordProd bGen (decode (genMCodes.getD k [])) := by
  decide +kernel

theorem genP_mem (k : ℕ) (hk : k < 5) : genP k ∈ autM12Model := by
  rw [genP_eq k hk]
  exact wordProd_mem bGen_mem _

theorem bGen_eq : ∀ i < 3, bGen i = wordProd genP (decode (mCodes.getD i [])) := by
  decide +kernel

theorem genTab_rep : ∀ k < 5, RepL (genTab.getD k []) (genP k) := by decide +kernel

theorem genInvTab_rep : ∀ k < 5, RepL (genInvTab.getD k []) (genP k)⁻¹ := by decide +kernel

theorem telLetters : ∀ i < 128, ∀ l ∈ telW i, l.1 < 3 := by decide +kernel

theorem dLetters : ∀ j < 28, ∀ l ∈ dW j, l.1 < 5 := by decide +kernel

theorem telTab_eq : ∀ i < 128, telTab.getD i [] = wordL (telW i) := by decide +kernel

theorem dTab_eq : ∀ j < 28, dTab.getD j [] = wordL (dW j) := by decide +kernel

@[expose] def invW (w : List (ℕ × Bool)) : List (ℕ × Bool) := w.reverse.map fun l => (l.1, !l.2)

theorem dInvTab_eq : ∀ j < 28, dInvTab.getD j [] = wordL (invW (dW j)) := by decide +kernel

theorem dInvLetters : ∀ j < 28, ∀ l ∈ invW (dW j), l.1 < 5 := by decide +kernel

theorem genP_orders : genP 0 ^ 4 = 1 ∧ genP 1 ^ 4 = 1 ∧ genP 2 ^ 2 = 1 ∧ genP 3 ^ 3 = 1 ∧
    genP 4 ^ 3 = 1 := by decide +kernel

@[expose] def genG (k : ℕ) : AutG :=
  if h : k < 5 then ⟨genP k, genP_mem k h⟩ else 1

theorem genG_coe (k : ℕ) (hk : k < 5) :
    ((genG k : AutG) : Perm (Fin 24)) = genP k := by
  simp [genG, hk]

theorem wordProd_congr {G : Type*} [Group G] {x y : ℕ → G} (w : List (ℕ × Bool))
    (h : ∀ l ∈ w, x l.1 = y l.1) : wordProd x w = wordProd y w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [h l (by simp), ih (fun l' hl' => h l' (by simp [hl']))]

theorem wordProd_invW {G : Type*} [Group G] (x : ℕ → G) (w : List (ℕ × Bool)) :
    wordProd x (invW w) = (wordProd x w)⁻¹ := by
  induction w with
  | nil => simp [invW, wordProd]
  | cons l w ih =>
    have e : invW (l :: w) = invW w ++ [(l.1, !l.2)] := by simp [invW]
    rw [e]
    simp only [wordProd, List.map_append, List.prod_append, List.map_cons, List.prod_cons,
      List.map_nil, List.prod_nil, mul_one, mul_inv_rev] at ih ⊢
    rw [ih]
    cases l.2 <;> simp

abbrev ReprG (l : List ℕ) (g : AutG) : Prop :=
  RepL (n := 24) l (g : Perm (Fin 24))

theorem reprG_mul {l m : List ℕ} {g h : AutG} (hl : ReprG l g)
    (hm : ReprG m h) : ReprG (compL l m) (g * h) :=
  repL_mul hl hm

theorem eq_of_reprG {l : List ℕ} {g h : AutG} (hg : ReprG l g)
    (hh : ReprG l h) : g = h :=
  Subtype.ext (eq_of_repL hg hh)

theorem ne_of_reprG {l m : List ℕ} {g h : AutG} (hg : ReprG l g)
    (hh : ReprG m h) (hlm : l ≠ m) : g ≠ h := by
  rintro rfl
  exact hlm (repL_unique hg hh)

theorem reprG_gen (k : ℕ) (hk : k < 5) : ReprG (genTab.getD k []) (genG k) := by
  have := genTab_rep k hk
  unfold ReprG
  rwa [genG_coe k hk]

theorem reprG_inv_gen (k : ℕ) (hk : k < 5) : ReprG (genInvTab.getD k []) (genG k)⁻¹ := by
  have := genInvTab_rep k hk
  unfold ReprG
  rwa [Subgroup.coe_inv, genG_coe k hk]

theorem reprG_one : ReprG (List.range 24) 1 := repL_one 24

theorem wordL_rep : ∀ w : List (ℕ × Bool), (∀ l ∈ w, l.1 < 5) →
    ReprG (wordL w) (wordProd genG w) := by
  intro w
  induction w with
  | nil => intro _; simpa [wordL, wordProd] using reprG_one
  | cons l w ih =>
    intro h
    have hl : l.1 < 5 := h l (by simp)
    have h1 : ReprG (letterL l) (if l.2 then genG l.1 else (genG l.1)⁻¹) := by
      unfold letterL
      split_ifs
      · exact reprG_gen l.1 hl
      · exact reprG_inv_gen l.1 hl
    have h2 := ih (fun l' hl' => h l' (by simp [hl']))
    simp only [wordL, wordProd, List.map_cons, List.prod_cons] at h2 ⊢
    exact reprG_mul h1 h2

@[expose] def telG (i : ℕ) : AutG := wordProd genG (telW i)

@[expose] def dG (j : ℕ) : AutG := wordProd genG (dW j)

theorem reprG_tel (i : ℕ) (hi : i < 128) : ReprG (telTab.getD i []) (telG i) := by
  rw [telTab_eq i hi]
  exact wordL_rep (telW i) (fun l hl => by have := telLetters i hi l hl; omega)

theorem reprG_d (j : ℕ) (hj : j < 28) : ReprG (dTab.getD j []) (dG j) := by
  rw [dTab_eq j hj]
  exact wordL_rep (dW j) (dLetters j hj)

theorem reprG_dInv (j : ℕ) (hj : j < 28) : ReprG (dInvTab.getD j []) (dG j)⁻¹ := by
  rw [dInvTab_eq j hj]
  have := wordL_rep (invW (dW j)) (dInvLetters j hj)
  rwa [wordProd_invW] at this

@[expose] def gen4 (d : AutG) (i : ℕ) : AutG :=
  if i = 0 then genG 0 else if i = 1 then genG 1 else if i = 2 then genG 2 else d

theorem wordL4_rep (j : ℕ) (hj : j < 28) : ∀ w : List (ℕ × Bool), (∀ l ∈ w, l.1 < 4) →
    ReprG (wordL4 j w) (wordProd (gen4 (dG j)) w) := by
  intro w
  induction w with
  | nil => intro _; simpa [wordL4, wordProd] using reprG_one
  | cons l w ih =>
    intro h
    have hl : l.1 < 4 := h l (by simp)
    have h1 : ReprG (letterL4 j l) (if l.2 then gen4 (dG j) l.1 else (gen4 (dG j) l.1)⁻¹) := by
      unfold letterL4
      by_cases h3 : l.1 < 3
      · have e : gen4 (dG j) l.1 = genG l.1 := by
          unfold gen4
          have : l.1 = 0 ∨ l.1 = 1 ∨ l.1 = 2 := by omega
          rcases this with e | e | e <;> simp [e]
        rw [e]
        simp only [h3, ↓reduceIte]
        unfold letterL
        split_ifs
        · exact reprG_gen l.1 (by omega)
        · exact reprG_inv_gen l.1 (by omega)
      · have e : gen4 (dG j) l.1 = dG j := by
          unfold gen4
          have : l.1 = 3 := by omega
          simp [this]
        rw [e]
        simp only [h3, ↓reduceIte]
        split_ifs
        · exact reprG_d j hj
        · exact reprG_dInv j hj
    have h2 := ih (fun l' hl' => h l' (by simp [hl']))
    simp only [wordL4, wordProd, List.map_cons, List.prod_cons] at h2 ⊢
    exact reprG_mul h1 h2

private def pack (B : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: l => a + B * pack B l

private def digit (B c k : ℕ) : ℕ := Nat.mod (Nat.div c (Nat.pow B k)) B

private theorem nat_pow_succ (B k : ℕ) : Nat.pow B (k + 1) = B * Nat.pow B k :=
  Nat.mul_comm _ _

private theorem digit_pack {B : ℕ} {l : List ℕ} (hl : ∀ a ∈ l, a < B) (k : ℕ) :
    digit B (pack B l) k = l.getD k 0 := by
  induction l generalizing k with
  | nil =>
    show 0 / Nat.pow B k % B = 0
    simp
  | cons a l ih =>
    have ha : a < B := hl a (by simp)
    have hB : 0 < B := by omega
    cases k with
    | zero =>
      show (a + B * pack B l) / 1 % B = a
      rw [Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
    | succ k =>
      show (a + B * pack B l) / Nat.pow B (k + 1) % B = l.getD k 0
      rw [nat_pow_succ, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hB,
        Nat.div_eq_of_lt ha, Nat.zero_add]
      exact ih (fun b hb => hl b (by simp [hb])) k

private theorem pack_inj {l l' : List ℕ} (hl : ∀ a ∈ l, a < 32) (hl' : ∀ a ∈ l', a < 32)
    (hlen : l.length = l'.length) (h : pack 32 l = pack 32 l') : l = l' := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons a l ih =>
    cases l' with
    | nil => simp at hlen
    | cons a' l' =>
      have ha : a < 32 := hl a (by simp)
      have ha' : a' < 32 := hl' a' (by simp)
      simp only [pack] at h
      have e1 : a = a' := by omega
      have e2 : pack 32 l = pack 32 l' := by omega
      rw [e1, ih (fun b hb => hl b (by simp [hb])) (fun b hb => hl' b (by simp [hb]))
        (by simpa using hlen) e2]

private def compCode (c : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, d => Nat.add (digit 32 c (Nat.mod d 32)) (Nat.mul 32 (compCode c n (Nat.div d 32)))

private theorem compCode_succ (c n d : ℕ) :
    compCode c (n + 1) d = digit 32 c (d % 32) + 32 * compCode c n (d / 32) := rfl

private theorem compL_cons (l m : List ℕ) (b : ℕ) :
    compL l (b :: m) = l.getD b 0 :: compL l m := rfl

private theorem length_compL (l m : List ℕ) : (compL l m).length = m.length := by simp [compL]

private theorem compL_getD {l m : List ℕ} {p : ℕ} (hp : p < m.length) :
    (compL l m).getD p 0 = l.getD (m.getD p 0) 0 := by
  rw [List.getD_eq_getElem _ _ (by rwa [length_compL]), List.getD_eq_getElem _ _ hp]
  simp [compL]

private theorem compL_lt {l : List ℕ} (hl : ∀ a ∈ l, a < 32) (m : List ℕ) :
    ∀ a ∈ compL l m, a < 32 := by
  intro a ha
  simp only [compL, List.mem_map] at ha
  obtain ⟨j, -, rfl⟩ := ha
  rcases Nat.lt_or_ge j l.length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    exact hl _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ h]
    omega

private theorem compCode_pack {l m : List ℕ} {n : ℕ} (hl : ∀ a ∈ l, a < 32)
    (hm : ∀ b ∈ m, b < 32) (hn : m.length = n) :
    compCode (pack 32 l) n (pack 32 m) = pack 32 (compL l m) := by
  subst hn
  induction m with
  | nil => rfl
  | cons b m ih =>
    have hb : b < 32 := hm b (by simp)
    have h1 : (b + 32 * pack 32 m) % 32 = b := by omega
    have h2 : (b + 32 * pack 32 m) / 32 = pack 32 m := by omega
    rw [List.length_cons, compCode_succ, pack, h1, h2, ih (fun c hc => hm c (by simp [hc])),
      digit_pack hl, compL_cons, pack]

private theorem compL_compL_eq {x y z u v w : List ℕ} (hx : ∀ a ∈ x, a < 32)
    (hu : ∀ a ∈ u, a < 32) (hy : y.length = 24 ∧ ∀ a ∈ y, a < 32)
    (hz : z.length = 24 ∧ ∀ a ∈ z, a < 32) (hv : v.length = 24 ∧ ∀ a ∈ v, a < 32)
    (hw : w.length = 24 ∧ ∀ a ∈ w, a < 32)
    (h : compCode (compCode (pack 32 x) 24 (pack 32 y)) 24 (pack 32 z) =
      compCode (compCode (pack 32 u) 24 (pack 32 v)) 24 (pack 32 w)) :
    compL (compL x y) z = compL (compL u v) w := by
  rw [compCode_pack hx hy.2 hy.1, compCode_pack (compL_lt hx y) hz.2 hz.1,
    compCode_pack hu hv.2 hv.1, compCode_pack (compL_lt hu v) hw.2 hw.1] at h
  exact pack_inj (compL_lt (compL_lt hx y) z) (compL_lt (compL_lt hu v) w)
    (by simp only [length_compL, hz.1, hw.1]) h

private def triplesAll (p : ℕ → ℕ → ℕ → ℕ → Bool) : List ℕ → List ℕ → Bool
  | k :: a :: b :: r, t :: ts => p k a b t && triplesAll p r ts
  | _, [] => true
  | _, _ :: _ => false

private theorem triplesAll_getD {p : ℕ → ℕ → ℕ → ℕ → Bool} {row ts : List ℕ}
    (h : triplesAll p row ts = true) {i : ℕ} (hi : i < ts.length) :
    p (row.getD (3 * i) 0) (row.getD (3 * i + 1) 0) (row.getD (3 * i + 2) 0) (ts.getD i 0) =
      true := by
  induction ts generalizing row i with
  | nil => simp at hi
  | cons t ts ih =>
    match row, h with
    | k :: a :: b :: r, h =>
      simp only [triplesAll, Bool.and_eq_true] at h
      cases i with
      | zero => simpa using h.1
      | succ i =>
        have := ih h.2 (i := i) (by simpa using hi)
        simpa [show 3 * (i + 1) = 3 * i + 2 + 1 by omega,
          show 3 * (i + 1) + 1 = 3 * i + 3 + 1 by omega,
          show 3 * (i + 1) + 2 = 3 * i + 4 + 1 by omega] using this
    | [], h => simp [triplesAll] at h
    | [_], h => simp [triplesAll] at h
    | [_, _], h => simp [triplesAll] at h

private def differAt (x z w : ℕ) : ℕ → Bool
  | 0 => false
  | n + 1 => digit 32 x (digit 32 z n) != digit 32 w n || differAt x z w n

private theorem differAt_spec {x z w n : ℕ} (h : differAt x z w n = true) :
    ∃ p < n, digit 32 x (digit 32 z p) ≠ digit 32 w p := by
  induction n with
  | zero => simp [differAt] at h
  | succ n ih =>
    simp only [differAt, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
    rcases h with h | h
    · exact ⟨n, by omega, h⟩
    · obtain ⟨p, hp, h'⟩ := ih h
      exact ⟨p, by omega, h'⟩

@[expose] def decXk (j i : ℕ) : ℕ := (decXTab.getD j []).getD (3 * i) 0

@[expose] def decXa (j i : ℕ) : ℕ := (decXTab.getD j []).getD (3 * i + 1) 0

@[expose] def decXb (j i : ℕ) : ℕ := (decXTab.getD j []).getD (3 * i + 2) 0

@[expose] def decYk (j i : ℕ) : ℕ := (decYTab.getD j []).getD (3 * i) 0

@[expose] def decYa (j i : ℕ) : ℕ := (decYTab.getD j []).getD (3 * i + 1) 0

@[expose] def decYb (j i : ℕ) : ℕ := (decYTab.getD j []).getD (3 * i + 2) 0

private def telPk : List ℕ := telTab.map (pack 32)

private def dPk : List ℕ := dTab.map (pack 32)

private def telBig : ℕ := pack (2 ^ 120) telPk

private def dBig : ℕ := pack (2 ^ 120) dPk

private theorem telTab_fits : ∀ l ∈ telTab, l.length = 24 ∧ ∀ a ∈ l, a < 32 := by
  decide +kernel

private theorem dTab_fits : ∀ l ∈ dTab, l.length = 24 ∧ ∀ a ∈ l, a < 32 := by decide +kernel

private theorem genTab_fits : ∀ l ∈ genTab, l.length = 24 ∧ ∀ a ∈ l, a < 32 := by
  decide +kernel

private theorem telPk_lt : ∀ c ∈ telPk, c < 2 ^ 120 := by decide +kernel

private theorem dPk_lt : ∀ c ∈ dPk, c < 2 ^ 120 := by decide +kernel

private theorem telTab_length : telTab.length = 128 := by decide +kernel

private theorem dTab_length : dTab.length = 28 := by decide +kernel

private theorem genTab_length : genTab.length = 5 := by decide +kernel

private theorem getD_fits {T : List (List ℕ)} (hT : ∀ l ∈ T, l.length = 24 ∧ ∀ a ∈ l, a < 32)
    {i : ℕ} (hi : i < T.length) : (T.getD i []).length = 24 ∧ ∀ a ∈ T.getD i [], a < 32 := by
  rw [List.getD_eq_getElem _ _ hi]
  exact hT _ (List.getElem_mem hi)

private theorem telTab_getD_fits {i : ℕ} (hi : i < 128) :
    (telTab.getD i []).length = 24 ∧ ∀ a ∈ telTab.getD i [], a < 32 :=
  getD_fits telTab_fits (by rw [telTab_length]; exact hi)

private theorem dTab_getD_fits {j : ℕ} (hj : j < 28) :
    (dTab.getD j []).length = 24 ∧ ∀ a ∈ dTab.getD j [], a < 32 :=
  getD_fits dTab_fits (by rw [dTab_length]; exact hj)

private theorem genTab_getD_fits {g : ℕ} (hg : g < 5) :
    (genTab.getD g []).length = 24 ∧ ∀ a ∈ genTab.getD g [], a < 32 :=
  getD_fits genTab_fits (by rw [genTab_length]; exact hg)

private theorem length_telPk : telPk.length = 128 := by simp [telPk, telTab_length]

private theorem telPk_getD (i : ℕ) : telPk.getD i 0 = pack 32 (telTab.getD i []) :=
  List.getD_map telTab [] (pack 32)

private theorem digit_telBig (a : ℕ) : digit (2 ^ 120) telBig a = pack 32 (telTab.getD a []) := by
  rw [telBig, digit_pack telPk_lt, telPk_getD]

private theorem digit_dBig (k : ℕ) : digit (2 ^ 120) dBig k = pack 32 (dTab.getD k []) := by
  rw [dBig, digit_pack dPk_lt]
  exact List.getD_map dTab [] (pack 32)

private def nextOK (t g n : ℕ) : Bool := n < 128 && compCode t 24 g == digit (2 ^ 120) telBig n

private theorem telNext_rows : triplesAll (fun n₀ n₁ n₂ t =>
    nextOK t (pack 32 (genTab.getD 0 [])) n₀ && nextOK t (pack 32 (genTab.getD 1 [])) n₁ &&
      nextOK t (pack 32 (genTab.getD 2 [])) n₂) telNext telPk = true := by
  decide +kernel

private theorem nextOK_spec {i g n : ℕ} (hi : i < 128) (hg : g < 5)
    (h : nextOK (telPk.getD i 0) (pack 32 (genTab.getD g [])) n = true) :
    n < 128 ∧ compL (telTab.getD i []) (genTab.getD g []) = telTab.getD n [] := by
  simp only [nextOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, digit_telBig,
    telPk_getD] at h
  obtain ⟨hn, he⟩ := h
  have ht := telTab_getD_fits hi
  have hgg := genTab_getD_fits hg
  have htn := telTab_getD_fits hn
  rw [compCode_pack ht.2 hgg.2 hgg.1] at he
  exact ⟨hn, pack_inj (compL_lt ht.2 _) htn.2 (by rw [length_compL, hgg.1, htn.1]) he⟩

theorem telNext_chk : ∀ i < 128, ∀ g < 3, telNext.getD (3 * i + g) 0 < 128 ∧
    compL (telTab.getD i []) (genTab.getD g []) =
      telTab.getD (telNext.getD (3 * i + g) 0) [] := by
  intro i hi g hg
  have h := triplesAll_getD telNext_rows (i := i) (by rw [length_telPk]; exact hi)
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  interval_cases g
  · exact nextOK_spec hi (by norm_num) h0
  · exact nextOK_spec hi (by norm_num) h1
  · exact nextOK_spec hi (by norm_num) h2

@[expose] def DecXOK (j i : ℕ) : Prop := decXk j i < 28 ∧ decXa j i < 128 ∧ decXb j i < 128 ∧
    compL (compL (dTab.getD j []) (telTab.getD i [])) (genTab.getD 3 []) =
      compL (compL (telTab.getD (decXa j i) []) (dTab.getD (decXk j i) []))
        (telTab.getD (decXb j i) [])

instance (j i : ℕ) : Decidable (DecXOK j i) := by unfold DecXOK; infer_instance

@[expose] def DecYOK (j i : ℕ) : Prop := decYk j i < 28 ∧ decYa j i < 128 ∧ decYb j i < 128 ∧
    compL (compL (dTab.getD j []) (telTab.getD i [])) (genTab.getD 4 []) =
      compL (compL (telTab.getD (decYa j i) []) (dTab.getD (decYk j i) []))
        (telTab.getD (decYb j i) [])

instance (j i : ℕ) : Decidable (DecYOK j i) := by unfold DecYOK; infer_instance

private def decOK (g d k a b t : ℕ) : Bool :=
  k < 28 && a < 128 && b < 128 &&
    compCode (compCode d 24 t) 24 g ==
      compCode (compCode (digit (2 ^ 120) telBig a) 24 (digit (2 ^ 120) dBig k)) 24
        (digit (2 ^ 120) telBig b)

private theorem decX_rows : ∀ j < 28, triplesAll
    (decOK (pack 32 (genTab.getD 3 [])) (pack 32 (dTab.getD j []))) (decXTab.getD j []) telPk =
      true := by
  decide +kernel

private theorem decY_rows : ∀ j < 28, triplesAll
    (decOK (pack 32 (genTab.getD 4 [])) (pack 32 (dTab.getD j []))) (decYTab.getD j []) telPk =
      true := by
  decide +kernel

private theorem decOK_spec {g j i : ℕ} (hg : g < 5) (hj : j < 28) (hi : i < 128) {k a b : ℕ}
    (h : decOK (pack 32 (genTab.getD g [])) (pack 32 (dTab.getD j [])) k a b
      (telPk.getD i 0) = true) :
    k < 28 ∧ a < 128 ∧ b < 128 ∧
      compL (compL (dTab.getD j []) (telTab.getD i [])) (genTab.getD g []) =
        compL (compL (telTab.getD a []) (dTab.getD k [])) (telTab.getD b []) := by
  simp only [decOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, digit_telBig, digit_dBig,
    telPk_getD] at h
  obtain ⟨⟨⟨hk, ha⟩, hb⟩, he⟩ := h
  exact ⟨hk, ha, hb, compL_compL_eq (dTab_getD_fits hj).2 (telTab_getD_fits ha).2
    (telTab_getD_fits hi) (genTab_getD_fits hg) (dTab_getD_fits hk) (telTab_getD_fits hb) he⟩

private theorem decXOK_all (j : ℕ) (hj : j < 28) (i : ℕ) (hi : i < 128) : DecXOK j i :=
  decOK_spec (by norm_num) hj hi (triplesAll_getD (decX_rows j hj) (by rw [length_telPk]; exact hi))

private theorem decYOK_all (j : ℕ) (hj : j < 28) (i : ℕ) (hi : i < 128) : DecYOK j i :=
  decOK_spec (by norm_num) hj hi (triplesAll_getD (decY_rows j hj) (by rw [length_telPk]; exact hi))

theorem decX_c0 : ∀ j, 0 ≤ j → j < 2 → ∀ i < 128, DecXOK j i :=
  fun j _ hj i hi => decXOK_all j (by omega) i hi

theorem decX_c1 : ∀ j, 2 ≤ j → j < 4 → ∀ i < 128, DecXOK j i :=
  fun j _ hj i hi => decXOK_all j (by omega) i hi

theorem decX_c2 : ∀ j, 4 ≤ j → j < 6 → ∀ i < 128, DecXOK j i :=
  fun j _ hj i hi => decXOK_all j (by omega) i hi

theorem decX_c3 : ∀ j, 6 ≤ j → j < 8 → ∀ i < 128, DecXOK j i :=
  fun j _ hj i hi => decXOK_all j (by omega) i hi

theorem decX_c4 : ∀ j, 8 ≤ j → j < 10 → ∀ i < 128, DecXOK j i :=
  fun j _ hj i hi => decXOK_all j (by omega) i hi

theorem decX_c5 : ∀ j, 10 ≤ j → j < 12 → ∀ i < 128, DecXOK j i :=
  fun j _ hj i hi => decXOK_all j (by omega) i hi

theorem decX_c6 : ∀ j, 12 ≤ j → j < 14 → ∀ i < 128, DecXOK j i :=
  fun j _ hj i hi => decXOK_all j (by omega) i hi

theorem decX_c7 : ∀ j, 14 ≤ j → j < 16 → ∀ i < 128, DecXOK j i :=
  fun j _ hj i hi => decXOK_all j (by omega) i hi

theorem decX_c8 : ∀ j, 16 ≤ j → j < 18 → ∀ i < 128, DecXOK j i :=
  fun j _ hj i hi => decXOK_all j (by omega) i hi

theorem decX_c9 : ∀ j, 18 ≤ j → j < 20 → ∀ i < 128, DecXOK j i :=
  fun j _ hj i hi => decXOK_all j (by omega) i hi

theorem decX_c10 : ∀ j, 20 ≤ j → j < 22 → ∀ i < 128, DecXOK j i :=
  fun j _ hj i hi => decXOK_all j (by omega) i hi

theorem decX_c11 : ∀ j, 22 ≤ j → j < 24 → ∀ i < 128, DecXOK j i :=
  fun j _ hj i hi => decXOK_all j (by omega) i hi

theorem decX_c12 : ∀ j, 24 ≤ j → j < 26 → ∀ i < 128, DecXOK j i :=
  fun j _ hj i hi => decXOK_all j (by omega) i hi

theorem decX_c13 : ∀ j, 26 ≤ j → j < 28 → ∀ i < 128, DecXOK j i :=
  fun j _ hj i hi => decXOK_all j (by omega) i hi

theorem decX_chk (j : ℕ) (hj : j < 28) (i : ℕ) (hi : i < 128) : DecXOK j i := by
  by_cases h0 : j < 2
  · exact decX_c0 j (by omega) h0 i hi
  by_cases h1 : j < 4
  · exact decX_c1 j (by omega) h1 i hi
  by_cases h2 : j < 6
  · exact decX_c2 j (by omega) h2 i hi
  by_cases h3 : j < 8
  · exact decX_c3 j (by omega) h3 i hi
  by_cases h4 : j < 10
  · exact decX_c4 j (by omega) h4 i hi
  by_cases h5 : j < 12
  · exact decX_c5 j (by omega) h5 i hi
  by_cases h6 : j < 14
  · exact decX_c6 j (by omega) h6 i hi
  by_cases h7 : j < 16
  · exact decX_c7 j (by omega) h7 i hi
  by_cases h8 : j < 18
  · exact decX_c8 j (by omega) h8 i hi
  by_cases h9 : j < 20
  · exact decX_c9 j (by omega) h9 i hi
  by_cases h10 : j < 22
  · exact decX_c10 j (by omega) h10 i hi
  by_cases h11 : j < 24
  · exact decX_c11 j (by omega) h11 i hi
  by_cases h12 : j < 26
  · exact decX_c12 j (by omega) h12 i hi
  exact decX_c13 j (by omega) hj i hi

theorem decY_c0 : ∀ j, 0 ≤ j → j < 2 → ∀ i < 128, DecYOK j i :=
  fun j _ hj i hi => decYOK_all j (by omega) i hi

theorem decY_c1 : ∀ j, 2 ≤ j → j < 4 → ∀ i < 128, DecYOK j i :=
  fun j _ hj i hi => decYOK_all j (by omega) i hi

theorem decY_c2 : ∀ j, 4 ≤ j → j < 6 → ∀ i < 128, DecYOK j i :=
  fun j _ hj i hi => decYOK_all j (by omega) i hi

theorem decY_c3 : ∀ j, 6 ≤ j → j < 8 → ∀ i < 128, DecYOK j i :=
  fun j _ hj i hi => decYOK_all j (by omega) i hi

theorem decY_c4 : ∀ j, 8 ≤ j → j < 10 → ∀ i < 128, DecYOK j i :=
  fun j _ hj i hi => decYOK_all j (by omega) i hi

theorem decY_c5 : ∀ j, 10 ≤ j → j < 12 → ∀ i < 128, DecYOK j i :=
  fun j _ hj i hi => decYOK_all j (by omega) i hi

theorem decY_c6 : ∀ j, 12 ≤ j → j < 14 → ∀ i < 128, DecYOK j i :=
  fun j _ hj i hi => decYOK_all j (by omega) i hi

theorem decY_c7 : ∀ j, 14 ≤ j → j < 16 → ∀ i < 128, DecYOK j i :=
  fun j _ hj i hi => decYOK_all j (by omega) i hi

theorem decY_c8 : ∀ j, 16 ≤ j → j < 18 → ∀ i < 128, DecYOK j i :=
  fun j _ hj i hi => decYOK_all j (by omega) i hi

theorem decY_c9 : ∀ j, 18 ≤ j → j < 20 → ∀ i < 128, DecYOK j i :=
  fun j _ hj i hi => decYOK_all j (by omega) i hi

theorem decY_c10 : ∀ j, 20 ≤ j → j < 22 → ∀ i < 128, DecYOK j i :=
  fun j _ hj i hi => decYOK_all j (by omega) i hi

theorem decY_c11 : ∀ j, 22 ≤ j → j < 24 → ∀ i < 128, DecYOK j i :=
  fun j _ hj i hi => decYOK_all j (by omega) i hi

theorem decY_c12 : ∀ j, 24 ≤ j → j < 26 → ∀ i < 128, DecYOK j i :=
  fun j _ hj i hi => decYOK_all j (by omega) i hi

theorem decY_c13 : ∀ j, 26 ≤ j → j < 28 → ∀ i < 128, DecYOK j i :=
  fun j _ hj i hi => decYOK_all j (by omega) i hi

theorem decY_chk (j : ℕ) (hj : j < 28) (i : ℕ) (hi : i < 128) : DecYOK j i := by
  by_cases h0 : j < 2
  · exact decY_c0 j (by omega) h0 i hi
  by_cases h1 : j < 4
  · exact decY_c1 j (by omega) h1 i hi
  by_cases h2 : j < 6
  · exact decY_c2 j (by omega) h2 i hi
  by_cases h3 : j < 8
  · exact decY_c3 j (by omega) h3 i hi
  by_cases h4 : j < 10
  · exact decY_c4 j (by omega) h4 i hi
  by_cases h5 : j < 12
  · exact decY_c5 j (by omega) h5 i hi
  by_cases h6 : j < 14
  · exact decY_c6 j (by omega) h6 i hi
  by_cases h7 : j < 16
  · exact decY_c7 j (by omega) h7 i hi
  by_cases h8 : j < 18
  · exact decY_c8 j (by omega) h8 i hi
  by_cases h9 : j < 20
  · exact decY_c9 j (by omega) h9 i hi
  by_cases h10 : j < 22
  · exact decY_c10 j (by omega) h10 i hi
  by_cases h11 : j < 24
  · exact decY_c11 j (by omega) h11 i hi
  by_cases h12 : j < 26
  · exact decY_c12 j (by omega) h12 i hi
  exact decY_c13 j (by omega) hj i hi

private theorem decXA_rows : ∀ j < 2,
    triplesAll (fun k _ _ _ => k < 2) (decXTab.getD j []) telPk = true := by
  decide +kernel

theorem decXA_chk : ∀ j < 2, ∀ i < 128, decXk j i < 2 := fun j hj i hi =>
  of_decide_eq_true (triplesAll_getD (decXA_rows j hj) (i := i) (by rw [length_telPk]; exact hi))

private theorem decYB_rows :
    triplesAll (fun k _ _ _ => k == 0 || k == 2) (decYTab.getD 0 []) telPk = true ∧
      triplesAll (fun k _ _ _ => k == 0 || k == 2) (decYTab.getD 2 []) telPk = true := by
  decide +kernel

theorem decYB_chk : ∀ i < 128, (decYk 0 i = 0 ∨ decYk 0 i = 2) ∧ (decYk 2 i = 0 ∨ decYk 2 i = 2) := by
  intro i hi
  have h0 := triplesAll_getD decYB_rows.1 (i := i) (by rw [length_telPk]; exact hi)
  have h2 := triplesAll_getD decYB_rows.2 (i := i) (by rw [length_telPk]; exact hi)
  simp only [Bool.or_eq_true, beq_iff_eq] at h0 h2
  exact ⟨h0, h2⟩

theorem ox_chk : ∀ j < 25, (∀ l ∈ decode (oxCodes.getD j []), l.1 < 4) ∧
    wordL4 (j + 3) (decode (oxCodes.getD j [])) = genTab.getD 3 [] := by decide +kernel

theorem oy_chk : ∀ j < 25, (∀ l ∈ decode (oyCodes.getD j []), l.1 < 4) ∧
    wordL4 (j + 3) (decode (oyCodes.getD j [])) = genTab.getD 4 [] := by decide +kernel

theorem sepA_chk : ∀ i < 128, telTab.getD i [] ≠ dTab.getD 1 [] := by decide +kernel

theorem sepB_chk : ∀ i < 128, telTab.getD i [] ≠ dTab.getD 2 [] := by decide +kernel

@[expose] def SepABOK (i : ℕ) : Prop := ∀ i' < 128,
    compL (compL (telTab.getD i []) (dTab.getD 1 [])) (telTab.getD i' []) ≠ dTab.getD 2 []

instance (i : ℕ) : Decidable (SepABOK i) := by unfold SepABOK; infer_instance

private theorem sepAB_rows : telPk.all (fun x => telPk.all fun z =>
    differAt (compCode x 24 (pack 32 (dTab.getD 1 []))) z (pack 32 (dTab.getD 2 [])) 24) =
      true := by
  decide +kernel

private theorem sepABOK_all (i : ℕ) (hi : i < 128) : SepABOK i := by
  intro i' hi' he
  have hmem : ∀ {n : ℕ}, n < 128 → telPk.getD n 0 ∈ telPk := fun hn => by
    rw [List.getD_eq_getElem _ _ (by rw [length_telPk]; exact hn)]
    exact List.getElem_mem _
  obtain ⟨p, hp, hne⟩ :=
    differAt_spec (List.all_eq_true.1 (List.all_eq_true.1 sepAB_rows _ (hmem hi)) _ (hmem hi'))
  apply hne
  have ht := telTab_getD_fits hi
  have ht' := telTab_getD_fits hi'
  have hd1 := dTab_getD_fits (j := 1) (by norm_num)
  have hd2 := dTab_getD_fits (j := 2) (by norm_num)
  rw [telPk_getD, telPk_getD, compCode_pack ht.2 hd1.2 hd1.1, digit_pack (compL_lt ht.2 _),
    digit_pack ht'.2, digit_pack hd2.2, ← compL_getD (by rw [ht'.1]; exact hp), he]

theorem sepAB_c0 : ∀ i, 0 ≤ i → i < 8 → SepABOK i :=
  fun i _ hi => sepABOK_all i (by omega)

theorem sepAB_c1 : ∀ i, 8 ≤ i → i < 16 → SepABOK i :=
  fun i _ hi => sepABOK_all i (by omega)

theorem sepAB_c2 : ∀ i, 16 ≤ i → i < 24 → SepABOK i :=
  fun i _ hi => sepABOK_all i (by omega)

theorem sepAB_c3 : ∀ i, 24 ≤ i → i < 32 → SepABOK i :=
  fun i _ hi => sepABOK_all i (by omega)

theorem sepAB_c4 : ∀ i, 32 ≤ i → i < 40 → SepABOK i :=
  fun i _ hi => sepABOK_all i (by omega)

theorem sepAB_c5 : ∀ i, 40 ≤ i → i < 48 → SepABOK i :=
  fun i _ hi => sepABOK_all i (by omega)

theorem sepAB_c6 : ∀ i, 48 ≤ i → i < 56 → SepABOK i :=
  fun i _ hi => sepABOK_all i (by omega)

theorem sepAB_c7 : ∀ i, 56 ≤ i → i < 64 → SepABOK i :=
  fun i _ hi => sepABOK_all i (by omega)

theorem sepAB_c8 : ∀ i, 64 ≤ i → i < 72 → SepABOK i :=
  fun i _ hi => sepABOK_all i (by omega)

theorem sepAB_c9 : ∀ i, 72 ≤ i → i < 80 → SepABOK i :=
  fun i _ hi => sepABOK_all i (by omega)

theorem sepAB_c10 : ∀ i, 80 ≤ i → i < 88 → SepABOK i :=
  fun i _ hi => sepABOK_all i (by omega)

theorem sepAB_c11 : ∀ i, 88 ≤ i → i < 96 → SepABOK i :=
  fun i _ hi => sepABOK_all i (by omega)

theorem sepAB_c12 : ∀ i, 96 ≤ i → i < 104 → SepABOK i :=
  fun i _ hi => sepABOK_all i (by omega)

theorem sepAB_c13 : ∀ i, 104 ≤ i → i < 112 → SepABOK i :=
  fun i _ hi => sepABOK_all i (by omega)

theorem sepAB_c14 : ∀ i, 112 ≤ i → i < 120 → SepABOK i :=
  fun i _ hi => sepABOK_all i (by omega)

theorem sepAB_c15 : ∀ i, 120 ≤ i → i < 128 → SepABOK i :=
  fun i _ hi => sepABOK_all i (by omega)

theorem sepAB_chk (i : ℕ) (hi : i < 128) : SepABOK i := by
  by_cases h0 : i < 8
  · exact sepAB_c0 i (by omega) h0
  by_cases h1 : i < 16
  · exact sepAB_c1 i (by omega) h1
  by_cases h2 : i < 24
  · exact sepAB_c2 i (by omega) h2
  by_cases h3 : i < 32
  · exact sepAB_c3 i (by omega) h3
  by_cases h4 : i < 40
  · exact sepAB_c4 i (by omega) h4
  by_cases h5 : i < 48
  · exact sepAB_c5 i (by omega) h5
  by_cases h6 : i < 56
  · exact sepAB_c6 i (by omega) h6
  by_cases h7 : i < 64
  · exact sepAB_c7 i (by omega) h7
  by_cases h8 : i < 72
  · exact sepAB_c8 i (by omega) h8
  by_cases h9 : i < 80
  · exact sepAB_c9 i (by omega) h9
  by_cases h10 : i < 88
  · exact sepAB_c10 i (by omega) h10
  by_cases h11 : i < 96
  · exact sepAB_c11 i (by omega) h11
  by_cases h12 : i < 104
  · exact sepAB_c12 i (by omega) h12
  by_cases h13 : i < 112
  · exact sepAB_c13 i (by omega) h13
  by_cases h14 : i < 120
  · exact sepAB_c14 i (by omega) h14
  exact sepAB_c15 i (by omega) hi

theorem dCodes_one : dCodes.getD 1 [] = [6] := by decide +kernel

theorem dCodes_two : dCodes.getD 2 [] = [8] := by decide +kernel

theorem dCodes_zero : dCodes.getD 0 [] = [] := by decide +kernel

theorem telCodes_zero : telCodes.getD 0 [] = [] := by decide +kernel

section Fields

theorem tel_zero : telG 0 = 1 := by
  unfold telG telW
  rw [telCodes_zero]
  rfl

theorem d_zero : dG 0 = 1 := by
  unfold dG dW
  rw [dCodes_zero]
  rfl

theorem dG_one : dG 1 = genG 3 := by
  unfold dG dW
  rw [dCodes_one]
  simp [decode, wordProd]

theorem dG_two : dG 2 = genG 4 := by
  unfold dG dW
  rw [dCodes_two]
  simp [decode, wordProd]

theorem tel_mem (i : ℕ) (hi : i < 128) :
    telG i ∈ Subgroup.closure ({genG 0, genG 1, genG 2} : Set AutG) := by
  have e : telG i = wordProd (fun k => if k = 0 then genG 0 else if k = 1 then genG 1 else genG 2)
      (telW i) := by
    unfold telG
    refine wordProd_congr _ fun l hl => ?_
    have := telLetters i hi l hl
    have : l.1 = 0 ∨ l.1 = 1 ∨ l.1 = 2 := by omega
    rcases this with e | e | e <;> simp [e]
  rw [e]
  refine wordProd_mem (fun k => ?_) _
  by_cases h0 : k = 0
  · simp [h0]; exact Subgroup.subset_closure (by simp)
  by_cases h1 : k = 1
  · simp [h1]; exact Subgroup.subset_closure (by simp)
  · simp [h0, h1]; exact Subgroup.subset_closure (by simp)

theorem reprG_eq {l m : List ℕ} {g h : AutG} (hg : ReprG l g) (hh : ReprG m h) (e : l = m) :
    g = h := eq_of_reprG hg (e ▸ hh)

theorem tel_next (i : ℕ) (hi : i < 128) (g : ℕ) (hg : g < 3) :
    ∃ j : Fin 128, telG i * genG g = telG j := by
  obtain ⟨hlt, he⟩ := telNext_chk i hi g hg
  refine ⟨⟨telNext.getD (3 * i + g) 0, hlt⟩, ?_⟩
  exact reprG_eq (reprG_mul (reprG_tel i hi) (reprG_gen g (by omega)))
    (reprG_tel _ hlt) he

theorem dec_x (j i : ℕ) (hj : j < 28) (hi : i < 128) :
    ∃ (k : Fin 28) (i₁ i₂ : Fin 128), dG j * telG i * genG 3 = telG i₁ * dG k * telG i₂ := by
  obtain ⟨hk, h1, h2, he⟩ := decX_chk j hj i hi
  refine ⟨⟨_, hk⟩, ⟨_, h1⟩, ⟨_, h2⟩, ?_⟩
  exact reprG_eq (reprG_mul (reprG_mul (reprG_d j hj) (reprG_tel i hi)) (reprG_gen 3 (by omega)))
    (reprG_mul (reprG_mul (reprG_tel _ h1) (reprG_d _ hk)) (reprG_tel _ h2)) he

theorem dec_y (j i : ℕ) (hj : j < 28) (hi : i < 128) :
    ∃ (k : Fin 28) (i₁ i₂ : Fin 128), dG j * telG i * genG 4 = telG i₁ * dG k * telG i₂ := by
  obtain ⟨hk, h1, h2, he⟩ := decY_chk j hj i hi
  refine ⟨⟨_, hk⟩, ⟨_, h1⟩, ⟨_, h2⟩, ?_⟩
  exact reprG_eq (reprG_mul (reprG_mul (reprG_d j hj) (reprG_tel i hi)) (reprG_gen 4 (by omega)))
    (reprG_mul (reprG_mul (reprG_tel _ h1) (reprG_d _ hk)) (reprG_tel _ h2)) he

end Fields

end CFSG.Quasithin.M12AmalAut
