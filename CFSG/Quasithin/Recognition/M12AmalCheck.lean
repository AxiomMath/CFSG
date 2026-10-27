module

public import CFSG.Quasithin.Recognition.M12AmalData
public import CFSG.Quasithin.Recognition.CertPermList
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin.M12Amal

open CFSG.Sporadic.Bridge Equiv

@[expose] def mA : Perm (Fin 12) :=
  List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11]

@[expose] def mB : Perm (Fin 12) :=
  List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
    List.formPerm [5, 9, 6]

theorem quasithinM12_eq : CFSG.Open.quasithinM12 = Subgroup.closure {mA, mB} := rfl

@[expose] def mGen (i : ℕ) : Perm (Fin 12) := if i = 0 then mA else mB

@[expose] def genP (i : ℕ) : Perm (Fin 12) :=
  if i = 0 then
    List.formPerm [0, 2] * List.formPerm [1, 3] * List.formPerm [4, 9, 8, 6] *
      List.formPerm [5, 7, 10, 11]
  else if i = 1 then List.formPerm [0, 3, 1, 2] * List.formPerm [6, 11, 9, 7]
  else if i = 2 then
    List.formPerm [0, 3] * List.formPerm [1, 2] * List.formPerm [4, 8] * List.formPerm [7, 11]
  else if i = 3 then List.formPerm [1, 3, 2] * List.formPerm [4, 9, 7] * List.formPerm [6, 11, 8]
  else if i = 4 then
    List.formPerm [0, 7, 8] * List.formPerm [1, 11, 4] * List.formPerm [2, 6, 5] *
      List.formPerm [3, 9, 10]
  else 1

@[expose] def genMCodes : List (List Nat) :=
  [[2, 0, 2, 0, 3, 0, 2, 0, 2, 0, 2, 0, 2, 0, 3, 0, 2, 0, 3, 0, 3, 0, 2, 0, 3, 0, 3, 0, 2, 0],
   [3, 0, 2, 0, 3, 0, 2, 0, 2, 0, 2, 0, 2, 0, 3, 0, 3, 0, 2, 0, 2, 0, 2, 0, 3, 0],
   [0, 3, 0, 3, 0, 3, 0, 2, 0, 3, 0, 2, 0, 2, 0, 2, 0],
   [2, 0, 2, 0, 3, 0, 2, 0, 2, 0, 2, 0, 3, 0, 2, 0, 2, 0, 2, 0, 3, 0, 3, 0, 2, 0, 2],
   [2, 0, 2, 0, 2, 0, 3, 0, 2, 0, 2, 0, 3, 0, 3, 0, 2, 0, 3, 0, 3, 0, 2, 0, 3, 0, 2, 0, 3]]

@[expose] def mCodes : List (List Nat) :=
  [[0, 7, 0, 8, 7, 9, 6, 8, 7, 8], [1, 7, 8, 7, 0, 9, 7, 9, 7, 9]]

@[expose] def decode (c : List Nat) : List (Nat × Bool) :=
  c.map fun n => (n / 2, n % 2 == 0)

@[expose] def telW (i : ℕ) : List (ℕ × Bool) := decode (telCodes.getD i [])

@[expose] def dW (j : ℕ) : List (ℕ × Bool) := decode (dCodes.getD j [])

@[expose] def letterL (l : ℕ × Bool) : List ℕ :=
  if l.2 then genTab.getD l.1 [] else genInvTab.getD l.1 []

@[expose] def wordL : List (ℕ × Bool) → List ℕ
  | [] => List.range 12
  | l :: w => compL (letterL l) (wordL w)

@[expose] def letterL4 (j : ℕ) (l : ℕ × Bool) : List ℕ :=
  if l.1 < 3 then letterL l else if l.2 then dTab.getD j [] else dInvTab.getD j []

@[expose] def wordL4 (j : ℕ) : List (ℕ × Bool) → List ℕ
  | [] => List.range 12
  | l :: w => compL (letterL4 j l) (wordL4 j w)

theorem mGen_mem (i : ℕ) : mGen i ∈ CFSG.Open.quasithinM12 := by
  rw [quasithinM12_eq]
  unfold mGen
  split
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem genP_eq : ∀ k < 5, genP k = wordProd mGen (decode (genMCodes.getD k [])) := by
  decide +kernel

theorem genP_mem (k : ℕ) (hk : k < 5) : genP k ∈ CFSG.Open.quasithinM12 := by
  rw [genP_eq k hk]
  exact wordProd_mem mGen_mem _

theorem mA_eq : mA = wordProd genP (decode (mCodes.getD 0 [])) := by decide +kernel

theorem mB_eq : mB = wordProd genP (decode (mCodes.getD 1 [])) := by decide +kernel

theorem genTab_rep : ∀ k < 5, RepL (genTab.getD k []) (genP k) := by decide +kernel

theorem genInvTab_rep : ∀ k < 5, RepL (genInvTab.getD k []) (genP k)⁻¹ := by decide +kernel

theorem telLetters : ∀ i < 64, ∀ l ∈ telW i, l.1 < 3 := by decide +kernel

theorem dLetters : ∀ j < 44, ∀ l ∈ dW j, l.1 < 5 := by decide +kernel

theorem telTab_eq : ∀ i < 64, telTab.getD i [] = wordL (telW i) := by decide +kernel

theorem dTab_eq : ∀ j < 44, dTab.getD j [] = wordL (dW j) := by decide +kernel

@[expose] def invW (w : List (ℕ × Bool)) : List (ℕ × Bool) := w.reverse.map fun l => (l.1, !l.2)

theorem dInvTab_eq : ∀ j < 44, dInvTab.getD j [] = wordL (invW (dW j)) := by decide +kernel

theorem dInvLetters : ∀ j < 44, ∀ l ∈ invW (dW j), l.1 < 5 := by decide +kernel

theorem genP_orders : genP 0 ^ 4 = 1 ∧ genP 1 ^ 4 = 1 ∧ genP 2 ^ 2 = 1 ∧ genP 3 ^ 3 = 1 ∧
    genP 4 ^ 3 = 1 := by decide +kernel

@[expose] def genG (k : ℕ) : ↥CFSG.Open.quasithinM12 :=
  if h : k < 5 then ⟨genP k, genP_mem k h⟩ else 1

theorem genG_coe (k : ℕ) (hk : k < 5) :
    ((genG k : ↥CFSG.Open.quasithinM12) : Perm (Fin 12)) = genP k := by
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

abbrev ReprG (l : List ℕ) (g : ↥CFSG.Open.quasithinM12) : Prop :=
  RepL (n := 12) l (g : Perm (Fin 12))

theorem reprG_mul {l m : List ℕ} {g h : ↥CFSG.Open.quasithinM12} (hl : ReprG l g)
    (hm : ReprG m h) : ReprG (compL l m) (g * h) :=
  repL_mul hl hm

theorem eq_of_reprG {l : List ℕ} {g h : ↥CFSG.Open.quasithinM12} (hg : ReprG l g)
    (hh : ReprG l h) : g = h :=
  Subtype.ext (eq_of_repL hg hh)

theorem ne_of_reprG {l m : List ℕ} {g h : ↥CFSG.Open.quasithinM12} (hg : ReprG l g)
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

theorem reprG_one : ReprG (List.range 12) 1 := repL_one 12

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

@[expose] def telG (i : ℕ) : ↥CFSG.Open.quasithinM12 := wordProd genG (telW i)

@[expose] def dG (j : ℕ) : ↥CFSG.Open.quasithinM12 := wordProd genG (dW j)

theorem reprG_tel (i : ℕ) (hi : i < 64) : ReprG (telTab.getD i []) (telG i) := by
  rw [telTab_eq i hi]
  exact wordL_rep (telW i) (fun l hl => by have := telLetters i hi l hl; omega)

theorem reprG_d (j : ℕ) (hj : j < 44) : ReprG (dTab.getD j []) (dG j) := by
  rw [dTab_eq j hj]
  exact wordL_rep (dW j) (dLetters j hj)

theorem reprG_dInv (j : ℕ) (hj : j < 44) : ReprG (dInvTab.getD j []) (dG j)⁻¹ := by
  rw [dInvTab_eq j hj]
  have := wordL_rep (invW (dW j)) (dInvLetters j hj)
  rwa [wordProd_invW] at this

@[expose] def gen4 (d : ↥CFSG.Open.quasithinM12) (i : ℕ) : ↥CFSG.Open.quasithinM12 :=
  if i = 0 then genG 0 else if i = 1 then genG 1 else if i = 2 then genG 2 else d

theorem wordL4_rep (j : ℕ) (hj : j < 44) : ∀ w : List (ℕ × Bool), (∀ l ∈ w, l.1 < 4) →
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

@[expose] def decXk (j i : ℕ) : ℕ := (decXTab.getD j []).getD (3 * i) 0

@[expose] def decXa (j i : ℕ) : ℕ := (decXTab.getD j []).getD (3 * i + 1) 0

@[expose] def decXb (j i : ℕ) : ℕ := (decXTab.getD j []).getD (3 * i + 2) 0

@[expose] def decYk (j i : ℕ) : ℕ := (decYTab.getD j []).getD (3 * i) 0

@[expose] def decYa (j i : ℕ) : ℕ := (decYTab.getD j []).getD (3 * i + 1) 0

@[expose] def decYb (j i : ℕ) : ℕ := (decYTab.getD j []).getD (3 * i + 2) 0

theorem telNext_chk : ∀ i < 64, ∀ g < 3, telNext.getD (3 * i + g) 0 < 64 ∧
    compL (telTab.getD i []) (genTab.getD g []) =
      telTab.getD (telNext.getD (3 * i + g) 0) [] := by decide +kernel

@[expose] def DecXOK (j i : ℕ) : Prop := decXk j i < 44 ∧ decXa j i < 64 ∧ decXb j i < 64 ∧
    compL (compL (dTab.getD j []) (telTab.getD i [])) (genTab.getD 3 []) =
      compL (compL (telTab.getD (decXa j i) []) (dTab.getD (decXk j i) []))
        (telTab.getD (decXb j i) [])

instance (j i : ℕ) : Decidable (DecXOK j i) := by unfold DecXOK; infer_instance

@[expose] def DecYOK (j i : ℕ) : Prop := decYk j i < 44 ∧ decYa j i < 64 ∧ decYb j i < 64 ∧
    compL (compL (dTab.getD j []) (telTab.getD i [])) (genTab.getD 4 []) =
      compL (compL (telTab.getD (decYa j i) []) (dTab.getD (decYk j i) []))
        (telTab.getD (decYb j i) [])

instance (j i : ℕ) : Decidable (DecYOK j i) := by unfold DecYOK; infer_instance

theorem decX_c0 : ∀ j, 0 ≤ j → j < 4 → ∀ i < 64, DecXOK j i := by
  decide +kernel

theorem decX_c1 : ∀ j, 4 ≤ j → j < 8 → ∀ i < 64, DecXOK j i := by
  decide +kernel

theorem decX_c2 : ∀ j, 8 ≤ j → j < 12 → ∀ i < 64, DecXOK j i := by
  decide +kernel

theorem decX_c3 : ∀ j, 12 ≤ j → j < 16 → ∀ i < 64, DecXOK j i := by
  decide +kernel

theorem decX_c4 : ∀ j, 16 ≤ j → j < 20 → ∀ i < 64, DecXOK j i := by
  decide +kernel

theorem decX_c5 : ∀ j, 20 ≤ j → j < 24 → ∀ i < 64, DecXOK j i := by
  decide +kernel

theorem decX_c6 : ∀ j, 24 ≤ j → j < 28 → ∀ i < 64, DecXOK j i := by
  decide +kernel

theorem decX_c7 : ∀ j, 28 ≤ j → j < 32 → ∀ i < 64, DecXOK j i := by
  decide +kernel

theorem decX_c8 : ∀ j, 32 ≤ j → j < 36 → ∀ i < 64, DecXOK j i := by
  decide +kernel

theorem decX_c9 : ∀ j, 36 ≤ j → j < 40 → ∀ i < 64, DecXOK j i := by
  decide +kernel

theorem decX_c10 : ∀ j, 40 ≤ j → j < 44 → ∀ i < 64, DecXOK j i := by
  decide +kernel

theorem decY_c0 : ∀ j, 0 ≤ j → j < 4 → ∀ i < 64, DecYOK j i := by
  decide +kernel

theorem decY_c1 : ∀ j, 4 ≤ j → j < 8 → ∀ i < 64, DecYOK j i := by
  decide +kernel

theorem decY_c2 : ∀ j, 8 ≤ j → j < 12 → ∀ i < 64, DecYOK j i := by
  decide +kernel

theorem decY_c3 : ∀ j, 12 ≤ j → j < 16 → ∀ i < 64, DecYOK j i := by
  decide +kernel

theorem decY_c4 : ∀ j, 16 ≤ j → j < 20 → ∀ i < 64, DecYOK j i := by
  decide +kernel

theorem decY_c5 : ∀ j, 20 ≤ j → j < 24 → ∀ i < 64, DecYOK j i := by
  decide +kernel

theorem decY_c6 : ∀ j, 24 ≤ j → j < 28 → ∀ i < 64, DecYOK j i := by
  decide +kernel

theorem decY_c7 : ∀ j, 28 ≤ j → j < 32 → ∀ i < 64, DecYOK j i := by
  decide +kernel

theorem decY_c8 : ∀ j, 32 ≤ j → j < 36 → ∀ i < 64, DecYOK j i := by
  decide +kernel

theorem decY_c9 : ∀ j, 36 ≤ j → j < 40 → ∀ i < 64, DecYOK j i := by
  decide +kernel

theorem decY_c10 : ∀ j, 40 ≤ j → j < 44 → ∀ i < 64, DecYOK j i := by
  decide +kernel

theorem decX_chk (j : ℕ) (hj : j < 44) (i : ℕ) (hi : i < 64) : DecXOK j i := by
  by_cases h0 : j < 4
  · exact decX_c0 j (by omega) h0 i hi
  by_cases h1 : j < 8
  · exact decX_c1 j (by omega) h1 i hi
  by_cases h2 : j < 12
  · exact decX_c2 j (by omega) h2 i hi
  by_cases h3 : j < 16
  · exact decX_c3 j (by omega) h3 i hi
  by_cases h4 : j < 20
  · exact decX_c4 j (by omega) h4 i hi
  by_cases h5 : j < 24
  · exact decX_c5 j (by omega) h5 i hi
  by_cases h6 : j < 28
  · exact decX_c6 j (by omega) h6 i hi
  by_cases h7 : j < 32
  · exact decX_c7 j (by omega) h7 i hi
  by_cases h8 : j < 36
  · exact decX_c8 j (by omega) h8 i hi
  by_cases h9 : j < 40
  · exact decX_c9 j (by omega) h9 i hi
  exact decX_c10 j (by omega) hj i hi

theorem decY_chk (j : ℕ) (hj : j < 44) (i : ℕ) (hi : i < 64) : DecYOK j i := by
  by_cases h0 : j < 4
  · exact decY_c0 j (by omega) h0 i hi
  by_cases h1 : j < 8
  · exact decY_c1 j (by omega) h1 i hi
  by_cases h2 : j < 12
  · exact decY_c2 j (by omega) h2 i hi
  by_cases h3 : j < 16
  · exact decY_c3 j (by omega) h3 i hi
  by_cases h4 : j < 20
  · exact decY_c4 j (by omega) h4 i hi
  by_cases h5 : j < 24
  · exact decY_c5 j (by omega) h5 i hi
  by_cases h6 : j < 28
  · exact decY_c6 j (by omega) h6 i hi
  by_cases h7 : j < 32
  · exact decY_c7 j (by omega) h7 i hi
  by_cases h8 : j < 36
  · exact decY_c8 j (by omega) h8 i hi
  by_cases h9 : j < 40
  · exact decY_c9 j (by omega) h9 i hi
  exact decY_c10 j (by omega) hj i hi

theorem decXA_chk : ∀ j < 2, ∀ i < 64, decXk j i < 2 := by decide +kernel

theorem decYB_chk : ∀ i < 64, (decYk 0 i = 0 ∨ decYk 0 i = 2) ∧ (decYk 2 i = 0 ∨ decYk 2 i = 2) := by
  decide +kernel

theorem ox_chk : ∀ j < 41, (∀ l ∈ decode (oxCodes.getD j []), l.1 < 4) ∧
    wordL4 (j + 3) (decode (oxCodes.getD j [])) = genTab.getD 3 [] := by decide +kernel

theorem oy_chk : ∀ j < 41, (∀ l ∈ decode (oyCodes.getD j []), l.1 < 4) ∧
    wordL4 (j + 3) (decode (oyCodes.getD j [])) = genTab.getD 4 [] := by decide +kernel

theorem sepA_chk : ∀ i < 64, telTab.getD i [] ≠ dTab.getD 1 [] := by decide +kernel

theorem sepB_chk : ∀ i < 64, telTab.getD i [] ≠ dTab.getD 2 [] := by decide +kernel

@[expose] def SepABOK (i : ℕ) : Prop := ∀ i' < 64,
    compL (compL (telTab.getD i []) (dTab.getD 1 [])) (telTab.getD i' []) ≠ dTab.getD 2 []

instance (i : ℕ) : Decidable (SepABOK i) := by unfold SepABOK; infer_instance

theorem sepAB_c0 : ∀ i, 0 ≤ i → i < 8 → SepABOK i := by
  decide +kernel

theorem sepAB_c1 : ∀ i, 8 ≤ i → i < 16 → SepABOK i := by
  decide +kernel

theorem sepAB_c2 : ∀ i, 16 ≤ i → i < 24 → SepABOK i := by
  decide +kernel

theorem sepAB_c3 : ∀ i, 24 ≤ i → i < 32 → SepABOK i := by
  decide +kernel

theorem sepAB_c4 : ∀ i, 32 ≤ i → i < 40 → SepABOK i := by
  decide +kernel

theorem sepAB_c5 : ∀ i, 40 ≤ i → i < 48 → SepABOK i := by
  decide +kernel

theorem sepAB_c6 : ∀ i, 48 ≤ i → i < 56 → SepABOK i := by
  decide +kernel

theorem sepAB_c7 : ∀ i, 56 ≤ i → i < 64 → SepABOK i := by
  decide +kernel

theorem sepAB_chk (i : ℕ) (hi : i < 64) : SepABOK i := by
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
  exact sepAB_c7 i (by omega) hi

theorem dCodes_one : dCodes.getD 1 [] = [6] := by decide +kernel

theorem dCodes_two : dCodes.getD 2 [] = [8] := by decide +kernel

theorem dCodes_zero : dCodes.getD 0 [] = [] := by decide +kernel

theorem telCodes_zero : telCodes.getD 0 [] = [] := by decide +kernel

abbrev M12G : Type := ↥CFSG.Open.quasithinM12

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

theorem tel_mem (i : ℕ) (hi : i < 64) :
    telG i ∈ Subgroup.closure ({genG 0, genG 1, genG 2} : Set M12G) := by
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

theorem reprG_eq {l m : List ℕ} {g h : M12G} (hg : ReprG l g) (hh : ReprG m h) (e : l = m) :
    g = h := eq_of_reprG hg (e ▸ hh)

theorem tel_next (i : ℕ) (hi : i < 64) (g : ℕ) (hg : g < 3) :
    ∃ j : Fin 64, telG i * genG g = telG j := by
  obtain ⟨hlt, he⟩ := telNext_chk i hi g hg
  refine ⟨⟨telNext.getD (3 * i + g) 0, hlt⟩, ?_⟩
  exact reprG_eq (reprG_mul (reprG_tel i hi) (reprG_gen g (by omega)))
    (reprG_tel _ hlt) he

theorem dec_x (j i : ℕ) (hj : j < 44) (hi : i < 64) :
    ∃ (k : Fin 44) (i₁ i₂ : Fin 64), dG j * telG i * genG 3 = telG i₁ * dG k * telG i₂ := by
  obtain ⟨hk, h1, h2, he⟩ := decX_chk j hj i hi
  refine ⟨⟨_, hk⟩, ⟨_, h1⟩, ⟨_, h2⟩, ?_⟩
  exact reprG_eq (reprG_mul (reprG_mul (reprG_d j hj) (reprG_tel i hi)) (reprG_gen 3 (by omega)))
    (reprG_mul (reprG_mul (reprG_tel _ h1) (reprG_d _ hk)) (reprG_tel _ h2)) he

theorem dec_y (j i : ℕ) (hj : j < 44) (hi : i < 64) :
    ∃ (k : Fin 44) (i₁ i₂ : Fin 64), dG j * telG i * genG 4 = telG i₁ * dG k * telG i₂ := by
  obtain ⟨hk, h1, h2, he⟩ := decY_chk j hj i hi
  refine ⟨⟨_, hk⟩, ⟨_, h1⟩, ⟨_, h2⟩, ?_⟩
  exact reprG_eq (reprG_mul (reprG_mul (reprG_d j hj) (reprG_tel i hi)) (reprG_gen 4 (by omega)))
    (reprG_mul (reprG_mul (reprG_tel _ h1) (reprG_d _ hk)) (reprG_tel _ h2)) he

end Fields

end CFSG.Quasithin.M12Amal
