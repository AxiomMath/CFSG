module

public import Certificates.Kernel.A8Part.Checks
public import CFSG.Certificates.Kernel.A8Part.Reduce
public import CFSG.Quasithin.Vol2.KGFactA8Inputs
public import CFSG.Certificates.Kernel.CosetLat.Sound
public import CFSG.Certificates.Kernel.Misc.PermClosWSound

public section

namespace CertificateChecks.KernelA8Part.Glue

open Equiv CFSG.KC.CosetLat CFSG.KC.Misc.ClosW CFSG.KC.A8Part CertificateChecks.KernelA8Part
open CFSG.Quasithin.H13.KGA8 (mGens sGens)
open CFSG.KC.Misc.Clos (ClosEnc clos_card treeAt sortAt closedAt letB_eq allN_iff andB_eq_true
  allR_iff forall_of_chunks)

@[expose] def cl (L : List (Perm (Fin 8))) : Subgroup (Perm (Fin 8)) := Subgroup.closure {g | g ∈ L}

theorem henc : ClosEnc (wcode (n := 8) 4) m8 one8 := wcode_enc (by norm_num) (by norm_num)

noncomputable def dec (c : ℕ) : Perm (Fin 8) :=
  if h : ∃ σ : Perm (Fin 8), wcode 4 σ = c then h.choose else 1

theorem dec_code {c : ℕ} (h : ∃ σ : Perm (Fin 8), wcode 4 σ = c) : wcode 4 (dec c) = c := by
  rw [dec, dif_pos h]
  exact h.choose_spec

theorem dec_code' {K : Subgroup (Perm (Fin 8))} {c : ℕ} (h : ∃ σ ∈ K, wcode 4 σ = c) :
    wcode 4 (dec c) = c := by
  obtain ⟨σ, -, hσ⟩ := h
  exact dec_code ⟨σ, hσ⟩

theorem mem_of_code {K : Subgroup (Perm (Fin 8))} {σ : Perm (Fin 8)}
    (h : ∃ g ∈ K, wcode 4 g = wcode 4 σ) : σ ∈ K := by
  obtain ⟨g, hg, he⟩ := h
  rwa [henc.inj he] at hg

noncomputable def decL (G : ℕ → ℕ) (n : ℕ) : List (Perm (Fin 8)) :=
  (List.range n).map fun l => dec (G l)

theorem decL_length (G : ℕ → ℕ) (n : ℕ) : (decL G n).length = n := by
  simp [decL]

theorem decL_getD {G : ℕ → ℕ} {n : ℕ} (h : ∀ l < n, ∃ σ : Perm (Fin 8), wcode 4 σ = G l) :
    ∀ l < (decL G n).length, G l = wcode 4 ((decL G n).getD l 1) := by
  intro l hl
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
  rw [decL_length] at hl
  simp only [decL, List.getElem_map, List.getElem_range]
  exact (dec_code (h l hl)).symm

theorem in_cl {L : List (Perm (Fin 8))} {A : ℕ → ℕ}
    (hA : ∀ a < L.length, A a = wcode 4 (L.getD a 1)) :
    ∀ a < L.length, ∃ g ∈ cl L, wcode 4 g = A a :=
  fun a ha => ⟨_, getD_mem_closure L ha, (hA a ha).symm⟩

theorem cl_le {L : List (Perm (Fin 8))} {K : Subgroup (Perm (Fin 8))} {G : ℕ → ℕ}
    (hG : ∀ k < L.length, G k = wcode 4 (L.getD k 1))
    (h : ∀ k < L.length, ∃ g ∈ K, wcode 4 g = G k) : cl L ≤ K := by
  rw [cl, Subgroup.closure_le]
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
  have e : L.getD k 1 = L[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  rw [← e]
  obtain ⟨g, hg, hge⟩ := h k hk
  exact mem_of_code ⟨g, hg, hge.trans (hG k hk)⟩

theorem wordG_in {K : Subgroup (Perm (Fin 8))} {A : ℕ → ℕ} {nA : ℕ}
    (hA : ∀ a < nA, ∃ g ∈ K, wcode 4 g = A a) {w : List ℕ} (hw : lettersG nA w = true) :
    ∃ g ∈ K, wcode 4 g = wordG m8 one8 A w := by
  induction w with
  | nil => exact ⟨1, K.one_mem, henc.enc_one⟩
  | cons l w ih =>
    have hw' : CFSG.KC.Ord.andB (Nat.blt l nA) (lettersG nA w) = true := hw
    obtain ⟨hl, hw''⟩ := andB_eq_true hw'
    obtain ⟨g, hg, hge⟩ := ih hw''
    obtain ⟨a, ha, hae⟩ := hA l (Nat.blt_eq.mp hl)
    refine ⟨a * g, K.mul_mem ha hg, ?_⟩
    change wcode 4 (a * g) = m8 (A l) (wordG m8 one8 A w)
    rw [henc.enc_mul, hae, hge]

theorem word_in {K : Subgroup (Perm (Fin 8))} {A : ℕ → ℕ} {nA : ℕ}
    (hA : ∀ a < nA, ∃ g ∈ K, wcode 4 g = A a) {w : List ℕ} {c : ℕ}
    (h : wordAt m8 one8 A nA w c = true) : ∃ g ∈ K, wcode 4 g = c := by
  obtain ⟨h1, h2⟩ := andB_eq_true h
  obtain ⟨g, hg, hge⟩ := wordG_in hA h1
  exact ⟨g, hg, hge.trans (Nat.eq_of_beq_eq_true h2)⟩

theorem words_in {K : Subgroup (Perm (Fin 8))} {A : ℕ → ℕ} {nA : ℕ}
    (hA : ∀ a < nA, ∃ g ∈ K, wcode 4 g = A a) {ws : List (List ℕ)} {o n : ℕ} {G : ℕ → ℕ}
    (h : wordsAt A nA ws o G n = true) : ∀ k < n, ∃ g ∈ K, wcode 4 g = G k :=
  fun k hk => word_in hA ((allN_iff _ _).1 h k hk)

theorem tree_in {K : Subgroup (Perm (Fin 8))} {G : ℕ → ℕ} {nG N : ℕ} {E PA : ℕ → ℕ}
    (hG : ∀ l < nG, ∃ g ∈ K, wcode 4 g = G l)
    (ht : ∀ k < N, treeAt m8 one8 G nG E PA k = true) : ∀ k < N, ∃ g ∈ K, wcode 4 g = E k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    cases k with
    | zero => exact ⟨1, K.one_mem, by rw [henc.enc_one, Nat.eq_of_beq_eq_true (ht 0 hk)]⟩
    | succ k =>
      have h : CFSG.KC.LQT.P.letB (PA (k + 1)) (fun r => CFSG.KC.LQT.P.letB (Nat.land r 16777215)
          fun p => CFSG.KC.LQT.P.letB (Nat.shiftRight r 24) fun l =>
            CFSG.KC.Ord.andB (Nat.blt p (k + 1)) (CFSG.KC.Ord.andB (Nat.blt l nG)
              (Nat.beq (E (k + 1)) (m8 (E p) (G l))))) = true := ht (k + 1) hk
      rw [letB_eq, letB_eq, letB_eq] at h
      obtain ⟨hp, h⟩ := andB_eq_true h
      obtain ⟨hl, h⟩ := andB_eq_true h
      have hp' := Nat.blt_eq.mp hp
      obtain ⟨g, hg, hge⟩ := ih _ hp' (by omega)
      obtain ⟨a, ha, hae⟩ := hG _ (Nat.blt_eq.mp hl)
      refine ⟨g * a, K.mul_mem hg ha, ?_⟩
      rw [henc.enc_mul, hge, hae]
      exact (Nat.eq_of_beq_eq_true h).symm

theorem getW_eq (l : List (List ℕ)) : ∀ i, getW l i = l.getD i [] := by
  induction l with
  | nil => intro i; rfl
  | cons x xs ih =>
    intro i
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem getWW_eq (l : List (List (List ℕ))) : ∀ i, getWW l i = l.getD i [] := by
  induction l with
  | nil => intro i; rfl
  | cons x xs ih =>
    intro i
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem lenW_eq (l : List (List ℕ)) : lenW l = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => exact congrArg Nat.succ ih

theorem lenWW_eq (l : List (List (List ℕ))) : lenWW l = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => exact congrArg Nat.succ ih

theorem allIx_get {l : List (List (List ℕ))} {f : ℕ → List (List ℕ) → Bool} :
    ∀ {i₀ : ℕ}, allIx l f i₀ = true → ∀ i < l.length, f (i₀ + i) (l.getD i []) = true := by
  induction l with
  | nil => intro _ _ i hi; exact absurd hi (Nat.not_lt_zero _)
  | cons x xs ih =>
    intro i₀ h i hi
    obtain ⟨h1, h2⟩ := andB_eq_true h
    cases i with
    | zero => exact h1
    | succ i =>
      have := ih h2 i (by simpa using hi)
      rw [show i₀ + (i + 1) = Nat.succ i₀ + i by omega]
      exact this

theorem allIx_mem {l : List (List (List ℕ))} {f : List (List ℕ) → Bool} :
    ∀ {i₀ : ℕ}, allIx l (fun _ e => f e) i₀ = true → ∀ e ∈ l, f e = true := by
  induction l with
  | nil => intro _ _ e he; exact absurd he List.not_mem_nil
  | cons x xs ih =>
    intro i₀ h e he
    obtain ⟨h1, h2⟩ := andB_eq_true h
    rcases List.mem_cons.1 he with rfl | he
    · exact h1
    · exact ih h2 e he

theorem exists_of_notB_allIx {l : List (List (List ℕ))} {P : List (List ℕ) → Bool} :
    ∀ {i₀ : ℕ}, CFSG.KC.Ord.notB (allIx l (fun _ e => CFSG.KC.Ord.notB (P e)) i₀) = true →
      ∃ e ∈ l, P e = true := by
  induction l with
  | nil => intro _ h; exact absurd h Bool.false_ne_true
  | cons x xs ih =>
    intro i₀ h
    cases hx : P x
    · have h' : CFSG.KC.Ord.notB (allIx xs (fun _ e => CFSG.KC.Ord.notB (P e)) (Nat.succ i₀)) =
          true := by
        have e : allIx (x :: xs) (fun _ e => CFSG.KC.Ord.notB (P e)) i₀ =
            CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (P x))
              (allIx xs (fun _ e => CFSG.KC.Ord.notB (P e)) (Nat.succ i₀)) := rfl
        rw [e, hx] at h
        exact h
      obtain ⟨e, he, hPe⟩ := ih h'
      exact ⟨e, List.mem_cons_of_mem _ he, hPe⟩
    · exact ⟨x, List.mem_cons_self, hx⟩

theorem bridgeM : ∀ j < 6, MG j = wcode 4 (mGens.getD j 1) := by
  decide +kernel

theorem bridgeS : ∀ k < 3, SG k = wcode 4 (sGens.getD k 1) := by
  decide +kernel

theorem hMG : ∀ j < mGens.length, MG j = wcode 4 (mGens.getD j 1) := bridgeM

theorem hSG : ∀ k < sGens.length, SG k = wcode 4 (sGens.getD k 1) := bridgeS

@[expose] def S0 : Subgroup (Perm (Fin 8)) := cl sGens

@[expose] def AM : Subgroup (Perm (Fin 8)) := cl mGens

theorem hMGin : ∀ j < 6, ∃ g ∈ AM, wcode 4 g = MG j := in_cl hMG

theorem hSGin : ∀ k < 3, ∃ g ∈ S0, wcode 4 g = SG k := in_cl hSG

theorem tAt {k : ℕ} (hk : k < 64) : CFSG.KC.Ord.andB (treeAt m8 one8 SG 3 TE TP k)
    (CFSG.KC.Ord.andB (sortAt 64 TE TS k) (closedAt m8 SG 3 64 TE TC k)) = true :=
  (allN_iff _ _).1 ch7154t k hk

theorem S0_clos : (∀ k < 64, ∃ g ∈ S0, wcode 4 g = TE k) ∧ Nat.card S0 = 64 ∧
    ∀ g ∈ S0, ∃ k < 64, wcode 4 g = TE k := by
  obtain ⟨h1, -, h3⟩ := clos_card henc sGens (G := SG) (N := 64) (E := TE) (PA := TP) (SG := TS)
    hSG (by norm_num) (fun k hk => (andB_eq_true (tAt hk)).1)
    (fun k hk => (andB_eq_true (andB_eq_true (tAt hk)).2).1)
  obtain ⟨h4, h5⟩ := h3 (CT := TC) (fun k hk => (andB_eq_true (andB_eq_true (tAt hk)).2).2)
  exact ⟨h1, h4, h5⟩

theorem hTE : ∀ k < 64, ∃ g ∈ S0, wcode 4 g = TE k := S0_clos.1

theorem hTEx : ∀ g ∈ S0, ∃ k < 64, wcode 4 g = TE k := S0_clos.2.2

theorem card_S0 : Nat.card S0 = 64 := S0_clos.2.1

theorem rep_ex : ∀ a < 24, ∃ g ∈ AM, wcode 4 g = RC a := by
  have h : wordsAt MG 6 repM 0 RC 24 = true := ch7154repM
  exact words_in hMGin h

noncomputable def ρ (a : ℕ) : Perm (Fin 8) := dec (RC a)

theorem ρ_code : ∀ a < 24, wcode 4 (ρ a) = RC a := fun a ha => dec_code' (rep_ex a ha)

theorem hUE0 : Nat.beq (UE 0) one8 = true := (andB_eq_true ch7154u).1

theorem hTrans : ∀ i < 315, transAt m8 RC 24 TE 64 UE UR i = true :=
  fun i hi => (allN_iff _ _).1 (andB_eq_true ch7154u).2 i hi

theorem hU : ∀ i < 315, ∃ u : Perm (Fin 8), wcode 4 u = UE i := fun i hi => by
  obtain ⟨a, -, e, -, he⟩ := trans_sound henc ρ_code hTE hTrans i hi
  exact ⟨_, he⟩

theorem hCM : ∀ i < 315, ctabAt m8 MG 6 TE 64 UE 315 CR i = true := by
  have h := forall_of_chunks 105 3 (ctabAt m8 MG 6 TE 64 UE 315 CR) (fun c hc => by
    interval_cases c
    · exact ch7154m0
    · exact ch7154m1
    · exact ch7154m2)
  exact fun i hi => h i (by omega)

theorem cover : ∀ σ ∈ AM, ∃ a < 24, ∃ π ∈ S0, ∃ κ ∈ S0, σ = π * ρ a * κ :=
  ctab_cover henc mGens hMG ρ_code hTE hTrans (by norm_num) hUE0 hCM

theorem card_AM_le : Nat.card AM ≤ 20160 := by
  have h := ctab_card henc mGens hMG hTE hU (by norm_num) hUE0 hCM
  rw [card_S0] at h
  exact h

theorem lenL_ge : ∀ t < 8, 3 ≤ lenL t := by
  decide +kernel

theorem lenL_0 : lenL 0 = 3 := by
  decide +kernel

theorem lenL_7 : lenL 7 = 9 := by
  decide +kernel

theorem reps_cover : ∀ t < 8, ∃ j < 24, hd (getW (repW.getD j []) 0) = t := by
  decide +kernel

theorem repAt_of {j : ℕ} (hj : j < 24) : repAt j (repW.getD j []) = true := by
  have hl : repW.length = 24 := by
    rw [← lenWW_eq]
    exact Nat.eq_of_beq_eq_true (andB_eq_true ch7154rep).1
  have h := allIx_get (andB_eq_true ch7154rep).2 j (by rw [hl]; exact hj)
  rwa [Nat.zero_add] at h

theorem hTR {j : ℕ} (hj : j < 24) :
    ∀ a < (sGens ++ [ρ j]).length, TR j a = wcode 4 ((sGens ++ [ρ j]).getD a 1) := by
  intro a ha
  have ha4 : a < 4 := ha
  interval_cases a
  · exact bridgeS 0 (by decide)
  · exact bridgeS 1 (by decide)
  · exact bridgeS 2 (by decide)
  · exact (ρ_code j hj).symm

theorem ex_LG : ∀ t < 8, ∀ k < lenL t, ∃ σ : Perm (Fin 8), wcode 4 σ = LG t k := by
  intro t ht k hk
  obtain ⟨j, hj, hjt⟩ := reps_cover t ht
  have h := repAt_of hj
  unfold repAt at h
  rw [letB_eq] at h
  obtain ⟨-, h⟩ := andB_eq_true h
  obtain ⟨-, hw⟩ := andB_eq_true h
  rw [hjt] at hw
  obtain ⟨g, -, hg⟩ := words_in (K := cl (sGens ++ [ρ j])) (in_cl (hTR hj)) hw k hk
  exact ⟨g, hg⟩

noncomputable def Lgens (t : ℕ) : List (Perm (Fin 8)) := decL (LG t) (lenL t)

noncomputable def Lm (t : ℕ) : Subgroup (Perm (Fin 8)) := cl (Lgens t)

theorem Lgens_length (t : ℕ) : (Lgens t).length = lenL t := decL_length _ _

theorem hGL {t : ℕ} (ht : t < 8) : ∀ k < (Lgens t).length, LG t k = wcode 4 ((Lgens t).getD k 1) :=
  decL_getD (ex_LG t ht)

theorem hLin {t : ℕ} (ht : t < 8) : ∀ k < lenL t, ∃ g ∈ Lm t, wcode 4 g = LG t k := by
  intro k hk
  exact in_cl (hGL ht) k (by rw [Lgens_length]; exact hk)

theorem LG_lt {t k : ℕ} (hk : k < 3) : LG t k = SG k := by
  unfold LG
  rw [Nat.blt_eq.mpr hk]

theorem S0_le {t : ℕ} (ht : t < 8) : S0 ≤ Lm t := by
  refine cl_le hSG fun k hk => ?_
  have hk3 : k < 3 := hk
  rw [← LG_lt hk3]
  exact hLin ht k (by have := lenL_ge t ht; omega)

theorem Lm0 : Lm 0 = S0 := by
  refine le_antisymm (cl_le (hGL (by norm_num)) fun k hk => ?_) (S0_le (by norm_num))
  rw [Lgens_length, lenL_0] at hk
  rw [LG_lt hk]
  exact hSGin k hk

theorem top_eq : AM = Lm 7 := by
  obtain ⟨h1, h2⟩ := andB_eq_true ch7154top
  have hL7 : ∀ k < 9, ∃ g ∈ Lm 7, wcode 4 g = LG 7 k := by
    rw [← lenL_7]
    exact hLin (by norm_num)
  refine le_antisymm (cl_le hMG (words_in hL7 h1)) (cl_le (hGL (by norm_num)) fun k hk => ?_)
  rw [Lgens_length, lenL_7] at hk
  exact words_in hMGin h2 k hk

theorem mem_le {t n o r₀ : ℕ} (ht : t < 8) (hn : 0 < n) (h : memOK t n o r₀ = true) :
    Nat.card (Lm t) ≤ 64 * n := by
  unfold memOK at h
  rw [← Lgens_length] at h
  obtain ⟨h0, h⟩ := andB_eq_true h
  obtain ⟨hb, hc⟩ := andB_eq_true h
  have hb' := (allN_iff _ _).1 hb
  have hU' : ∀ i < n, ∃ u : Perm (Fin 8), wcode 4 u = UE (MJ (Nat.add o i)) :=
    fun i hi => hU _ (Nat.blt_eq.mp (hb' i hi))
  have h1 : Nat.beq (UE (MJ (Nat.add o 0))) one8 = true := by
    rw [show Nat.add o 0 = o from rfl, Nat.eq_of_beq_eq_true h0]
    exact hUE0
  have hle := ctab_card henc (Lgens t) (hGL ht) hTE hU' hn h1 ((allN_iff _ _).1 hc)
  rw [card_S0] at hle
  exact hle

theorem dvd_of_sub {t N nK oE oC oK : ℕ} (ht : t < 8) (hN : 0 < N)
    (h : subOK t N nK oE oC oK = true) : N ∣ Nat.card (Lm t) := by
  unfold subOK at h
  obtain ⟨hw, hl⟩ := andB_eq_true h
  have hK := words_in (hLin ht) hw
  have hl' := (allN_iff _ _).1 hl
  exact dvd_card_of_clos henc hK hN (fun k hk => (andB_eq_true (hl' k hk)).1)
    (fun k hk => (andB_eq_true (andB_eq_true (hl' k hk)).2).1)
    (fun k hk => (andB_eq_true (andB_eq_true (hl' k hk)).2).2)

theorem dvd64 {t : ℕ} (ht : t < 8) : 64 ∣ Nat.card (Lm t) := by
  rw [← card_S0]
  exact Subgroup.card_dvd_of_le (S0_le ht)

theorem cop {a b c : ℕ} (h : Nat.Coprime a b) (ha : a ∣ c) (hb : b ∣ c) : a * b ∣ c :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd h ha hb

theorem card_AM : Nat.card AM = 20160 := by
  have h9 := dvd_of_sub (by norm_num) (by norm_num) ch7154s7a
  have h5 := dvd_of_sub (by norm_num) (by norm_num) ch7154s7b
  have h7 := dvd_of_sub (by norm_num) (by norm_num) ch7154s7c
  have hd := cop (by norm_num) (cop (by norm_num) (cop (by norm_num) (dvd64 (t := 7) (by norm_num))
    h9) h5) h7
  rw [← top_eq] at hd
  exact card_eq_of_dvd_of_le hd card_AM_le

theorem AM_le_alt : AM ≤ alternatingGroup (Fin 8) := by
  have h : ∀ j < 6, Perm.sign (mGens.getD j 1) = 1 := by
    decide +kernel
  rw [AM, cl, Subgroup.closure_le]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
  have e : mGens.getD j 1 = mGens[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup, ← e]
  exact h j hj

theorem hAeq : AM = alternatingGroup (Fin 8) :=
  Subgroup.eq_of_le_of_card_ge AM_le_alt (by rw [card_alt8, card_AM])

theorem S0_le_alt : S0 ≤ alternatingGroup (Fin 8) := by
  rw [← hAeq, top_eq]
  exact S0_le (by norm_num)

theorem card_of {t a : ℕ} (ht : t < 8) (hc : Nat.Coprime 64 a) (hle : Nat.card (Lm t) ≤ 64 * a)
    (ha : a ∣ Nat.card (Lm t)) : Nat.card (Lm t) = 64 * a :=
  card_eq_of_dvd_of_le (cop hc (dvd64 ht) ha) hle

theorem card_of2 {t n a b : ℕ} (ht : t < 8) (hab : 64 * a * b = 64 * n) (h1 : Nat.Coprime 64 a)
    (h2 : Nat.Coprime (64 * a) b) (hle : Nat.card (Lm t) ≤ 64 * n) (ha : a ∣ Nat.card (Lm t))
    (hb : b ∣ Nat.card (Lm t)) : Nat.card (Lm t) = 64 * n := by
  have hd := cop h2 (cop h1 (dvd64 ht) ha) hb
  rw [hab] at hd
  exact card_eq_of_dvd_of_le hd hle

theorem card_Lm : ∀ t < 8, Nat.card (Lm t) = 64 ∨ Nat.card (Lm t) = 192 ∨
    Nat.card (Lm t) = 576 ∨ Nat.card (Lm t) = 1344 ∨ Nat.card (Lm t) = 20160 := by
  intro t ht
  interval_cases t
  · rw [Lm0, card_S0]
    norm_num
  · rw [card_of (a := 3) (by norm_num) (by norm_num) (mem_le (by norm_num) (by norm_num) ch7154L1)
      (dvd_of_sub (by norm_num) (by norm_num) ch7154s1)]
    norm_num
  · rw [card_of (a := 3) (by norm_num) (by norm_num) (mem_le (by norm_num) (by norm_num) ch7154L2)
      (dvd_of_sub (by norm_num) (by norm_num) ch7154s2)]
    norm_num
  · rw [card_of (a := 3) (by norm_num) (by norm_num) (mem_le (by norm_num) (by norm_num) ch7154L3)
      (dvd_of_sub (by norm_num) (by norm_num) ch7154s3)]
    norm_num
  · rw [card_of (a := 9) (by norm_num) (by norm_num) (mem_le (by norm_num) (by norm_num) ch7154L4)
      (dvd_of_sub (by norm_num) (by norm_num) ch7154s4)]
    norm_num
  · rw [card_of2 (a := 3) (b := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (mem_le (by norm_num) (by norm_num) ch7154L5)
      (dvd_of_sub (by norm_num) (by norm_num) ch7154s5a)
      (dvd_of_sub (by norm_num) (by norm_num) ch7154s5b)]
    norm_num
  · rw [card_of2 (a := 3) (b := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (mem_le (by norm_num) (by norm_num) ch7154L6)
      (dvd_of_sub (by norm_num) (by norm_num) ch7154s6a)
      (dvd_of_sub (by norm_num) (by norm_num) ch7154s6b)]
    norm_num
  · rw [← top_eq, card_AM]
    norm_num

theorem rep_join : ∀ j < 24, ∃ t < 8, S0 ⊔ Subgroup.closure {ρ j} = Lm t := by
  intro j hj
  have h := repAt_of hj
  unfold repAt at h
  rw [letB_eq] at h
  obtain ⟨ht, h⟩ := andB_eq_true h
  obtain ⟨hr, hw⟩ := andB_eq_true h
  set t := hd (getW (repW.getD j []) 0)
  have ht' : t < 8 := Nat.blt_eq.mp ht
  refine ⟨t, ht', ?_⟩
  have hsup : S0 ⊔ Subgroup.closure {ρ j} = cl (sGens ++ [ρ j]) := by
    rw [S0, cl, cl, ← Subgroup.closure_union]
    congr 1
    ext x
    simp [or_comm]
  rw [hsup]
  refine le_antisymm ?_ (cl_le (hGL ht') fun k hk => ?_)
  · rw [← hsup]
    refine sup_le (S0_le ht') ?_
    rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_singleton_iff.1 hx]
    obtain ⟨g, hg, hge⟩ := word_in (hLin ht') hr
    exact mem_of_code ⟨g, hg, hge.trans (ρ_code j hj).symm⟩
  · rw [Lgens_length] at hk
    exact words_in (in_cl (hTR hj)) hw k hk

theorem getD_append_codes {a b : ℕ} (ha : a < 8) (hb : b < 8) :
    ∀ l < (Lgens a ++ Lgens b).length, LGG a b l = wcode 4 ((Lgens a ++ Lgens b).getD l 1) := by
  intro l hl
  unfold LGG
  by_cases h : l < lenL a
  · rw [Nat.blt_eq.mpr h]
    have h' : l < (Lgens a).length := by rw [Lgens_length]; exact h
    rw [List.getD_append _ _ _ _ h']
    exact hGL ha l h'
  · have hf : Nat.blt l (lenL a) = false := by
      cases e : Nat.blt l (lenL a)
      · rfl
      · exact absurd (Nat.blt_eq.mp e) h
    rw [hf]
    have h' : (Lgens a).length ≤ l := by rw [Lgens_length]; omega
    rw [List.getD_append_right _ _ _ _ h', Lgens_length]
    rw [List.length_append, Lgens_length, Lgens_length] at hl
    exact hGL hb (l - lenL a) (by rw [Lgens_length]; omega)

theorem join_eq : ∀ a < 8, ∀ b < 8, ∃ c < 8, Lm a ⊔ Lm b = Lm c := by
  intro a ha b hb
  obtain ⟨hall, hcov⟩ := andB_eq_true ch7154join
  have hc := (allN_iff _ _).1 ((allN_iff _ _).1 hcov a ha) b hb
  obtain ⟨e, he, hP⟩ := exists_of_notB_allIx hc
  obtain ⟨hea, heb⟩ := andB_eq_true hP
  have hea' := Nat.eq_of_beq_eq_true hea
  have heb' := Nat.eq_of_beq_eq_true heb
  have h := allIx_mem hall e he
  unfold joinAt at h
  rw [letB_eq, letB_eq, letB_eq, hea', heb'] at h
  obtain ⟨-, h⟩ := andB_eq_true h
  obtain ⟨-, h⟩ := andB_eq_true h
  obtain ⟨hc', h⟩ := andB_eq_true h
  obtain ⟨hw1, h⟩ := andB_eq_true h
  obtain ⟨hw2, hw3⟩ := andB_eq_true h
  set c := nth (getW e 0) 2
  have hc8 : c < 8 := Nat.blt_eq.mp hc'
  refine ⟨c, hc8, le_antisymm ?_ ?_⟩
  · refine sup_le (cl_le (hGL ha) fun k hk => ?_) (cl_le (hGL hb) fun k hk => ?_)
    · rw [Lgens_length] at hk
      exact words_in (hLin hc8) hw2 k hk
    · rw [Lgens_length] at hk
      exact words_in (hLin hc8) hw3 k hk
  · have hlen : (Lgens a ++ Lgens b).length = Nat.add (lenL a) (lenL b) := by
      rw [List.length_append, Lgens_length, Lgens_length]
      rfl
    have hsup : Lm a ⊔ Lm b = cl (Lgens a ++ Lgens b) := by
      rw [Lm, Lm, cl, cl, cl, ← Subgroup.closure_union]
      congr 1
      ext x
      simp
    rw [hsup]
    refine cl_le (hGL hc8) fun k hk => ?_
    rw [Lgens_length] at hk
    have hA := in_cl (getD_append_codes ha hb)
    rw [hlen] at hA
    exact words_in hA hw1 k hk

theorem overgroups : ∀ Y : Subgroup (Perm (Fin 8)), S0 ≤ Y → Y ≤ AM → ∃ t < 8, Y = Lm t := by
  intro Y h1 h2
  obtain ⟨i, hi, he⟩ := lat_overgroups_of (B := S0) (Mt := AM) (Q := Lm) (nM := 8) (nR := 24)
    (ρ := ρ) (i₀ := 0) (by norm_num) Lm0 (fun i hi => S0_le hi) cover rep_join join_eq Y h1 h2
  exact ⟨i, hi, he.symm⟩

theorem two : ∀ J : Subgroup (Perm (Fin 8)), J ≤ alternatingGroup (Fin 8) → 64 ∣ Nat.card J →
    Nat.card J = 64 ∨ Nat.card J = 192 ∨ Nat.card J = 576 ∨ Nat.card J = 1344 ∨
      Nat.card J = 20160 :=
  two_of_overgroups alt8_fact2 S0_le_alt card_S0 fun K h1 h2 => by
    obtain ⟨t, ht, rfl⟩ := overgroups K h1 (h2.trans hAeq.ge)
    exact card_Lm t ht

end CertificateChecks.KernelA8Part.Glue

end
