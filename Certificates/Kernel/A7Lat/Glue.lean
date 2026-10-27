module

public import Certificates.Kernel.A7Lat.Checks
public import CFSG.Certificates.Kernel.CosetLat.Sound
public import CFSG.Certificates.Kernel.Misc.PermClosWSound
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5Even7In

public section

namespace CertificateChecks.KernelA7Lat.Glue

open Equiv CFSG.Quasithin.H13.Even7 CFSG.KC.CosetLat CFSG.KC.Misc.ClosW CertificateChecks.KernelA7Lat
open CFSG.KC.Misc.Clos (ClosEnc clos_card treeAt sortAt closedAt letB_eq allN_iff andB_eq_true
  allR_iff forall_of_chunks)

@[expose] def cl (L : List (Perm (Fin 7))) : Subgroup (Perm (Fin 7)) := Subgroup.closure {g | g ∈ L}

@[expose] def Lgens (t : ℕ) : List (Perm (Fin 7)) := (tGens :: lat).getD t []

@[expose] def Lm (t : ℕ) : Subgroup (Perm (Fin 7)) := cl (Lgens t)

theorem henc : ClosEnc (wcode (n := 7) 4) m7 one7 := wcode_enc (by norm_num) (by norm_num)

theorem bridgeL : ∀ t < 12, (Lgens t).length = lenL t ∧
    ∀ j < lenL t, LG t j = wcode 4 ((Lgens t).getD j 1) := by
  decide +kernel

theorem bridgeM : ∀ j < 2, MG j = wcode 4 (mGens.getD j 1) := by
  decide +kernel

theorem hGL {t : ℕ} (ht : t < 12) : ∀ j < (Lgens t).length, LG t j = wcode 4 ((Lgens t).getD j 1) :=
  fun j hj => (bridgeL t ht).2 j (by rw [← (bridgeL t ht).1]; exact hj)

theorem hGT : ∀ j < tGens.length, EL j = wcode 4 (tGens.getD j 1) := fun j hj => by
  have h := hGL (t := 0) (by norm_num) j hj
  have hj2 : j < 2 := hj
  interval_cases j <;> exact h

theorem getD_mem_cl (L : List (Perm (Fin 7))) {j : ℕ} (hj : j < L.length) : L.getD j 1 ∈ cl L :=
  getD_mem_closure L hj

theorem of_wordAt (gens : List (Perm (Fin 7))) {A : ℕ → ℕ}
    (hA : ∀ a < gens.length, A a = wcode 4 (gens.getD a 1)) {w : List ℕ} {c : ℕ}
    (h : wordAt m7 one7 A gens.length w c = true) : ∃ g ∈ cl gens, wcode 4 g = c := by
  obtain ⟨h1, h2⟩ := andB_eq_true h
  obtain ⟨g, hg, hge⟩ := wordG_mem henc gens hA h1
  exact ⟨g, hg, hge.trans (Nat.eq_of_beq_eq_true h2)⟩

theorem of_wordsAt (gens : List (Perm (Fin 7))) {A : ℕ → ℕ}
    (hA : ∀ a < gens.length, A a = wcode 4 (gens.getD a 1)) {ws : List (List ℕ)} {o n : ℕ}
    {G : ℕ → ℕ} (h : wordsAt A gens.length ws o G n = true) :
    ∀ k < n, ∃ g ∈ cl gens, wcode 4 g = G k :=
  fun k hk => of_wordAt gens hA ((allN_iff _ _).1 h k hk)

theorem mem_of_code {X : List (Perm (Fin 7))} {x : Perm (Fin 7)}
    (h : ∃ g ∈ cl X, wcode 4 g = wcode 4 x) : x ∈ cl X := by
  obtain ⟨g, hg, he⟩ := h
  rwa [henc.inj he] at hg

theorem cl_le_of_codes {L X : List (Perm (Fin 7))} {G : ℕ → ℕ}
    (hG : ∀ k < L.length, G k = wcode 4 (L.getD k 1))
    (h : ∀ k < L.length, ∃ g ∈ cl X, wcode 4 g = G k) : cl L ≤ cl X := by
  rw [cl, Subgroup.closure_le]
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
  have e : L.getD k 1 = L[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  rw [← e]
  obtain ⟨g, hg, hge⟩ := h k hk
  exact mem_of_code ⟨g, hg, hge.trans (hG k hk)⟩

theorem cl_append (L L' : List (Perm (Fin 7))) : cl (L ++ L') = cl L ⊔ cl L' := by
  rw [cl, cl, cl, ← Subgroup.closure_union]
  congr 1
  ext x
  simp

theorem tTree : ∀ k < 8, treeAt m7 one7 EL tGens.length TE TP k = true :=
  fun k hk => (andB_eq_true ((allN_iff _ _).1 ch7250t k hk)).1

theorem hT : ∀ k < 8, ∃ g ∈ cl tGens, wcode 4 g = TE k :=
  (clos_card henc tGens (G := EL) (N := 8) (E := TE) (PA := TP) (SG := TS) hGT (by norm_num) tTree
    (fun k hk => (andB_eq_true (andB_eq_true ((allN_iff _ _).1 ch7250t k hk)).2).1)).1

theorem card_T : Nat.card (cl tGens) = 8 :=
  ((clos_card henc tGens (G := EL) (N := 8) (E := TE) (PA := TP) (SG := TS) hGT (by norm_num)
    tTree (fun k hk => (andB_eq_true (andB_eq_true ((allN_iff _ _).1 ch7250t k hk)).2).1)).2.2
    (CT := TC)
    (fun k hk => (andB_eq_true (andB_eq_true ((allN_iff _ _).1 ch7250t k hk)).2).2)).1

theorem rep_ex : ∀ a < 49, ∃ g ∈ cl mGens, wcode 4 g = RC a := by
  have h : wordsAt MG mGens.length repM 0 RC 49 = true := ch7250repM
  exact of_wordsAt mGens bridgeM h

noncomputable def ρ (a : ℕ) : Perm (Fin 7) := if h : a < 49 then (rep_ex a h).choose else 1

theorem ρ_code : ∀ a < 49, wcode 4 (ρ a) = RC a := fun a ha => by
  rw [ρ, dif_pos ha]
  exact (rep_ex a ha).choose_spec.2

theorem hUE0 : Nat.beq (UE 0) one7 = true := (andB_eq_true ch7250u).1

theorem hTrans : ∀ i < 315, transAt m7 RC 49 TE 8 UE UR i = true :=
  fun i hi => (allN_iff _ _).1 (andB_eq_true ch7250u).2 i hi

theorem hU : ∀ i < 315, ∃ u : Perm (Fin 7), wcode 4 u = UE i := fun i hi => by
  obtain ⟨a, -, e, -, he⟩ := trans_sound henc ρ_code hT hTrans i hi
  exact ⟨_, he⟩

theorem hCM : ∀ i < 315, ctabAt m7 MG 2 TE 8 UE 315 CR i = true := by
  have h := forall_of_chunks 105 3 (ctabAt m7 MG 2 TE 8 UE 315 CR) (fun c hc => by
    interval_cases c
    · exact ch7250m0
    · exact ch7250m1
    · exact ch7250m2)
  exact fun i hi => h i (by omega)

theorem hMG : ∀ j < mGens.length, MG j = wcode 4 (mGens.getD j 1) := bridgeM

theorem T_le {t : ℕ} (ht : t < 12) : cl tGens ≤ Lm t := by
  refine cl_le_of_codes hGT fun k hk => ?_
  have hk2 : k < 2 := hk
  have hl : 2 ≤ (Lgens t).length := by
    rw [(bridgeL t ht).1]
    unfold lenL
    cases Nat.beq t 0 <;> cases Nat.beq t 6 <;> decide
  refine ⟨_, getD_mem_cl (Lgens t) (j := k) (by omega), ?_⟩
  rw [← hGL ht k (by omega)]
  interval_cases k <;> rfl

theorem card_M_le : Nat.card (cl mGens) ≤ 2520 := by
  have h := ctab_card henc mGens hMG hT hU (by norm_num) hUE0 hCM
  rw [card_T] at h
  exact h

theorem top_eq : cl mGens = Lm 11 := by
  obtain ⟨h1, h2⟩ := andB_eq_true ch7250top
  refine le_antisymm (cl_le_of_codes hMG (of_wordsAt (Lgens 11) (hGL (by norm_num)) h1))
    (cl_le_of_codes (hGL (by norm_num)) (of_wordsAt mGens hMG h2))

theorem mem_le {t n o r₀ : ℕ} (ht : t < 12) (hn : 0 < n) (h : memOK t n o r₀ = true) :
    Nat.card (Lm t) ≤ 8 * n := by
  unfold memOK at h
  rw [← (bridgeL t ht).1] at h
  obtain ⟨h0, h⟩ := andB_eq_true h
  obtain ⟨hb, hc⟩ := andB_eq_true h
  have hb' := (allN_iff _ _).1 hb
  have hU' : ∀ i < n, ∃ u : Perm (Fin 7), wcode 4 u = UE (MJ (Nat.add o i)) :=
    fun i hi => hU _ (Nat.blt_eq.mp (hb' i hi))
  have h1 : Nat.beq (UE (MJ (Nat.add o 0))) one7 = true := by
    rw [show Nat.add o 0 = o from rfl, Nat.eq_of_beq_eq_true h0]
    exact hUE0
  have hle := ctab_card henc (Lgens t) (hGL ht) hT hU' hn h1 ((allN_iff _ _).1 hc)
  rw [card_T] at hle
  exact hle

theorem dvd_of_sub {t N nK oE oC oK : ℕ} (ht : t < 12) (hN : 0 < N)
    (h : subOK t N nK oE oC oK = true) : N ∣ Nat.card (Lm t) := by
  unfold subOK at h
  rw [← (bridgeL t ht).1] at h
  obtain ⟨hw, hl⟩ := andB_eq_true h
  have hK := of_wordsAt (Lgens t) (hGL ht) hw
  have hl' := (allN_iff _ _).1 hl
  exact dvd_card_of_clos henc hK hN (fun k hk => (andB_eq_true (hl' k hk)).1)
    (fun k hk => (andB_eq_true (andB_eq_true (hl' k hk)).2).1)
    (fun k hk => (andB_eq_true (andB_eq_true (hl' k hk)).2).2)

theorem eight_dvd {t : ℕ} (ht : t < 12) : 8 ∣ Nat.card (Lm t) := by
  rw [← card_T]
  exact Subgroup.card_dvd_of_le (T_le ht)

theorem card_eq {t n : ℕ} (ht : t < 12) (hle : Nat.card (Lm t) ≤ 8 * n) (hd : 8 * n ∣ Nat.card (Lm t)) :
    Nat.card (Lm t) = 8 * n :=
  card_eq_of_dvd_of_le hd hle

theorem cop {a b c : ℕ} (h : Nat.Coprime a b) (ha : a ∣ c) (hb : b ∣ c) : a * b ∣ c :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd h ha hb

theorem card_eq2 {t n a b : ℕ} (ht : t < 12) (hab : 8 * a * b = 8 * n) (h1 : Nat.Coprime 8 a)
    (h2 : Nat.Coprime (8 * a) b) (hle : Nat.card (Lm t) ≤ 8 * n) (ha : a ∣ Nat.card (Lm t))
    (hb : b ∣ Nat.card (Lm t)) : Nat.card (Lm t) = 8 * n := by
  have hd := cop h2 (cop h1 (eight_dvd ht) ha) hb
  rw [hab] at hd
  exact card_eq_of_dvd_of_le hd hle

theorem card_mGens : Nat.card (cl mGens) = 2520 := by
  have h8 := eight_dvd (t := 11) (by norm_num)
  have h9 := dvd_of_sub (by norm_num) (by norm_num) ch7250s11a
  have h5 := dvd_of_sub (by norm_num) (by norm_num) ch7250s11b
  have h7 := dvd_of_sub (by norm_num) (by norm_num) ch7250s11c
  have hd := cop (by norm_num) (cop (by norm_num) (cop (by norm_num) h8 h9) h5) h7
  rw [← top_eq] at hd
  exact card_eq_of_dvd_of_le hd card_M_le

theorem card_Lm : ∀ t < 12, Nat.card (Lm t) = sizes.getD t 0 := by
  intro t ht
  interval_cases t
  · exact card_T
  · exact card_eq (n := 3) (by norm_num) (mem_le (by norm_num) (by norm_num) ch7250L1)
      (cop (by norm_num) (eight_dvd (by norm_num)) (dvd_of_sub (by norm_num) (by norm_num) ch7250s1))
  · exact card_eq (n := 3) (by norm_num) (mem_le (by norm_num) (by norm_num) ch7250L2)
      (cop (by norm_num) (eight_dvd (by norm_num)) (dvd_of_sub (by norm_num) (by norm_num) ch7250s2))
  · exact card_eq (n := 3) (by norm_num) (mem_le (by norm_num) (by norm_num) ch7250L3)
      (cop (by norm_num) (eight_dvd (by norm_num)) (dvd_of_sub (by norm_num) (by norm_num) ch7250s3))
  · exact card_eq (n := 3) (by norm_num) (mem_le (by norm_num) (by norm_num) ch7250L4)
      (cop (by norm_num) (eight_dvd (by norm_num)) (dvd_of_sub (by norm_num) (by norm_num) ch7250s4))
  · exact card_eq (n := 3) (by norm_num) (mem_le (by norm_num) (by norm_num) ch7250L5)
      (cop (by norm_num) (eight_dvd (by norm_num)) (dvd_of_sub (by norm_num) (by norm_num) ch7250s5))
  · exact card_eq (n := 9) (by norm_num) (mem_le (by norm_num) (by norm_num) ch7250L6)
      (cop (by norm_num) (eight_dvd (by norm_num)) (dvd_of_sub (by norm_num) (by norm_num) ch7250s6))
  · exact card_eq2 (a := 3) (b := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (mem_le (by norm_num) (by norm_num) ch7250L7)
      (dvd_of_sub (by norm_num) (by norm_num) ch7250s7a)
      (dvd_of_sub (by norm_num) (by norm_num) ch7250s7b)
  · exact card_eq2 (a := 3) (b := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (mem_le (by norm_num) (by norm_num) ch7250L8)
      (dvd_of_sub (by norm_num) (by norm_num) ch7250s8a)
      (dvd_of_sub (by norm_num) (by norm_num) ch7250s8b)
  · exact card_eq2 (a := 3) (b := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (mem_le (by norm_num) (by norm_num) ch7250L9)
      (dvd_of_sub (by norm_num) (by norm_num) ch7250s9a)
      (dvd_of_sub (by norm_num) (by norm_num) ch7250s9b)
  · exact card_eq2 (a := 9) (b := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (mem_le (by norm_num) (by norm_num) ch7250L10)
      (dvd_of_sub (by norm_num) (by norm_num) ch7250s10a)
      (dvd_of_sub (by norm_num) (by norm_num) ch7250s10b)
  · rw [← top_eq]
    exact card_mGens

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

theorem cover : ∀ σ ∈ cl mGens, ∃ a < 49, ∃ π ∈ cl tGens, ∃ κ ∈ cl tGens, σ = π * ρ a * κ :=
  ctab_cover henc mGens hMG ρ_code hT hTrans (by norm_num) hUE0 hCM

theorem rep_join : ∀ j < 49, ∃ t < 12, cl tGens ⊔ Subgroup.closure {ρ j} = Lm t := by
  intro j hj
  obtain ⟨-, h⟩ := andB_eq_true ch7250rep
  have hl : repW.length = 49 := Nat.eq_of_beq_eq_true (andB_eq_true ch7250rep).1
  have h := allIx_get h j (by rw [hl]; exact hj)
  rw [Nat.zero_add] at h
  unfold repAt at h
  rw [letB_eq] at h
  obtain ⟨ht, h⟩ := andB_eq_true h
  obtain ⟨hr, hw⟩ := andB_eq_true h
  set t := hd (getW (repW.getD j []) 0)
  have ht' : t < 12 := Nat.blt_eq.mp ht
  rw [← (bridgeL t ht').1] at hr hw
  refine ⟨t, ht', ?_⟩
  have hsup : cl tGens ⊔ Subgroup.closure {ρ j} = cl (tGens ++ [ρ j]) := by
    rw [cl_append]
    congr 1
    rw [cl]
    congr 1
    ext x
    simp
  rw [hsup]
  have hA : ∀ a < (tGens ++ [ρ j]).length, TR j a = wcode 4 ((tGens ++ [ρ j]).getD a 1) := by
    intro a ha
    have ha3 : a < 3 := ha
    interval_cases a
    · exact hGT 0 (by decide)
    · exact hGT 1 (by decide)
    · exact (ρ_code j hj).symm
  refine le_antisymm ?_ (cl_le_of_codes (hGL ht') (of_wordsAt (tGens ++ [ρ j]) hA hw))
  rw [cl_append]
  refine sup_le (T_le ht') ?_
  rw [cl, Subgroup.closure_le]
  intro x hx
  have hx' : x = ρ j := by simpa using hx
  rw [hx']
  exact mem_of_code ((of_wordAt (Lgens t) (hGL ht') hr).imp fun g hg => ⟨hg.1, hg.2.trans
    (ρ_code j hj).symm⟩)

theorem getD_append_codes {a b : ℕ} (ha : a < 12) (hb : b < 12) :
    ∀ l < (Lgens a ++ Lgens b).length, LGG a b l = wcode 4 ((Lgens a ++ Lgens b).getD l 1) := by
  intro l hl
  unfold LGG
  by_cases h : l < lenL a
  · rw [Nat.blt_eq.mpr h]
    have h' : l < (Lgens a).length := by rw [(bridgeL a ha).1]; exact h
    rw [List.getD_append _ _ _ _ h']
    exact hGL ha l h'
  · have hf : Nat.blt l (lenL a) = false := by
      cases e : Nat.blt l (lenL a)
      · rfl
      · exact absurd (Nat.blt_eq.mp e) h
    rw [hf]
    have h' : (Lgens a).length ≤ l := by rw [(bridgeL a ha).1]; omega
    rw [List.getD_append_right _ _ _ _ h', (bridgeL a ha).1]
    rw [List.length_append, (bridgeL a ha).1] at hl
    exact hGL hb (l - lenL a) (by omega)

theorem join_eq : ∀ a < 12, ∀ b < 12, ∃ c < 12, Lm a ⊔ Lm b = Lm c := by
  intro a ha b hb
  obtain ⟨hall, hcov⟩ := andB_eq_true ch7250join
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
  have hc12 : c < 12 := Nat.blt_eq.mp hc'
  have hlen : (Lgens a ++ Lgens b).length = Nat.add (lenL a) (lenL b) := by
    rw [List.length_append, (bridgeL a ha).1, (bridgeL b hb).1]
    rfl
  rw [← hlen, ← (bridgeL c hc12).1] at hw1
  rw [← (bridgeL c hc12).1] at hw2 hw3
  rw [← (bridgeL a ha).1] at hw2
  rw [← (bridgeL b hb).1] at hw3
  refine ⟨c, hc12, le_antisymm ?_ ?_⟩
  · exact sup_le (cl_le_of_codes (hGL ha) (of_wordsAt (Lgens c) (hGL hc12) hw2))
      (cl_le_of_codes (hGL hb) (of_wordsAt (Lgens c) (hGL hc12) hw3))
  · unfold Lm
    rw [← cl_append]
    exact cl_le_of_codes (hGL hc12) (of_wordsAt _ (getD_append_codes ha hb) hw1)

theorem overgroups : ∀ Y : Subgroup (Perm (Fin 7)), cl tGens ≤ Y → Y ≤ cl mGens →
    ∃ j < 12, Y = Lm j := by
  intro Y h1 h2
  obtain ⟨i, hi, he⟩ := lat_overgroups_of (B := cl tGens) (Mt := cl mGens) (Q := Lm) (nM := 12)
    (nR := 49) (ρ := ρ) (i₀ := 0) (by norm_num) rfl (fun i hi => T_le hi) cover rep_join join_eq
    Y h1 h2
  exact ⟨i, hi, he.symm⟩

end CertificateChecks.KernelA7Lat.Glue

end
