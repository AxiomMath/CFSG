module

public import CFSG.Quasithin.H13.A5Orth

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin.H13.A5.Orth

@[expose] def enc (v : V4) : ℕ := (v 0).val + 2 * (v 1).val + 4 * (v 2).val + 8 * (v 3).val

@[expose] def dec (n : ℕ) : V4 := ![((n % 2 : ℕ) : ZMod 2), ((n / 2 % 2 : ℕ) : ZMod 2),
  ((n / 4 % 2 : ℕ) : ZMod 2), ((n / 8 % 2 : ℕ) : ZMod 2)]

theorem dec_enc : ∀ v : V4, dec (enc v) = v := by
  decide +kernel

theorem enc_dec : ∀ n < 16, enc (dec n) = n := by
  decide +kernel

theorem enc_lt : ∀ v : V4, enc v < 16 := by
  decide +kernel

theorem enc_add : ∀ u v : V4, enc (u + v) = enc u ^^^ enc v := by
  decide +kernel

theorem enc_smul : ∀ (s : ZMod 2) (u : V4), enc (s • u) = if s = 1 then enc u else 0 := by
  decide +kernel

theorem testBit_enc : ∀ v : V4, ((enc v).testBit 0 = decide (v 0 = 1)) ∧
    ((enc v).testBit 1 = decide (v 1 = 1)) ∧ ((enc v).testBit 2 = decide (v 2 = 1)) ∧
      ((enc v).testBit 3 = decide (v 3 = 1)) := by
  decide +kernel

@[expose] def appN (c0 c1 c2 c3 n : ℕ) : ℕ :=
  (if n.testBit 0 then c0 else 0) ^^^ (if n.testBit 1 then c1 else 0) ^^^
    (if n.testBit 2 then c2 else 0) ^^^ (if n.testBit 3 then c3 else 0)

theorem enc_app (M : Fin 4 → V4) (v : V4) :
    enc (app M v) = appN (enc (M 0)) (enc (M 1)) (enc (M 2)) (enc (M 3)) (enc v) := by
  obtain ⟨h0, h1, h2, h3⟩ := testBit_enc v
  unfold app appN
  rw [enc_add, enc_add, enc_add, enc_smul, enc_smul, enc_smul, enc_smul, h0, h1, h2, h3]
  simp only [decide_eq_true_eq]

@[expose] def Wm (x y : ZMod 2) : Fin 4 → V4 := ![idc 1, idc 0, ![x, y, 0, 1], idc 2]

@[expose] def Um (ε x y : ZMod 2) : Fin 4 → V4 :=
  ![idc 0, idc 0 + idc 1, ![ε, 0, 1, 0], ![x, y, 1, 1]]

@[expose] def Msig (p q r : V4) : Fin 4 → V4 := ![idc 0, p, q, r]

@[expose] def GuardS (M : Fin 4 → V4) : Prop :=
  M 0 = idc 0 ∧ M 1 3 = 0 ∧ M 2 3 = 0 ∧ M 3 3 = 1 ∧ (∀ c, app M (app M (app M c)) = c) ∧
    ¬((M 1 = idc 1 ∨ M 1 = idc 0 + idc 1) ∧ (M 2 = idc 2 ∨ M 2 = idc 0 + idc 2))

@[expose] def tabN (c0 c1 c2 c3 : ℕ) : List ℕ := (List.range 16).map (appN c0 c1 c2 c3)

@[expose] def tabV (M : Fin 4 → V4) : List ℕ :=
  tabN (enc (M 0)) (enc (M 1)) (enc (M 2)) (enc (M 3))

@[expose] def imgM (t : List ℕ) (S : ℕ) : ℕ :=
  (List.range 16).foldl (fun acc n => if S.testBit n then acc ||| (1 <<< t.getD n 0) else acc) 0

@[expose] def stepM (ts : List (List ℕ)) (S : ℕ) : ℕ :=
  ts.foldl (fun acc t => acc ||| imgM t S) S

@[expose] def reachM (ts : List (List ℕ)) (n : ℕ) : ℕ := (stepM ts)^[n] 2

@[expose] def tabW (x y : ℕ) : List ℕ := tabN 2 1 (x + 2 * y + 8) 4

@[expose] def tabU (ε x y : ℕ) : List ℕ := tabN 1 3 (ε + 4) (x + 2 * y + 12)

@[expose] def tabS (p q r : ℕ) : List ℕ := tabN 1 p q r

@[expose] def GuardN (p q r : ℕ) : Prop :=
  p.testBit 3 = false ∧ q.testBit 3 = false ∧ r.testBit 3 = true ∧
    (∀ n < 16, appN 1 p q r (appN 1 p q r (appN 1 p q r n)) = n) ∧
    ¬((p = 2 ∨ p = 3) ∧ (q = 4 ∨ q = 5))

instance (p q r : ℕ) : Decidable (GuardN p q r) :=
  inferInstanceAs (Decidable (p.testBit 3 = false ∧ q.testBit 3 = false ∧ r.testBit 3 = true ∧
    (∀ n < 16, appN 1 p q r (appN 1 p q r (appN 1 p q r n)) = n) ∧
    ¬((p = 2 ∨ p = 3) ∧ (q = 4 ∨ q = 5))))

@[expose] def ReachFor (x y ε x' y' p q r : ℕ) : Prop :=
  ∀ n < 16, n ≠ 0 → (reachM [tabW x y, tabU ε x' y', tabS p q r] 7).testBit n = true

instance (x y ε x' y' p q r : ℕ) : Decidable (ReachFor x y ε x' y' p q r) :=
  inferInstanceAs (Decidable (∀ n < 16, n ≠ 0 →
    (reachM [tabW x y, tabU ε x' y', tabS p q r] 7).testBit n = true))

@[expose] def ReachN (p q r : ℕ) : Prop :=
  ∀ x < 2, ∀ y < 2, ∀ ε < 2, ∀ x' < 2, ∀ y' < 2, ReachFor x y ε x' y' p q r

instance (p q r : ℕ) : Decidable (ReachN p q r) :=
  inferInstanceAs (Decidable (∀ x < 2, ∀ y < 2, ∀ ε < 2, ∀ x' < 2, ∀ y' < 2,
    ReachFor x y ε x' y' p q r))

@[expose] def GuardReach (p q r : ℕ) : Prop := GuardN p q r → ReachN p q r

instance (p q r : ℕ) : Decidable (GuardReach p q r) :=
  inferInstanceAs (Decidable (GuardN p q r → ReachN p q r))

theorem reach_all_N : ∀ p < 16, ∀ q < 16, ∀ r < 16, GuardReach p q r := by
  decide +kernel

theorem testBit_one_shiftLeft (j k : ℕ) : ((1 : ℕ) <<< j).testBit k = true ↔ k = j := by
  rw [Nat.testBit_shiftLeft]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have := Nat.testBit_one_eq_true_iff_self_eq_zero.mp h2
    omega
  · rintro rfl
    simp only [ge_iff_le, le_refl, Nat.sub_self, true_and]
    exact Nat.testBit_one_eq_true_iff_self_eq_zero.mpr rfl

theorem testBit_two (k : ℕ) : (2 : ℕ).testBit k = true ↔ k = 1 := by
  have h : (2 : ℕ) = 1 <<< 1 := by decide
  rw [h]
  exact testBit_one_shiftLeft 1 k

theorem tabN_getD (c0 c1 c2 c3 n : ℕ) (hn : n < 16) :
    (tabN c0 c1 c2 c3).getD n 0 = appN c0 c1 c2 c3 n := by
  unfold tabN
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hn]
  simp

theorem tabV_getD (M : Fin 4 → V4) (n : ℕ) (hn : n < 16) :
    (tabV M).getD n 0 = enc (app M (dec n)) := by
  unfold tabV
  rw [tabN_getD _ _ _ _ _ hn, enc_app, enc_dec n hn]

theorem imgM_inv (O : Set V4) (t : List ℕ) (S : ℕ)
    (ht : ∀ n < 16, S.testBit n = true → (t.getD n 0 < 16 ∧ dec (t.getD n 0) ∈ O)) :
    ∀ k, (imgM t S).testBit k = true → k < 16 ∧ dec k ∈ O := by
  unfold imgM
  have key : ∀ (l : List ℕ) (acc : ℕ), (∀ k, acc.testBit k = true → k < 16 ∧ dec k ∈ O) →
      (∀ n ∈ l, S.testBit n = true → (t.getD n 0 < 16 ∧ dec (t.getD n 0) ∈ O)) →
      ∀ k, (l.foldl (fun acc n => if S.testBit n then acc ||| (1 <<< t.getD n 0) else acc)
        acc).testBit k = true → k < 16 ∧ dec k ∈ O := by
    intro l
    induction l with
    | nil => intro acc hacc _ k hk; exact hacc k hk
    | cons n l ih =>
      intro acc hacc hl
      simp only [List.foldl_cons]
      apply ih
      · intro k hk
        by_cases hS : S.testBit n = true
        · simp only [hS, ↓reduceIte, Nat.testBit_or, Bool.or_eq_true] at hk
          rcases hk with hk | hk
          · exact hacc k hk
          · have hkj := (testBit_one_shiftLeft _ _).1 hk
            subst hkj
            exact hl n List.mem_cons_self hS
        · simp only [hS] at hk
          exact hacc k hk
      · intro m hm
        exact hl m (List.mem_cons_of_mem _ hm)
  exact key (List.range 16) 0 (by intro k hk; simp at hk)
    (fun n hn => ht n (List.mem_range.mp hn))

theorem stepM_inv (O : Set V4) (ts : List (List ℕ)) (S : ℕ)
    (hS : ∀ k, S.testBit k = true → k < 16 ∧ dec k ∈ O)
    (ht : ∀ t ∈ ts, ∀ n < 16, S.testBit n = true → (t.getD n 0 < 16 ∧ dec (t.getD n 0) ∈ O)) :
    ∀ k, (stepM ts S).testBit k = true → k < 16 ∧ dec k ∈ O := by
  unfold stepM
  have key : ∀ (l : List (List ℕ)) (acc : ℕ), (∀ k, acc.testBit k = true → k < 16 ∧ dec k ∈ O) →
      (∀ t ∈ l, ∀ n < 16, S.testBit n = true → (t.getD n 0 < 16 ∧ dec (t.getD n 0) ∈ O)) →
      ∀ k, (l.foldl (fun acc t => acc ||| imgM t S) acc).testBit k = true →
        k < 16 ∧ dec k ∈ O := by
    intro l
    induction l with
    | nil => intro acc hacc _ k hk; exact hacc k hk
    | cons t l ih =>
      intro acc hacc hl
      simp only [List.foldl_cons]
      apply ih
      · intro k hk
        rw [Nat.testBit_or, Bool.or_eq_true] at hk
        rcases hk with hk | hk
        · exact hacc k hk
        · exact imgM_inv O t S (hl t List.mem_cons_self) k hk
      · intro t' ht'
        exact hl t' (List.mem_cons_of_mem _ ht')
  exact key ts S hS ht

theorem reachM_inv (gens : List (Fin 4 → V4)) (O : Set V4) (h0 : idc 0 ∈ O)
    (hO : ∀ M ∈ gens, ∀ c ∈ O, app M c ∈ O) (n : ℕ) :
    ∀ k, (reachM (gens.map tabV) n).testBit k = true → k < 16 ∧ dec k ∈ O := by
  have hdec1 : dec 1 = idc 0 := by decide +kernel
  induction n with
  | zero =>
    intro k hk
    have : k = 1 := (testBit_two k).1 hk
    subst this
    exact ⟨by norm_num, by rw [hdec1]; exact h0⟩
  | succ n ih =>
    intro k hk
    simp only [reachM, Function.iterate_succ_apply'] at hk
    refine stepM_inv O (gens.map tabV) _ ih ?_ k hk
    intro t ht m hm hmS
    obtain ⟨M, hM, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hm16, hmO⟩ := ih m hmS
    rw [tabV_getD M m hm]
    exact ⟨enc_lt _, by rw [dec_enc]; exact hO M hM _ hmO⟩

theorem enc_Wm : ∀ x y : ZMod 2, enc (Wm x y 0) = 2 ∧ enc (Wm x y 1) = 1 ∧
    enc (Wm x y 2) = x.val + 2 * y.val + 8 ∧ enc (Wm x y 3) = 4 := by
  decide +kernel

theorem enc_Um : ∀ ε x y : ZMod 2, enc (Um ε x y 0) = 1 ∧ enc (Um ε x y 1) = 3 ∧
    enc (Um ε x y 2) = ε.val + 4 ∧ enc (Um ε x y 3) = x.val + 2 * y.val + 12 := by
  decide +kernel

theorem enc_idc0 : enc (idc 0) = 1 := by decide +kernel

theorem tabV_Wm (x y : ZMod 2) : tabV (Wm x y) = tabW x.val y.val := by
  obtain ⟨h0, h1, h2, h3⟩ := enc_Wm x y
  unfold tabV tabW
  rw [h0, h1, h2, h3]

theorem tabV_Um (ε x y : ZMod 2) : tabV (Um ε x y) = tabU ε.val x.val y.val := by
  obtain ⟨h0, h1, h2, h3⟩ := enc_Um ε x y
  unfold tabV tabU
  rw [h0, h1, h2, h3]

theorem tabV_Msig (p q r : V4) : tabV (Msig p q r) = tabS (enc p) (enc q) (enc r) := by
  unfold tabV tabS
  have : enc (Msig p q r 0) = 1 := enc_idc0
  rw [this]
  rfl

theorem dec_special : dec 0 = 0 ∧ dec 2 = idc 1 ∧ dec 3 = idc 0 + idc 1 ∧ dec 4 = idc 2 ∧
    dec 5 = idc 0 + idc 2 := by
  decide +kernel

theorem guardN_of (p q r : V4) (h : GuardS (Msig p q r)) : GuardN (enc p) (enc q) (enc r) := by
  obtain ⟨-, h1, h2, h3, hc, hn⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [(testBit_enc p).2.2.2]
    have : p 3 = 0 := h1
    simp [this]
  · rw [(testBit_enc q).2.2.2]
    have : q 3 = 0 := h2
    simp [this]
  · rw [(testBit_enc r).2.2.2]
    have : r 3 = 1 := h3
    simp [this]
  · intro n hn16
    have e : ∀ v : V4, appN 1 (enc p) (enc q) (enc r) (enc v) = enc (app (Msig p q r) v) := by
      intro v
      rw [enc_app]
      have : enc (Msig p q r 0) = 1 := enc_idc0
      rw [this]
      rfl
    have := hc (dec n)
    have e3 : appN 1 (enc p) (enc q) (enc r) (appN 1 (enc p) (enc q) (enc r)
        (appN 1 (enc p) (enc q) (enc r) (enc (dec n)))) = enc (dec n) := by
      rw [e, e, e, this]
    rwa [enc_dec n hn16] at e3
  · rintro ⟨hp, hq⟩
    apply hn
    refine ⟨?_, ?_⟩
    · rcases hp with hp | hp
      · left
        have := dec_enc p
        rw [hp] at this
        rw [← this]
        exact dec_special.2.1
      · right
        have := dec_enc p
        rw [hp] at this
        rw [← this]
        exact dec_special.2.2.1
    · rcases hq with hq | hq
      · left
        have := dec_enc q
        rw [hq] at this
        rw [← this]
        exact dec_special.2.2.2.1
      · right
        have := dec_enc q
        rw [hq] at this
        rw [← this]
        exact dec_special.2.2.2.2

theorem reach_transitive (x y ε x' y' : ZMod 2) (p q r : V4) (hG : GuardS (Msig p q r))
    (O : Set V4) (h0 : idc 0 ∈ O) (hW : ∀ c ∈ O, app (Wm x y) c ∈ O)
    (hU : ∀ c ∈ O, app (Um ε x' y') c ∈ O) (hS : ∀ c ∈ O, app (Msig p q r) c ∈ O) :
    ∀ c : V4, c ≠ 0 → c ∈ O := by
  have hN := reach_all_N (enc p) (enc_lt p) (enc q) (enc_lt q) (enc r) (enc_lt r)
    (guardN_of p q r hG)
  have hF := hN x.val (ZMod.val_lt x) y.val (ZMod.val_lt y) ε.val (ZMod.val_lt ε) x'.val
    (ZMod.val_lt x') y'.val (ZMod.val_lt y')
  have hgens : [tabW x.val y.val, tabU ε.val x'.val y'.val, tabS (enc p) (enc q) (enc r)] =
      [Wm x y, Um ε x' y', Msig p q r].map tabV := by
    simp only [List.map_cons, List.map_nil, tabV_Wm, tabV_Um, tabV_Msig]
  have hinv := reachM_inv [Wm x y, Um ε x' y', Msig p q r] O h0 (by
    intro M hM c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
    rcases hM with rfl | rfl | rfl
    · exact hW c hc
    · exact hU c hc
    · exact hS c hc) 7
  intro c hc
  have hne : enc c ≠ 0 := by
    intro h
    apply hc
    have := dec_enc c
    rw [h] at this
    rw [← this]
    exact dec_special.1
  have hbit := hF (enc c) (enc_lt c) hne
  rw [hgens] at hbit
  have := (hinv (enc c) hbit).2
  rwa [dec_enc] at this

end CFSG.Quasithin.H13.U43
