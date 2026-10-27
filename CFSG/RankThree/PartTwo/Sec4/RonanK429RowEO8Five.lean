module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowEO8Copies

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429E

namespace O8Out

open CFSG.EvenSmallLie.OmegaEight
open CFSG.Monster.B.Co2 (Rep getElem!_ofFn_nat)

@[expose] def pairK (i k : ℕ) : ℕ × ℕ := (rootPairs.getD i []).getD k (0, 0)

@[expose] def eK (i k v : ℕ) : ℕ := eichNat (pairK i k).1 (pairK i k).2 v

theorem eK_ok : ∀ i < 8, ∀ k < 3, ∀ v < 256, qNat v = true →
    eK i k v < 256 ∧ qNat (eK i k v) = true := by
  decide +kernel


theorem nsIdx_lt {v : ℕ} (hv : v < 256) (hq : qNat v = true) : nsIdx[v]! < 120 :=
  (ns_ok.2.2.2 v hv hq).1

theorem nsArr_nsIdx {v : ℕ} (hv : v < 256) (hq : qNat v = true) : nsArr[nsIdx[v]!]! = v :=
  (ns_ok.2.2.2 v hv hq).2

theorem gen_apply_pt {i : ℕ} (hi : i < 8) {k : ℕ} (hk : k < 3) {v : ℕ} (hv : v < 256)
    (hq : qNat v = true) (p : Fin 360) (hp : (p : ℕ) = 120 * k + nsIdx[v]!) :
    ((gen i p : Fin 360) : ℕ) = 120 * k + nsIdx[eK i k v]! := by
  have hr := rep_gen (by omega : i < 10) p
  rw [genArrs_getElem! hi, rootArr, getElem!_ofFn_nat _ p.2] at hr
  rw [← hr]
  have hl := nsIdx_lt hv hq
  have hd : (p : ℕ) / 120 = k := by omega
  have hm : (p : ℕ) % 120 = nsIdx[v]! := by omega
  simp only [hd, hm, nsArr_nsIdx hv hq]
  rfl

@[expose] noncomputable def wordPerm (w : List ℕ) : Equiv.Perm (Fin 360) := (w.map gen).prod

@[expose] def wordAct (w : List ℕ) (k v : ℕ) : ℕ := w.foldr (fun i u => eK i k u) v

theorem wordPerm_mem {w : List ℕ} (hw : ∀ i ∈ w, i < 8) : wordPerm w ∈ omegaT := by
  refine omegaT.list_prod_mem fun g hg => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
  exact gen_mem_omegaT (hw i hi)

theorem wordPerm_apply : ∀ (w : List ℕ), (∀ i ∈ w, i < 8) → ∀ {k : ℕ}, k < 3 → ∀ {v : ℕ},
    v < 256 → qNat v = true → ∀ p : Fin 360, (p : ℕ) = 120 * k + nsIdx[v]! →
      ((wordPerm w p : Fin 360) : ℕ) = 120 * k + nsIdx[wordAct w k v]! ∧
        wordAct w k v < 256 ∧ qNat (wordAct w k v) = true
  | [], _, _, _, _, hv, hq, p, hp => ⟨hp, hv, hq⟩
  | i :: w, hw, k, hk, v, hv, hq, p, hp => by
    obtain ⟨h1, h2, h3⟩ := wordPerm_apply w (fun j hj => hw j (List.mem_cons_of_mem i hj)) hk
      hv hq p hp
    have hi : i < 8 := hw i List.mem_cons_self
    obtain ⟨h4, h5⟩ := eK_ok i hi k hk _ h2 h3
    refine ⟨?_, h4, h5⟩
    have : wordPerm (i :: w) = gen i * wordPerm w := by
      rw [wordPerm, List.map_cons, List.prod_cons]
      rfl
    rw [this, Equiv.Perm.mul_apply, gen_apply_pt hi hk h2 h3 _ h1]
    rfl

theorem pt_decomp (p : Fin 360) : nsArr[(p : ℕ) % 120]! < 256 ∧ qNat nsArr[(p : ℕ) % 120]! = true ∧
    (p : ℕ) = 120 * ((p : ℕ) / 120) + nsIdx[nsArr[(p : ℕ) % 120]!]! := by
  obtain ⟨h1, h2, h3⟩ := ns_ok.2.2.1 ((p : ℕ) % 120) (Nat.mod_lt _ (by norm_num))
  refine ⟨h1, h2, ?_⟩
  rw [h3]
  omega

theorem nsIdx_inj {v u : ℕ} (hv : v < 256) (hq : qNat v = true) (hu : u < 256)
    (hqu : qNat u = true) (h : nsIdx[v]! = nsIdx[u]!) : v = u := by
  rw [← nsArr_nsIdx hv hq, ← nsArr_nsIdx hu hqu, h]

@[expose] def w1 : List ℕ := [5, 4, 3, 2, 1, 0]

@[expose] def w2 : List ℕ := [5, 3, 6, 0, 7, 2, 3, 5, 0, 6, 2, 7, 5, 4, 3, 2, 1, 0, 7, 2, 6, 0, 5,
  3, 2, 7, 0, 6, 3, 5]

theorem w1_lt : ∀ i ∈ w1, i < 8 := by decide

theorem w2_lt : ∀ i ∈ w2, i < 8 := by decide

@[expose] def appM (M : List ℕ) (v : ℕ) : ℕ :=
  (List.range 8).foldl (fun acc c => if v.testBit c then acc ^^^ M.getD c 0 else acc) 0

@[expose] def m1 : ℕ → List ℕ
  | 0 => [15, 1, 2, 4, 128, 144, 160, 192]
  | 1 => [3, 5, 129, 120, 32, 64, 8, 1]
  | _ => [1, 134, 74, 2, 16, 8, 4, 44]

@[expose] def m2 : ℕ → List ℕ
  | 0 => [205, 133, 26, 59, 30, 45, 75, 135]
  | 1 => [194, 206, 55, 15, 150, 165, 195, 37]
  | _ => [179, 3, 250, 9, 255, 33, 190, 126]

theorem w1_act : ∀ k < 3, ∀ v < 256, wordAct w1 k v = appM (m1 k) v := by decide +kernel

theorem w2_act : ∀ k < 3, ∀ v < 256, wordAct w2 k v = appM (m2 k) v := by decide +kernel

theorem appM_lt : ∀ k < 3, ∀ v < 256, appM (m1 k) v < 256 ∧ appM (m2 k) v < 256 := by
  decide +kernel

@[expose] def itA (a b k v : ℕ) : ℕ := (appM (m1 k))^[a] ((appM (m2 k))^[b] v)

@[expose] def k0tab (a b : ℕ) : ℕ :=
  if b = 0 ∨ a = 0 then 2 else
  if (a = 1 ∧ (b = 1 ∨ b = 4)) ∨ (a = 2 ∧ (b = 2 ∨ b = 3)) ∨ (a = 3 ∧ (b = 2 ∨ b = 3)) ∨
    (a = 4 ∧ (b = 1 ∨ b = 4)) then 1 else 0

@[expose] def p5Check : Bool :=
  (List.range 5).all fun a => (List.range 5).all fun b => (a == 0 && b == 0) ||
    (((List.range 256).any fun v => qNat v && itA a b (k0tab a b) v == v) &&
      (List.range 3).all fun k => (List.range 256).all fun v =>
        !(qNat v && itA a b k v == v) || k == k0tab a b)

theorem p5Check_eq : p5Check = true := by decide +kernel

theorem p5_fix_check : ∀ a < 5, ∀ b < 5, ¬ (a = 0 ∧ b = 0) →
    (∃ v < 256, qNat v = true ∧ itA a b (k0tab a b) v = v) ∧
      ∀ k < 3, ∀ v < 256, qNat v = true → itA a b k v = v → k = k0tab a b := by
  intro a ha b hb hab
  have h := p5Check_eq
  unfold p5Check at h
  rw [List.all_eq_true] at h
  have h1 := h a (List.mem_range.mpr ha)
  rw [List.all_eq_true] at h1
  have h2 := h1 b (List.mem_range.mpr hb)
  have hab' : (a == 0 && b == 0) = false := by
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · have hb0 : b ≠ 0 := fun hb0 => hab ⟨rfl, hb0⟩
      simp [hb0]
    · have : a ≠ 0 := by omega
      simp [this]
  rw [hab', Bool.false_or, Bool.and_eq_true] at h2
  obtain ⟨hex, hall⟩ := h2
  rw [List.any_eq_true] at hex
  obtain ⟨v, hv, hv'⟩ := hex
  rw [Bool.and_eq_true, beq_iff_eq] at hv'
  refine ⟨⟨v, List.mem_range.mp hv, hv'.1, hv'.2⟩, fun k hk u hu hqu hfu => ?_⟩
  rw [List.all_eq_true] at hall
  have h3 := hall k (List.mem_range.mpr hk)
  rw [List.all_eq_true] at h3
  have h4 := h3 u (List.mem_range.mpr hu)
  have hfu' : (itA a b k u == u) = true := beq_iff_eq.mpr hfu
  rw [hqu, hfu', Bool.and_self, Bool.not_true, Bool.false_or, beq_iff_eq] at h4
  exact h4

theorem k0tab_lt (a b : ℕ) : k0tab a b < 3 := by
  unfold k0tab
  split_ifs <;> omega

theorem appM_iterate_lt (k : ℕ) (hk : k < 3) (a b : ℕ) {v : ℕ} (hv : v < 256) :
    (appM (m2 k))^[b] v < 256 ∧ itA a b k v < 256 := by
  have h2 : ∀ n {u : ℕ}, u < 256 → (appM (m2 k))^[n] u < 256 := by
    intro n
    induction n with
    | zero => exact fun hu => hu
    | succ n ih => intro u hu; rw [Function.iterate_succ_apply']; exact (appM_lt k hk _ (ih hu)).2
  have h1 : ∀ n {u : ℕ}, u < 256 → (appM (m1 k))^[n] u < 256 := by
    intro n
    induction n with
    | zero => exact fun hu => hu
    | succ n ih => intro u hu; rw [Function.iterate_succ_apply']; exact (appM_lt k hk _ (ih hu)).1
  exact ⟨h2 b hv, h1 a (h2 b hv)⟩

theorem wordAct_append (u w : List ℕ) (k v : ℕ) :
    wordAct (u ++ w) k v = wordAct u k (wordAct w k v) := by
  rw [wordAct, wordAct, wordAct, List.foldr_append]

@[expose] def powW (w : List ℕ) (a : ℕ) : List ℕ := (List.replicate a w).flatten

theorem powW_succ (w : List ℕ) (a : ℕ) : powW w (a + 1) = w ++ powW w a := by
  rw [powW, powW, List.replicate_succ, List.flatten_cons]

theorem powW_lt {w : List ℕ} (hw : ∀ i ∈ w, i < 8) (a : ℕ) : ∀ i ∈ powW w a, i < 8 := by
  intro i hi
  rw [powW, List.mem_flatten] at hi
  obtain ⟨l, hl, hil⟩ := hi
  rw [List.eq_of_mem_replicate hl] at hil
  exact hw i hil

theorem wordPerm_append (u w : List ℕ) : wordPerm (u ++ w) = wordPerm u * wordPerm w := by
  rw [wordPerm, wordPerm, wordPerm, List.map_append, List.prod_append]

theorem wordPerm_powW (w : List ℕ) (a : ℕ) : wordPerm (powW w a) = wordPerm w ^ a := by
  induction a with
  | zero => rfl
  | succ a ih => rw [powW_succ, wordPerm_append, ih, pow_succ']

@[expose] def wab (a b : ℕ) : List ℕ := powW w1 a ++ powW w2 b

theorem wab_lt (a b : ℕ) : ∀ i ∈ wab a b, i < 8 := by
  intro i hi
  rcases List.mem_append.mp hi with h | h
  · exact powW_lt w1_lt a i h
  · exact powW_lt w2_lt b i h

theorem wordAct_powW_w1 (k : ℕ) (hk : k < 3) (a : ℕ) {v : ℕ} (hv : v < 256) :
    wordAct (powW w1 a) k v = (appM (m1 k))^[a] v := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [powW_succ, wordAct_append, ih, Function.iterate_succ_apply', w1_act k hk _
      (show (appM (m1 k))^[a] v < 256 from (appM_iterate_lt k hk a 0 hv).2)]

theorem wordAct_powW_w2 (k : ℕ) (hk : k < 3) (b : ℕ) {v : ℕ} (hv : v < 256) :
    wordAct (powW w2 b) k v = (appM (m2 k))^[b] v := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [powW_succ, wordAct_append, ih, Function.iterate_succ_apply', w2_act k hk _
      ((appM_iterate_lt k hk 0 b hv).1)]

theorem wordAct_wab (a b k : ℕ) (hk : k < 3) {v : ℕ} (hv : v < 256) :
    wordAct (wab a b) k v = itA a b k v := by
  rw [wab, wordAct_append, wordAct_powW_w2 k hk b hv,
    wordAct_powW_w1 k hk a (appM_iterate_lt k hk 0 b hv).1]
  rfl

theorem fix_wab {a b : ℕ} (ha : a < 5) (hb : b < 5) (hab : ¬ (a = 0 ∧ b = 0)) :
    (∃ p : Fin 360, wordPerm (wab a b) p = p) ∧
      ∀ p : Fin 360, wordPerm (wab a b) p = p → (blk p : ℕ) = k0tab a b := by
  obtain ⟨⟨v, hv, hq, hfix⟩, hall⟩ := p5_fix_check a ha b hb hab
  have hk0 := k0tab_lt a b
  refine ⟨?_, fun p hp => ?_⟩
  · have hl := nsIdx_lt hv hq
    refine ⟨⟨120 * k0tab a b + nsIdx[v]!, by omega⟩, Fin.ext ?_⟩
    obtain ⟨h1, -, -⟩ := wordPerm_apply (wab a b) (wab_lt a b) hk0 hv hq
      ⟨120 * k0tab a b + nsIdx[v]!, by omega⟩ rfl
    rw [h1, wordAct_wab a b _ hk0 hv, hfix]
  · obtain ⟨hv1, hv2, hp'⟩ := pt_decomp p
    have hk : (p : ℕ) / 120 < 3 := by omega
    obtain ⟨h1, h2, h3⟩ := wordPerm_apply (wab a b) (wab_lt a b) hk hv1 hv2 p hp'
    have hpv : ((wordPerm (wab a b) p : Fin 360) : ℕ) = (p : ℕ) := by rw [hp]
    rw [h1] at hpv
    have hidx : nsIdx[wordAct (wab a b) ((p : ℕ) / 120) nsArr[(p : ℕ) % 120]!]! =
        nsIdx[nsArr[(p : ℕ) % 120]!]! := by omega
    have heq := nsIdx_inj h2 h3 hv1 hv2 hidx
    rw [wordAct_wab a b _ hk hv1] at heq
    rw [blk_val]
    exact hall _ hk _ hv1 hv2 heq

end O8Out

end CFSG.RankThree.PartTwo.Sec4.RonanK429E
