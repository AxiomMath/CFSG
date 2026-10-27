module

public import CFSG.Quasithin.AppendixH.H14.H142Arr

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.Quasithin.H.Mathieu CFSG.ASVolI.ChH CFSG.Monster.Code CFSG.Open

@[expose] def tab64OK (tab : Array (Array ℕ)) : Bool :=
  decide (tab.size = 64) && (tab[0]! == id24) &&
    (List.range 64).all (fun n => inAutOK tab[n]! &&
      (List.range 6).all fun i => comp24 tab[n]! tab[2 ^ i]! == tab[n ^^^ 2 ^ i]!) &&
    (List.range 64).all fun n => (List.range 64).all fun m => ((tab[n]! == tab[m]!) == (n == m))

theorem arr_eq_of_hasArr {σ : S24} {a b : Array ℕ} (ha : HasArr σ a) (hb : HasArr σ b)
    (hsa : a.size = 24) (hsb : b.size = 24) : a = b := by
  refine Array.ext (by rw [hsa, hsb]) fun i hi₁ hi₂ => ?_
  have hi : i < 24 := by rw [hsa] at hi₁; exact hi₁
  rw [← getElem!_pos a i hi₁, ← getElem!_pos b i hi₂]
  exact (ha ⟨i, hi⟩).symm.trans (hb ⟨i, hi⟩)

theorem tab64OK_spec {tab : Array (Array ℕ)} (h : tab64OK tab = true) :
    tab[0]! = id24 ∧ ∀ n < 64, inAutOK tab[n]! = true ∧
      ∀ m < 64, comp24 tab[n]! tab[m]! = tab[n ^^^ m]! ∧ (tab[n]! = tab[m]! ↔ n = m) := by
  unfold tab64OK at h
  have hAB := Bool.and_eq_true_iff.mp h
  have hAB1 := Bool.and_eq_true_iff.mp hAB.1
  have hAB2 := Bool.and_eq_true_iff.mp hAB1.1
  have h0 : tab[0]! = id24 := beq_iff_eq.mp hAB2.2
  have hxor64 : ∀ {n m : ℕ}, n < 64 → m < 64 → n ^^^ m < 64 := by
    intro n m hn hm
    have hn' : n < 2 ^ 6 := by rw [show (2 : ℕ) ^ 6 = 64 by norm_num]; exact hn
    have hm' : m < 2 ^ 6 := by rw [show (2 : ℕ) ^ 6 = 64 by norm_num]; exact hm
    have h := Nat.xor_lt_two_pow hn' hm'
    rwa [show (2 : ℕ) ^ 6 = 64 by norm_num] at h
  have hIA : ∀ n < 64, inAutOK tab[n]! = true := by
    intro n hn
    exact (Bool.and_eq_true_iff.mp (List.all_eq_true.1 hAB1.2 n (List.mem_range.2 hn))).1
  have hBas : ∀ n < 64, ∀ i < 6, comp24 tab[n]! tab[2 ^ i]! = tab[n ^^^ 2 ^ i]! := by
    intro n hn i hi
    exact beq_iff_eq.mp (List.all_eq_true.1
      (Bool.and_eq_true_iff.mp (List.all_eq_true.1 hAB1.2 n (List.mem_range.2 hn))).2
      i (List.mem_range.2 hi))
  have hDist : ∀ n < 64, ∀ m < 64, (tab[n]! = tab[m]! ↔ n = m) := by
    intro n hn m hm
    have hcm := List.all_eq_true.1 (List.all_eq_true.1 hAB.2 n (List.mem_range.2 hn))
      m (List.mem_range.2 hm)
    rw [← beq_iff_eq (a := tab[n]!) (b := tab[m]!), ← beq_iff_eq (a := n) (b := m),
      beq_iff_eq.mp hcm]
  have hsize : ∀ n < 64, (tab[n]!).size = 24 := by
    intro n hn
    have hlt : n ^^^ 1 < 64 := hxor64 hn (by norm_num)
    have h1 := hBas (n ^^^ 1) hlt 0 (by norm_num)
    have hx : (n ^^^ 1) ^^^ 2 ^ 0 = n := by
      rw [show (2 : ℕ) ^ 0 = 1 by norm_num, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [hx] at h1
    rw [← h1]
    simp [comp24]
  have hpowlt : ∀ h : Fin 6, 2 ^ (h : ℕ) < 64 := by decide +kernel
  have hdec : ∀ m : Fin 64, (m : ℕ) = 0 ∨ ∃ h : Fin 6, ((m : ℕ) ^^^ 2 ^ (h : ℕ)) < (m : ℕ) := by
    decide +kernel
  have hmul : ∀ n < 64, ∀ m < 64,
      permOfArrD tab[n]! * permOfArrD tab[m]! = permOfArrD tab[n ^^^ m]! := by
    intro n hn
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      rcases hdec ⟨m, hm⟩ with hm0 | ⟨h, hlt'⟩
      · have hm0' : m = 0 := hm0
        rw [hm0']
        have hzero : permOfArrD tab[0]! = 1 := by
          refine hasArr_unique (hasArr_permOfArrD (hIA 0 (by norm_num))) ?_
          rw [h0]
          exact hasArr_one
        rw [Nat.xor_zero, hzero, mul_one]
      · set m' := m ^^^ 2 ^ (h : ℕ) with hm'def
        have hm'lt : m' < m := hlt'
        have hm'64 : m' < 64 := hm'lt.trans hm
        have hpow : 2 ^ (h : ℕ) < 64 := hpowlt h
        have hm_eq : m' ^^^ 2 ^ (h : ℕ) = m := by
          rw [hm'def, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        have hprod' : permOfArrD tab[m']! * permOfArrD tab[2 ^ (h : ℕ)]! =
            permOfArrD tab[m' ^^^ 2 ^ (h : ℕ)]! := by
          refine hasArr_unique ?_ (hasArr_permOfArrD (hIA _ (hxor64 hm'64 hpow)))
          have hmulh := hasArr_mul (hasArr_permOfArrD (hIA m' hm'64))
            (hasArr_permOfArrD (hIA (2 ^ (h : ℕ)) hpow))
          rwa [hBas m' hm'64 h h.2] at hmulh
        have hprod_n : permOfArrD tab[n ^^^ m']! * permOfArrD tab[2 ^ (h : ℕ)]! =
            permOfArrD tab[(n ^^^ m') ^^^ 2 ^ (h : ℕ)]! := by
          refine hasArr_unique ?_ (hasArr_permOfArrD
            (hIA _ (hxor64 (hxor64 hn hm'64) hpow)))
          have hmulh := hasArr_mul (hasArr_permOfArrD (hIA (n ^^^ m') (hxor64 hn hm'64)))
            (hasArr_permOfArrD (hIA (2 ^ (h : ℕ)) hpow))
          rwa [hBas (n ^^^ m') (hxor64 hn hm'64) h h.2] at hmulh
        have hxor : (n ^^^ m') ^^^ 2 ^ (h : ℕ) = n ^^^ m := by
          rw [Nat.xor_assoc, hm_eq]
        calc permOfArrD tab[n]! * permOfArrD tab[m]!
            = permOfArrD tab[n]! * permOfArrD tab[m' ^^^ 2 ^ (h : ℕ)]! := by rw [← hm_eq]
          _ = permOfArrD tab[n]! * (permOfArrD tab[m']! * permOfArrD tab[2 ^ (h : ℕ)]!) := by
                rw [hprod']
          _ = (permOfArrD tab[n]! * permOfArrD tab[m']!) * permOfArrD tab[2 ^ (h : ℕ)]! := by
                rw [mul_assoc]
          _ = permOfArrD tab[n ^^^ m']! * permOfArrD tab[2 ^ (h : ℕ)]! := by
                rw [ih m' hm'lt hm'64]
          _ = permOfArrD tab[(n ^^^ m') ^^^ 2 ^ (h : ℕ)]! := hprod_n
          _ = permOfArrD tab[n ^^^ m]! := by rw [hxor]
  have hcomp : ∀ n < 64, ∀ m < 64, comp24 tab[n]! tab[m]! = tab[n ^^^ m]! := by
    intro n hn m hm
    have harr : HasArr (permOfArrD tab[n]! * permOfArrD tab[m]!) (comp24 tab[n]! tab[m]!) :=
      hasArr_mul (hasArr_permOfArrD (hIA n hn)) (hasArr_permOfArrD (hIA m hm))
    rw [hmul n hn m hm] at harr
    exact arr_eq_of_hasArr harr (hasArr_permOfArrD (hIA (n ^^^ m) (hxor64 hn hm)))
      (by simp [comp24]) (hsize (n ^^^ m) (hxor64 hn hm))
  exact ⟨h0, fun n hn => ⟨hIA n hn, fun m hm => ⟨hcomp n hn m hm, hDist n hn m hm⟩⟩⟩

theorem xor_lt_64 {n m : ℕ} (hn : n < 64) (hm : m < 64) : n ^^^ m < 64 := by
  have hn' : n < 2 ^ 6 := by rw [show (2 : ℕ) ^ 6 = 64 by norm_num]; exact hn
  have hm' : m < 2 ^ 6 := by rw [show (2 : ℕ) ^ 6 = 64 by norm_num]; exact hm
  have h := Nat.xor_lt_two_pow hn' hm'
  rwa [show (2 : ℕ) ^ 6 = 64 by norm_num] at h

@[expose] noncomputable def tab64Perm (tab : Array (Array ℕ)) (n : ℕ) : S24 := permOfArrD tab[n]!

variable {tab : Array (Array ℕ)}

theorem hasArr_tab64Perm (hT : tab64OK tab = true) {n : ℕ} (hn : n < 64) :
    HasArr (tab64Perm tab n) tab[n]! :=
  hasArr_permOfArrD ((tab64OK_spec hT).2 n hn).1

theorem tab64_size_lt (hT : tab64OK tab = true) {n : ℕ} (hn : n < 64) : (tab[n]!).size = 24 := by
  have h' : comp24 tab[n]! tab[0]! = tab[n]! := by
    simpa using ((tab64OK_spec hT).2 n hn).2 0 (by norm_num) |>.1
  rw [← h']
  simp [comp24]

theorem tab64Perm_zero (hT : tab64OK tab = true) : tab64Perm tab 0 = 1 := by
  exact hasArr_unique (by simpa [(tab64OK_spec hT).1] using hasArr_tab64Perm hT (n := 0) (by norm_num))
    hasArr_one

theorem tab64Perm_mul (hT : tab64OK tab = true) {n m : ℕ} (hn : n < 64) (hm : m < 64) :
    tab64Perm tab n * tab64Perm tab m = tab64Perm tab (n ^^^ m) := by
  refine hasArr_unique ?_ (hasArr_tab64Perm hT (xor_lt_64 hn hm))
  have h := hasArr_mul (hasArr_tab64Perm hT hn) (hasArr_tab64Perm hT hm)
  rwa [((tab64OK_spec hT).2 n hn).2 m hm |>.1] at h

theorem tab64Perm_mul_self (hT : tab64OK tab = true) {n : ℕ} (hn : n < 64) :
    tab64Perm tab n * tab64Perm tab n = 1 := by
  rw [tab64Perm_mul hT hn hn, Nat.xor_self, tab64Perm_zero hT]

theorem tab64Perm_inj (hT : tab64OK tab = true) {n m : ℕ} (hn : n < 64) (hm : m < 64)
    (h : tab64Perm tab n = tab64Perm tab m) : n = m := by
  have hnm_lt : n ^^^ m < 64 := xor_lt_64 hn hm
  have h1 : tab64Perm tab (n ^^^ m) = 1 := by
    have hsq : tab64Perm tab n * tab64Perm tab m = 1 := by rw [h, tab64Perm_mul_self hT hm]
    rw [← tab64Perm_mul hT hn hm, hsq]
  have harr : HasArr (tab64Perm tab (n ^^^ m)) tab[n ^^^ m]! := hasArr_tab64Perm hT hnm_lt
  have harr1 : HasArr (1 : S24) tab[n ^^^ m]! := by rwa [h1] at harr
  have heq : tab[n ^^^ m]! = id24 := by
    refine Array.ext ?_ fun i hi₁ hi₂ => ?_
    · rw [tab64_size_lt hT hnm_lt]
      simp [id24]
    · have hi24 : i < 24 := by rw [tab64_size_lt hT hnm_lt] at hi₁; exact hi₁
      rw [← getElem!_pos (tab[n ^^^ m]!) i hi₁, ← getElem!_pos id24 i hi₂]
      exact (harr1 ⟨i, hi24⟩).symm.trans (hasArr_one ⟨i, hi24⟩)
  have hinj := ((tab64OK_spec hT).2 (n ^^^ m) hnm_lt).2 0 (by norm_num) |>.2
  have hzero : n ^^^ m = 0 := hinj.1 (by rw [heq, (tab64OK_spec hT).1])
  exact xor_eq_zero_iff.mp hzero

theorem tab64Perm_mem_M24g (hT : tab64OK tab = true) {n : ℕ} (hn : n < 64) :
    tab64Perm tab n ∈ M24g :=
  permOfArrD_mem_M24g ((tab64OK_spec hT).2 n hn).1

theorem tab64Perm_comm (hT : tab64OK tab = true) {n m : ℕ} (hn : n < 64) (hm : m < 64) :
    tab64Perm tab n * tab64Perm tab m = tab64Perm tab m * tab64Perm tab n := by
  rw [tab64Perm_mul hT hn hm, tab64Perm_mul hT hm hn, Nat.xor_comm]

@[expose] noncomputable def tab64Sub (tab : Array (Array ℕ)) (hT : tab64OK tab = true) : Subgroup S24 where
  carrier := {x | ∃ n < 64, x = tab64Perm tab n}
  mul_mem' := by
    rintro x y ⟨n, hn, rfl⟩ ⟨m, hm, rfl⟩
    exact ⟨n ^^^ m, xor_lt_64 hn hm, tab64Perm_mul hT hn hm⟩
  one_mem' := ⟨0, by norm_num, (tab64Perm_zero hT).symm⟩
  inv_mem' := by
    rintro x ⟨n, hn, rfl⟩
    exact ⟨n, hn, inv_eq_of_mul_eq_one_right (tab64Perm_mul_self hT hn)⟩

theorem mem_tab64Sub (hT : tab64OK tab = true) {x : S24} :
    x ∈ tab64Sub tab hT ↔ ∃ n < 64, x = tab64Perm tab n := Iff.rfl

theorem tab64Perm_mem_tab64Sub (hT : tab64OK tab = true) {n : ℕ} (hn : n < 64) :
    tab64Perm tab n ∈ tab64Sub tab hT :=
  ⟨n, hn, rfl⟩

theorem card_tab64Sub (hT : tab64OK tab = true) : Nat.card ↥(tab64Sub tab hT) = 64 := by
  let f : Fin 64 → ↥(tab64Sub tab hT) := fun n => ⟨tab64Perm tab n, tab64Perm_mem_tab64Sub hT n.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro n m h
      have h' : tab64Perm tab (n : ℕ) = tab64Perm tab (m : ℕ) := congrArg Subtype.val h
      exact Fin.ext (tab64Perm_inj hT n.2 m.2 h')
    · intro y
      obtain ⟨n, hn, heq⟩ := y.2
      exact ⟨⟨n, hn⟩, Subtype.ext heq.symm⟩
  calc Nat.card ↥(tab64Sub tab hT) = Nat.card (Fin 64) :=
        (Nat.card_congr (Equiv.ofBijective f hf)).symm
    _ = 64 := Nat.card_fin 64

theorem isElemAbelian_tab64Sub (hT : tab64OK tab = true) : IsElemAbelian 2 (tab64Sub tab hT) := by
  rw [IsElemAbelian, isMulCommutative_iff]
  refine ⟨?_, ?_⟩
  · intro x y
    obtain ⟨n, hn, heq⟩ := x.2
    obtain ⟨m, hm, heq'⟩ := y.2
    exact Subtype.ext (by
      show (x : S24) * (y : S24) = (y : S24) * (x : S24)
      rw [heq, heq']
      exact tab64Perm_comm hT hn hm)
  · intro x hx
    obtain ⟨n, hn, heq⟩ := hx
    rw [heq]
    simpa [pow_two] using tab64Perm_mul_self hT hn

theorem isPGroup_tab64Sub (hT : tab64OK tab = true) : IsPGroup 2 (tab64Sub tab hT) :=
  IsPGroup.of_card (n := 6) (by rw [card_tab64Sub hT]; norm_num)

theorem tab64Sub_ne_bot (hT : tab64OK tab = true) : tab64Sub tab hT ≠ ⊥ := by
  intro hbot
  have hcard := card_tab64Sub hT
  rw [hbot, Subgroup.card_bot] at hcard
  norm_num at hcard

@[expose] def tab64Idx (tab : Array (Array ℕ)) (b : Array ℕ) : ℕ :=
  ((List.range 64).find? fun m => tab[m]! == b).getD 64

theorem tab64Idx_spec {b : Array ℕ} (hm : tab64Idx tab b < 64) : tab[tab64Idx tab b]! = b := by
  unfold tab64Idx at hm ⊢
  have hne : (List.range 64).find? (fun m => tab[m]! == b) ≠ none := by
    intro hnone
    rw [hnone] at hm
    simp only [Option.getD_none] at hm
    omega
  obtain ⟨m, hfind⟩ := Option.ne_none_iff_exists'.mp hne
  have hsome := List.find?_some hfind
  have hbeq : tab[m]! = b := beq_iff_eq.mp hsome
  have hidx : ((List.range 64).find? (fun m => tab[m]! == b)).getD 64 = m := by
    rw [hfind]; rfl
  rw [hidx]
  exact hbeq

@[expose] def cmap64 (tab : Array (Array ℕ)) (a : Array ℕ) (n : ℕ) : ℕ :=
  tab64Idx tab (conj24 a tab[n]!)

theorem conj_tab64Perm (hT : tab64OK tab = true) {g : S24} {a : Array ℕ} (hg : HasArr g a)
    (ha : inAutOK a = true) {n : ℕ} (hn : n < 64) (hm : cmap64 tab a n < 64) :
    g * tab64Perm tab n * g⁻¹ = tab64Perm tab (cmap64 tab a n) := by
  have harr : HasArr (g * tab64Perm tab n * g⁻¹) (conj24 a tab[n]!) :=
    hasArr_conj hg ha (hasArr_tab64Perm hT hn)
  have hentry : tab[cmap64 tab a n]! = conj24 a tab[n]! := by
    simpa [cmap64] using tab64Idx_spec (tab := tab) (b := conj24 a tab[n]!)
      (by simpa [cmap64] using hm)
  rw [← hentry] at harr
  exact hasArr_unique harr (hasArr_tab64Perm hT hm)

@[expose] def vbfs64OK (tab : Array (Array ℕ)) (gens : List (Array ℕ)) (n₀ : ℕ)
    (L : List (ℕ × ℕ × ℕ)) : Bool :=
  (List.range L.length).all fun k =>
    if k = 0 then (L.getD 0 (0, 0, 0)).1 == n₀ && decide (n₀ < 64) else
      decide ((L.getD k (0, 0, 0)).2.2 < k) && decide ((L.getD k (0, 0, 0)).2.1 < gens.length) &&
        (L.getD k (0, 0, 0)).1 == cmap64 tab (gens.getD (L.getD k (0, 0, 0)).2.1 #[])
          (L.getD (L.getD k (0, 0, 0)).2.2 (0, 0, 0)).1 &&
        decide ((L.getD k (0, 0, 0)).1 < 64)

theorem exists_conj_of_vbfs64 (hT : tab64OK tab = true) {M : Subgroup S24} {gens : List (Array ℕ)}
    (hg : ∀ a ∈ gens, inAutOK a = true ∧ ∃ σ ∈ M, HasArr σ a) {n₀ : ℕ}
    {L : List (ℕ × ℕ × ℕ)} (hL : vbfs64OK tab gens n₀ L = true) :
    ∀ k < L.length, (L.getD k (0, 0, 0)).1 < 64 ∧
      ∃ g ∈ M, g * tab64Perm tab n₀ * g⁻¹ = tab64Perm tab (L.getD k (0, 0, 0)).1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hc := List.all_eq_true.1 hL k (List.mem_range.2 hk)
    by_cases h0 : k = 0
    · subst h0
      simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      obtain ⟨hn0eq, hn0lt⟩ := hc
      refine ⟨by rw [hn0eq]; exact hn0lt, 1, M.one_mem, ?_⟩
      rw [hn0eq]
      simp
    · simp only [h0, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      obtain ⟨⟨⟨hq, hj⟩, heq⟩, hlt⟩ := hc
      obtain ⟨hplt, g, hgM, hgconj⟩ := ih _ hq (hq.trans hk)
      have hjm : gens.getD (L.getD k (0, 0, 0)).2.1 #[] ∈ gens := by
        rw [List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem hj
      obtain ⟨haut, σ, hσM, hσarr⟩ := hg _ hjm
      refine ⟨hlt, σ * g, M.mul_mem hσM hgM, ?_⟩
      have hcmap : cmap64 tab (gens.getD (L.getD k (0, 0, 0)).2.1 #[])
          (L.getD (L.getD k (0, 0, 0)).2.2 (0, 0, 0)).1 < 64 := by
        rw [← heq]; exact hlt
      have hconj := conj_tab64Perm hT hσarr haut hplt hcmap
      have hgrp : σ * g * tab64Perm tab n₀ * (σ * g)⁻¹
          = σ * (g * tab64Perm tab n₀ * g⁻¹) * σ⁻¹ := by group
      rw [hgrp, hgconj, hconj, heq]

@[expose] def derivOK (L : List ℕ) (D : List (ℕ × ℕ)) : Bool :=
  (List.range 63).all fun i =>
    L.contains (D.getD i (0, 0)).1 && decide ((D.getD i (0, 0)).2 < i + 1) &&
      ((D.getD i (0, 0)).1 ^^^ (D.getD i (0, 0)).2 == i + 1)

theorem exists_deriv_of_derivOK {L : List ℕ} {D : List (ℕ × ℕ)} (h : derivOK L D = true) :
    ∀ n, 0 < n → n < 64 → ∃ b ∈ L, ∃ n' < n, b ^^^ n' = n := by
  intro n hn0 hn64
  have hi : n - 1 < 63 := by omega
  have hc := List.all_eq_true.1 h (n - 1) (List.mem_range.2 hi)
  have hc' := Bool.and_eq_true_iff.mp hc
  have hc'' := Bool.and_eq_true_iff.mp hc'.1
  refine ⟨(D.getD (n - 1) (0, 0)).1, List.contains_iff_mem.mp hc''.1,
    (D.getD (n - 1) (0, 0)).2, ?_, ?_⟩
  · have hlt := of_decide_eq_true hc''.2
    omega
  · have hxor := beq_iff_eq.mp hc'.2
    omega

theorem irreducible_of_two_orbits64 (hT : tab64OK tab = true) {M : Subgroup S24}
    (hEM : tab64Sub tab hT ≤ M) {v₁ v₂ : ℕ} {L₁ L₂ : List ℕ} {D₁ : List (ℕ × ℕ)}
    (h1 : ∀ b ∈ L₁, b < 64 ∧ ∃ g ∈ M, g * tab64Perm tab v₁ * g⁻¹ = tab64Perm tab b)
    (h2 : ∀ b ∈ L₂, b < 64 ∧ ∃ g ∈ M, g * tab64Perm tab v₂ * g⁻¹ = tab64Perm tab b)
    (hcover : ∀ n, 0 < n → n < 64 → n ∈ L₁ ∨ n ∈ L₂)
    (hD₁ : derivOK L₁ D₁ = true)
    (hlink : L₂.any (fun b => L₂.any fun b' => L₁.contains (b ^^^ b')) = true) :
    ∀ W : Subgroup S24, W ≤ tab64Sub tab hT → W ≠ ⊥ →
      (∀ g ∈ M, W.map (MulAut.conj g).toMonoidHom = W) → W = tab64Sub tab hT := by
  intro W hWle hWne hWinv
  obtain ⟨w, hwne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWne
  have hwne' : (w : S24) ≠ 1 := fun h => hwne (Subtype.ext h)
  obtain ⟨n, hn, heq⟩ := hWle w.2
  have hn0 : n ≠ 0 := by
    intro h
    exact hwne' (by rw [heq, h, tab64Perm_zero hT])
  have hwn : tab64Perm tab n ∈ W := heq ▸ w.2
  have hmem_conj : ∀ g ∈ M, ∀ x ∈ W, g * x * g⁻¹ ∈ W := by
    intro g hg x hx
    have h := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx
    rw [hWinv g hg] at h
    simpa [MulAut.conj_apply] using h
  have key : ∀ (v : ℕ) (L : List ℕ) (D : List (ℕ × ℕ)),
      (∀ b ∈ L, b < 64 ∧ ∃ g ∈ M, g * tab64Perm tab v * g⁻¹ = tab64Perm tab b) →
      derivOK L D = true → tab64Perm tab v ∈ W →
      ∀ m < 64, tab64Perm tab m ∈ W := by
    intro v L D hL hD hv m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · rw [hm0, tab64Perm_zero hT]
        exact W.one_mem
      · obtain ⟨b, hbL, n', hn'lt, hxor⟩ := exists_deriv_of_derivOK hD m hmpos hm
        have hb64 : b < 64 := (hL b hbL).1
        have hn'64 : n' < 64 := hn'lt.trans hm
        have hbW : tab64Perm tab b ∈ W := by
          obtain ⟨g, hgM, hgconj⟩ := (hL b hbL).2
          have h := hmem_conj g hgM (tab64Perm tab v) hv
          rwa [hgconj] at h
        have hnW : tab64Perm tab n' ∈ W := ih n' hn'lt hn'64
        have hmul : tab64Perm tab m = tab64Perm tab b * tab64Perm tab n' := by
          rw [← hxor, ← tab64Perm_mul hT hb64 hn'64]
        rw [hmul]
        exact W.mul_mem hbW hnW
  have hall : ∀ m < 64, tab64Perm tab m ∈ W := by
    rcases hcover n (Nat.pos_of_ne_zero hn0) hn with hnL₁ | hnL₂
    · have hv₁W : tab64Perm tab v₁ ∈ W := by
        obtain ⟨g, hgM, hgconj⟩ := (h1 n hnL₁).2
        have h : g⁻¹ * tab64Perm tab n * g ∈ W := hmem_conj g⁻¹ (M.inv_mem hgM) _ hwn
        have h2 : g⁻¹ * tab64Perm tab n * g = tab64Perm tab v₁ := by
          rw [← hgconj]; group
        rwa [h2] at h
      exact key v₁ L₁ D₁ h1 hD₁ hv₁W
    · have hv₂W : tab64Perm tab v₂ ∈ W := by
        obtain ⟨g, hgM, hgconj⟩ := (h2 n hnL₂).2
        have h : g⁻¹ * tab64Perm tab n * g ∈ W := hmem_conj g⁻¹ (M.inv_mem hgM) _ hwn
        have h2 : g⁻¹ * tab64Perm tab n * g = tab64Perm tab v₂ := by
          rw [← hgconj]; group
        rwa [h2] at h
      have hL₂W : ∀ b ∈ L₂, tab64Perm tab b ∈ W := by
        intro b hb
        obtain ⟨g, hgM, hgconj⟩ := (h2 b hb).2
        have h := hmem_conj g hgM _ hv₂W
        rwa [hgconj] at h
      obtain ⟨b, hb, hrest⟩ := List.any_eq_true.1 hlink
      obtain ⟨b', hb', hc⟩ := List.any_eq_true.1 hrest
      have hcL₁ : (b ^^^ b') ∈ L₁ := List.contains_iff_mem.mp hc
      have hcW : tab64Perm tab (b ^^^ b') ∈ W := by
        rw [← tab64Perm_mul hT (h2 b hb).1 (h2 b' hb').1]
        exact W.mul_mem (hL₂W b hb) (hL₂W b' hb')
      have hv₁W : tab64Perm tab v₁ ∈ W := by
        obtain ⟨g, hgM, hgconj⟩ := (h1 _ hcL₁).2
        have h : g⁻¹ * tab64Perm tab (b ^^^ b') * g ∈ W := hmem_conj g⁻¹ (M.inv_mem hgM) _ hcW
        have h2 : g⁻¹ * tab64Perm tab (b ^^^ b') * g = tab64Perm tab v₁ := by
          rw [← hgconj]; group
        rwa [h2] at h
      exact key v₁ L₁ D₁ h1 hD₁ hv₁W
  refine le_antisymm hWle ?_
  intro x hx
  obtain ⟨m, hm, rfl⟩ := hx
  exact hall m hm

end CFSG.Quasithin.AppendixH.H14
