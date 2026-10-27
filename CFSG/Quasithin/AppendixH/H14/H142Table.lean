module

public import CFSG.Quasithin.AppendixH.H14.H142Arr

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.Quasithin.H.Mathieu CFSG.ASVolI.ChH CFSG.Monster.Code CFSG.Open

@[expose] def tabOK (tab : Array (Array ℕ)) : Bool :=
  decide (tab.size = 16) && (tab[0]! == id24) &&
    (List.range 16).all fun n => inAutOK tab[n]! &&
      (List.range 16).all fun m => (comp24 tab[n]! tab[m]! == tab[n ^^^ m]!) &&
        ((tab[n]! == tab[m]!) == (n == m))

theorem tabOK_spec {tab : Array (Array ℕ)} (h : tabOK tab = true) :
    tab[0]! = id24 ∧ ∀ n < 16, inAutOK tab[n]! = true ∧
      ∀ m < 16, comp24 tab[n]! tab[m]! = tab[n ^^^ m]! ∧ (tab[n]! = tab[m]! ↔ n = m) := by
  unfold tabOK at h
  have hAB := Bool.and_eq_true_iff.mp h
  have h0 : (tab[0]! == id24) = true := (Bool.and_eq_true_iff.mp hAB.1).2
  have hn : ((List.range 16).all fun n => inAutOK tab[n]! &&
      (List.range 16).all fun m => (comp24 tab[n]! tab[m]! == tab[n ^^^ m]!) &&
        ((tab[n]! == tab[m]!) == (n == m))) = true := hAB.2
  refine ⟨beq_iff_eq.mp h0, fun n hn' => ?_⟩
  have hc := List.all_eq_true.1 hn n (List.mem_range.2 hn')
  have hc' := Bool.and_eq_true_iff.mp hc
  refine ⟨beq_iff_eq.mp hc'.1, fun m hm' => ?_⟩
  have hcm := List.all_eq_true.1 hc'.2 m (List.mem_range.2 hm')
  have hcm' := Bool.and_eq_true_iff.mp hcm
  refine ⟨beq_iff_eq.mp hcm'.1, ?_⟩
  rw [← beq_iff_eq (a := tab[n]!) (b := tab[m]!), ← beq_iff_eq (a := n) (b := m),
    beq_iff_eq.mp hcm'.2]

theorem xor_lt_sixteen {n m : ℕ} (hn : n < 16) (hm : m < 16) : n ^^^ m < 16 := by
  have hn' : n < 2 ^ 4 := by rw [show (2 : ℕ) ^ 4 = 16 by norm_num]; exact hn
  have hm' : m < 2 ^ 4 := by rw [show (2 : ℕ) ^ 4 = 16 by norm_num]; exact hm
  have h := Nat.xor_lt_two_pow hn' hm'
  rwa [show (2 : ℕ) ^ 4 = 16 by norm_num] at h

@[expose] noncomputable def tabPerm (tab : Array (Array ℕ)) (n : ℕ) : S24 := permOfArrD tab[n]!

variable {tab : Array (Array ℕ)}

theorem hasArr_tabPerm (hT : tabOK tab = true) {n : ℕ} (hn : n < 16) :
    HasArr (tabPerm tab n) tab[n]! :=
  hasArr_permOfArrD ((tabOK_spec hT).2 n hn).1

theorem tab_size_lt (hT : tabOK tab = true) {n : ℕ} (hn : n < 16) : (tab[n]!).size = 24 := by
  have h' : comp24 tab[n]! tab[0]! = tab[n]! := by
    simpa using ((tabOK_spec hT).2 n hn).2 0 (by norm_num) |>.1
  rw [← h']
  simp [comp24]

theorem tabPerm_zero (hT : tabOK tab = true) : tabPerm tab 0 = 1 := by
  exact hasArr_unique (by simpa [(tabOK_spec hT).1] using hasArr_tabPerm hT (n := 0) (by norm_num))
    hasArr_one

theorem tabPerm_mul (hT : tabOK tab = true) {n m : ℕ} (hn : n < 16) (hm : m < 16) :
    tabPerm tab n * tabPerm tab m = tabPerm tab (n ^^^ m) := by
  refine hasArr_unique ?_ (hasArr_tabPerm hT (xor_lt_sixteen hn hm))
  have h := hasArr_mul (hasArr_tabPerm hT hn) (hasArr_tabPerm hT hm)
  rwa [((tabOK_spec hT).2 n hn).2 m hm |>.1] at h

theorem tabPerm_mul_self (hT : tabOK tab = true) {n : ℕ} (hn : n < 16) :
    tabPerm tab n * tabPerm tab n = 1 := by
  rw [tabPerm_mul hT hn hn, Nat.xor_self, tabPerm_zero hT]

theorem tabPerm_inj (hT : tabOK tab = true) {n m : ℕ} (hn : n < 16) (hm : m < 16)
    (h : tabPerm tab n = tabPerm tab m) : n = m := by
  have hnm_lt : n ^^^ m < 16 := xor_lt_sixteen hn hm
  have h1 : tabPerm tab (n ^^^ m) = 1 := by
    have hsq : tabPerm tab n * tabPerm tab m = 1 := by rw [h, tabPerm_mul_self hT hm]
    rw [← tabPerm_mul hT hn hm, hsq]
  have harr : HasArr (tabPerm tab (n ^^^ m)) tab[n ^^^ m]! := hasArr_tabPerm hT hnm_lt
  have harr1 : HasArr (1 : S24) tab[n ^^^ m]! := by rwa [h1] at harr
  have heq : tab[n ^^^ m]! = id24 := by
    refine Array.ext ?_ fun i hi₁ hi₂ => ?_
    · rw [tab_size_lt hT hnm_lt]
      simp [id24]
    · have hi24 : i < 24 := by rw [tab_size_lt hT hnm_lt] at hi₁; exact hi₁
      rw [← getElem!_pos (tab[n ^^^ m]!) i hi₁, ← getElem!_pos id24 i hi₂]
      exact (harr1 ⟨i, hi24⟩).symm.trans (hasArr_one ⟨i, hi24⟩)
  have hinj := ((tabOK_spec hT).2 (n ^^^ m) hnm_lt).2 0 (by norm_num) |>.2
  have hzero : n ^^^ m = 0 := hinj.1 (by rw [heq, (tabOK_spec hT).1])
  exact xor_eq_zero_iff.mp hzero

theorem tabPerm_comm (hT : tabOK tab = true) {n m : ℕ} (hn : n < 16) (hm : m < 16) :
    tabPerm tab n * tabPerm tab m = tabPerm tab m * tabPerm tab n := by
  rw [tabPerm_mul hT hn hm, tabPerm_mul hT hm hn, Nat.xor_comm]

@[expose] noncomputable def tabSub (tab : Array (Array ℕ)) (hT : tabOK tab = true) : Subgroup S24 where
  carrier := {x | ∃ n < 16, x = tabPerm tab n}
  mul_mem' := by
    rintro x y ⟨n, hn, rfl⟩ ⟨m, hm, rfl⟩
    exact ⟨n ^^^ m, xor_lt_sixteen hn hm, tabPerm_mul hT hn hm⟩
  one_mem' := ⟨0, by norm_num, (tabPerm_zero hT).symm⟩
  inv_mem' := by
    rintro x ⟨n, hn, rfl⟩
    exact ⟨n, hn, inv_eq_of_mul_eq_one_right (tabPerm_mul_self hT hn)⟩

theorem mem_tabSub (hT : tabOK tab = true) {x : S24} :
    x ∈ tabSub tab hT ↔ ∃ n < 16, x = tabPerm tab n := Iff.rfl

theorem tabPerm_mem_tabSub (hT : tabOK tab = true) {n : ℕ} (hn : n < 16) :
    tabPerm tab n ∈ tabSub tab hT :=
  ⟨n, hn, rfl⟩

theorem card_tabSub (hT : tabOK tab = true) : Nat.card ↥(tabSub tab hT) = 16 := by
  let f : Fin 16 → ↥(tabSub tab hT) := fun n => ⟨tabPerm tab n, tabPerm_mem_tabSub hT n.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro n m h
      have h' : tabPerm tab (n : ℕ) = tabPerm tab (m : ℕ) := congrArg Subtype.val h
      exact Fin.ext (tabPerm_inj hT n.2 m.2 h')
    · intro y
      obtain ⟨n, hn, heq⟩ := y.2
      exact ⟨⟨n, hn⟩, Subtype.ext heq.symm⟩
  calc Nat.card ↥(tabSub tab hT) = Nat.card (Fin 16) :=
        (Nat.card_congr (Equiv.ofBijective f hf)).symm
    _ = 16 := Nat.card_fin 16

theorem isElemAbelian_tabSub (hT : tabOK tab = true) : IsElemAbelian 2 (tabSub tab hT) := by
  rw [IsElemAbelian, isMulCommutative_iff]
  refine ⟨?_, ?_⟩
  · intro x y
    obtain ⟨n, hn, heq⟩ := x.2
    obtain ⟨m, hm, heq'⟩ := y.2
    exact Subtype.ext (by
      show (x : S24) * (y : S24) = (y : S24) * (x : S24)
      rw [heq, heq']
      exact tabPerm_comm hT hn hm)
  · intro x hx
    obtain ⟨n, hn, heq⟩ := hx
    rw [heq]
    simpa [pow_two] using tabPerm_mul_self hT hn

theorem isPGroup_tabSub (hT : tabOK tab = true) : IsPGroup 2 (tabSub tab hT) :=
  IsPGroup.of_card (n := 4) (by rw [card_tabSub hT]; norm_num)

theorem tabSub_ne_bot (hT : tabOK tab = true) : tabSub tab hT ≠ ⊥ := by
  intro hbot
  have hcard := card_tabSub hT
  rw [hbot, Subgroup.card_bot] at hcard
  norm_num at hcard

@[expose] def tabIdx (tab : Array (Array ℕ)) (b : Array ℕ) : ℕ :=
  ((List.range 16).find? fun m => tab[m]! == b).getD 16

theorem tabIdx_spec {b : Array ℕ} (hm : tabIdx tab b < 16) : tab[tabIdx tab b]! = b := by
  unfold tabIdx at hm ⊢
  have hne : (List.range 16).find? (fun m => tab[m]! == b) ≠ none := by
    intro hnone
    rw [hnone] at hm
    simp only [Option.getD_none] at hm
    omega
  obtain ⟨m, hfind⟩ := Option.ne_none_iff_exists'.mp hne
  have hsome := List.find?_some hfind
  have hbeq : tab[m]! = b := beq_iff_eq.mp hsome
  have hidx : ((List.range 16).find? (fun m => tab[m]! == b)).getD 16 = m := by
    rw [hfind]; rfl
  rw [hidx]
  exact hbeq

@[expose] def cmap (tab : Array (Array ℕ)) (a : Array ℕ) (n : ℕ) : ℕ :=
  tabIdx tab (conj24 a tab[n]!)

theorem conj_tabPerm (hT : tabOK tab = true) {g : S24} {a : Array ℕ} (hg : HasArr g a)
    (ha : inAutOK a = true) {n : ℕ} (hn : n < 16) (hm : cmap tab a n < 16) :
    g * tabPerm tab n * g⁻¹ = tabPerm tab (cmap tab a n) := by
  have harr : HasArr (g * tabPerm tab n * g⁻¹) (conj24 a tab[n]!) :=
    hasArr_conj hg ha (hasArr_tabPerm hT hn)
  have hentry : tab[cmap tab a n]! = conj24 a tab[n]! := by
    simpa [cmap] using tabIdx_spec (tab := tab) (b := conj24 a tab[n]!)
      (by simpa [cmap] using hm)
  rw [← hentry] at harr
  exact hasArr_unique harr (hasArr_tabPerm hT hm)

@[expose] def vbfsOK (tab : Array (Array ℕ)) (gens : List (Array ℕ)) (n₀ : ℕ)
    (L : List (ℕ × ℕ × ℕ)) : Bool :=
  (List.range L.length).all fun k =>
    if k = 0 then (L.getD 0 (0, 0, 0)).1 == n₀ && decide (n₀ < 16) else
      decide ((L.getD k (0, 0, 0)).2.2 < k) && decide ((L.getD k (0, 0, 0)).2.1 < gens.length) &&
        (L.getD k (0, 0, 0)).1 == cmap tab (gens.getD (L.getD k (0, 0, 0)).2.1 #[])
          (L.getD (L.getD k (0, 0, 0)).2.2 (0, 0, 0)).1 &&
        decide ((L.getD k (0, 0, 0)).1 < 16)

theorem exists_conj_of_vbfs (hT : tabOK tab = true) {M : Subgroup S24} {gens : List (Array ℕ)}
    (hg : ∀ a ∈ gens, inAutOK a = true ∧ ∃ σ ∈ M, HasArr σ a) {n₀ : ℕ}
    {L : List (ℕ × ℕ × ℕ)} (hL : vbfsOK tab gens n₀ L = true) :
    ∀ k < L.length, (L.getD k (0, 0, 0)).1 < 16 ∧
      ∃ g ∈ M, g * tabPerm tab n₀ * g⁻¹ = tabPerm tab (L.getD k (0, 0, 0)).1 := by
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
      have hcmap : cmap tab (gens.getD (L.getD k (0, 0, 0)).2.1 #[])
          (L.getD (L.getD k (0, 0, 0)).2.2 (0, 0, 0)).1 < 16 := by
        rw [← heq]; exact hlt
      have hconj := conj_tabPerm hT hσarr haut hplt hcmap
      have hgrp : σ * g * tabPerm tab n₀ * (σ * g)⁻¹
          = σ * (g * tabPerm tab n₀ * g⁻¹) * σ⁻¹ := by group
      rw [hgrp, hgconj, hconj, heq]

theorem irreducible_of_orbit (hT : tabOK tab = true) {M : Subgroup S24}
    (hEM : tabSub tab hT ≤ M)
    (horb : ∀ n, 0 < n → n < 16 → ∃ g ∈ M, g * tabPerm tab 1 * g⁻¹ = tabPerm tab n) :
    ∀ W : Subgroup S24, W ≤ tabSub tab hT → W ≠ ⊥ →
      (∀ g ∈ M, W.map (MulAut.conj g).toMonoidHom = W) → W = tabSub tab hT := by
  intro W hWle hWne hWinv
  obtain ⟨w, hwne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWne
  have hwne' : (w : S24) ≠ 1 := fun h => hwne (Subtype.ext h)
  obtain ⟨n, hn, heq⟩ := hWle w.2
  have hn0 : n ≠ 0 := by
    intro h
    exact hwne' (by rw [heq, h, tabPerm_zero hT])
  have hwn : tabPerm tab n ∈ W := heq ▸ w.2
  have hmem_conj : ∀ g ∈ M, ∀ x ∈ W, g * x * g⁻¹ ∈ W := by
    intro g hg x hx
    have h := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx
    rw [hWinv g hg] at h
    simpa [MulAut.conj_apply] using h
  have hpsi1 : tabPerm tab 1 ∈ W := by
    obtain ⟨g, hgM, hgconj⟩ := horb n (Nat.pos_of_ne_zero hn0) hn
    have hinv : g⁻¹ * tabPerm tab n * g ∈ W := hmem_conj g⁻¹ (M.inv_mem hgM) _ hwn
    have h2 : g⁻¹ * tabPerm tab n * g = tabPerm tab 1 := by
      rw [← hgconj]; group
    rwa [h2] at hinv
  refine le_antisymm hWle ?_
  intro x hx
  obtain ⟨m, hm, rfl⟩ := hx
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · rw [hm0, tabPerm_zero hT]
    exact W.one_mem
  · obtain ⟨g, hgM, hgconj⟩ := horb m hmpos hm
    have hmW : g * tabPerm tab 1 * g⁻¹ ∈ W := hmem_conj g hgM _ hpsi1
    rwa [hgconj] at hmW

end CFSG.Quasithin.AppendixH.H14
