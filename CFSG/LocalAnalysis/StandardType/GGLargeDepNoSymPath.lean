module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.StandardType

private lemma l04fPM_orderOf_swap_mul_swap_three {α : Type*} [Fintype α] [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    orderOf (Equiv.swap a b * Equiv.swap a c) = 3 :=
  (Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc).orderOf

private lemma l04fPM_not_commute_swap_swap_same {α : Type*} [Fintype α] [DecidableEq α]
    {a b d : α} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    ¬ Commute (Equiv.swap a b) (Equiv.swap a d) := by
  intro hcomm
  have h3 : orderOf (Equiv.swap a b * Equiv.swap a d) = 3 :=
    (Equiv.Perm.isThreeCycle_swap_mul_swap_same hab had hbd).orderOf
  have h2 : (Equiv.swap a b * Equiv.swap a d) ^ 2 = 1 := by
    rw [hcomm.mul_pow 2, pow_two, pow_two, Equiv.swap_mul_self, Equiv.swap_mul_self, mul_one]
  have hdvd : orderOf (Equiv.swap a b * Equiv.swap a d) ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr h2
  rw [h3] at hdvd
  omega

private lemma l04fPM_nodup_four {α : Type*} [DecidableEq α] (a b c d : α)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    [a, b, c, d].Nodup := by
  refine List.nodup_cons.mpr
    ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_nil⟩⟩⟩⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro (h | h | h)
    · exact hab h
    · exact hac h
    · exact had h
  · simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro (h | h)
    · exact hbc h
    · exact hbd h
  · simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro h
    exact hcd h
  · simp

private lemma l04fPM_notMem_of_disjoint_swap {α : Type*} [Fintype α] [DecidableEq α]
    {x y c d : α} (hxy : x ≠ y) (hcd : c ≠ d)
    (h : Equiv.Perm.Disjoint (Equiv.swap x y) (Equiv.swap c d)) :
    c ≠ x ∧ c ≠ y ∧ d ≠ x ∧ d ≠ y := by
  rw [Equiv.Perm.disjoint_iff_disjoint_support, Equiv.Perm.support_swap hxy,
    Equiv.Perm.support_swap hcd, Finset.disjoint_left] at h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hh
  · exact (h (a := c) (by simp [hh]) (by simp [hcd]))
  · exact (h (a := c) (by simp [hh]) (by simp [hcd]))
  · exact (h (a := d) (by simp [hh]) (by simp))
  · exact (h (a := d) (by simp [hh]) (by simp))

private lemma l04fPM_disjoint_of_commute_ne {α : Type*} [Fintype α] [DecidableEq α]
    {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d)
    (hcomm : Commute (Equiv.swap a b) (Equiv.swap c d))
    (hne : Equiv.swap a b ≠ Equiv.swap c d) :
    Equiv.Perm.Disjoint (Equiv.swap a b) (Equiv.swap c d) := by
  have hac : a ≠ c := by
    rintro rfl
    by_cases hbd : b = d
    · exact hne (by rw [hbd])
    · exact l04fPM_not_commute_swap_swap_same (a := a) (b := b) (d := d) hab hcd hbd hcomm
  have had : a ≠ d := by
    rintro rfl
    by_cases hbc : b = c
    · exact hne (by rw [hbc, Equiv.swap_comm])
    · have hcomm' : Commute (Equiv.swap a b) (Equiv.swap a c) := by
        rwa [Equiv.swap_comm c a] at hcomm
      exact l04fPM_not_commute_swap_swap_same (a := a) (b := b) (d := c) hab hcd.symm hbc hcomm'
  have hbc : b ≠ c := by
    rintro rfl
    by_cases had' : a = d
    · exact hne (by rw [had', Equiv.swap_comm])
    · have hcomm' : Commute (Equiv.swap b a) (Equiv.swap b d) := by
        rwa [Equiv.swap_comm a b] at hcomm
      exact l04fPM_not_commute_swap_swap_same (a := b) (b := a) (d := d)
        (Ne.symm hab) hcd had' hcomm'
  have hbd : b ≠ d := by
    rintro rfl
    by_cases hac' : a = c
    · exact hne (by rw [hac'])
    · have hcomm' : Commute (Equiv.swap b a) (Equiv.swap b c) := by
        rw [Equiv.swap_comm a b, Equiv.swap_comm c b] at hcomm
        exact hcomm
      exact l04fPM_not_commute_swap_swap_same (a := b) (b := a) (d := c)
        (Ne.symm hab) hcd.symm hac' hcomm'
  rw [Equiv.Perm.disjoint_iff_disjoint_support, Equiv.Perm.support_swap hab,
    Equiv.Perm.support_swap hcd, Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
  rcases hx with rfl | rfl <;> rcases hx' with h | h
  · exact hac h
  · exact had h
  · exact hbc h
  · exact hbd h

private lemma l04fPM_share_of_order_three {α : Type*} [Fintype α] [DecidableEq α]
    {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d)
    (h3 : orderOf (Equiv.swap a b * Equiv.swap c d) = 3) :
    a = c ∨ a = d ∨ b = c ∨ b = d := by
  by_contra h
  push Not at h
  obtain ⟨hac, had, hbc, hbd⟩ := h
  have hnd := l04fPM_nodup_four a b c d hab hac had hbc hbd hcd
  have h2 : (Equiv.swap a b * Equiv.swap c d) ^ 2 = 1 := by
    rw [(Equiv.Perm.disjoint_swap_swap hnd).commute.mul_pow 2, pow_two, pow_two,
      Equiv.swap_mul_self, Equiv.swap_mul_self, mul_one]
  have hdvd : orderOf (Equiv.swap a b * Equiv.swap c d) ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr h2
  rw [h3] at hdvd
  omega

private lemma l04fPM_exists_triple_of_order_three {α : Type*} [Fintype α] [DecidableEq α]
    {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d)
    (h3 : orderOf (Equiv.swap a b * Equiv.swap c d) = 3) :
    ∃ u0 u1 u2 : α, u0 ≠ u1 ∧ u1 ≠ u2 ∧ u0 ≠ u2 ∧
      Equiv.swap a b = Equiv.swap u0 u1 ∧ Equiv.swap c d = Equiv.swap u1 u2 := by
  have hshared := l04fPM_share_of_order_three hab hcd h3
  have hnb : ¬ (a = c ∧ b = d) ∧ ¬ (a = d ∧ b = c) := by
    constructor
    · rintro ⟨hac, hbd⟩
      have h1 : Equiv.swap a b * Equiv.swap c d = 1 := by rw [← hac, ← hbd, Equiv.swap_mul_self]
      rw [h1, orderOf_one] at h3
      omega
    · rintro ⟨had, hbc⟩
      have h1 : Equiv.swap a b * Equiv.swap c d = 1 := by
        rw [← hbc, ← had, Equiv.swap_comm b a, Equiv.swap_mul_self]
      rw [h1, orderOf_one] at h3
      omega
  rcases hshared with hac | had | hbc | hbd
  · exact ⟨b, a, d, hab.symm, fun h => hcd (hac.symm.trans h), fun h => hnb.1 ⟨hac, h⟩,
      Equiv.swap_comm a b, by rw [← hac]⟩
  · exact ⟨b, a, c, hab.symm, fun h => hcd (h.symm.trans had), fun h => hnb.2 ⟨had, h⟩,
      Equiv.swap_comm a b, by rw [← had, Equiv.swap_comm]⟩
  · exact ⟨a, b, d, hab, fun h => hcd (hbc ▸ h), fun h => hnb.2 ⟨h, hbc⟩,
      rfl, by rw [← hbc]⟩
  · exact ⟨a, b, c, hab, fun h => hcd (h.symm.trans hbd), fun h => hnb.1 ⟨h, hbd⟩,
      rfl, by rw [← hbd, Equiv.swap_comm]⟩

theorem ggLargeDep_perm_path {m n : ℕ} (hm : 2 ≤ m) (hn : n = m + 2) (τ : Fin m → Equiv.Perm (Fin n))
    (hswap : ∀ i, ∃ a b, a ≠ b ∧ τ i = Equiv.swap a b)
    (hadj : ∀ i j : Fin m, (i : ℕ) + 1 = (j : ℕ) → orderOf (τ i * τ j) = 3)
    (hfar : ∀ i j : Fin m, (i : ℕ) + 2 ≤ (j : ℕ) → Commute (τ i) (τ j) ∧ τ i ≠ τ j) :
    ∃ t : Equiv.Perm (Fin n), (∃ a b, a ≠ b ∧ t = Equiv.swap a b) ∧
      (∀ i : Fin m, (i : ℕ) + 2 ≤ m → Commute t (τ i) ∧ t ≠ τ i) ∧
      ∀ j : Fin m, (j : ℕ) + 1 = m → orderOf (t * τ j) = 3 := by
  classical
  subst hn
  let P : (k : ℕ) → 2 ≤ k → Prop := fun k _ =>
    ∀ (_hkm : k ≤ m), ∃ u : Fin (k+1) → Fin (m+2), Function.Injective u ∧
      ∀ i : Fin k, τ ⟨i.val, by omega⟩ = Equiv.swap (u i.castSucc) (u i.succ)
  have hbase : P 2 (by omega) := by
    intro _
    obtain ⟨a, b, hab, hτ0⟩ := hswap ⟨0, by omega⟩
    obtain ⟨c, d, hcd, hτ1⟩ := hswap ⟨1, by omega⟩
    have h3 : orderOf (Equiv.swap a b * Equiv.swap c d) = 3 := by
      have h := hadj ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)
      rwa [hτ0, hτ1] at h
    obtain ⟨u0, u1, u2, h01, h12, h02, hsw0, hsw1⟩ :=
      l04fPM_exists_triple_of_order_three hab hcd h3
    let u : Fin 3 → Fin (m+2) := ![u0, u1, u2]
    refine ⟨u, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [u]
    · intro i
      fin_cases i <;> simp_all [u]
  have hstep : ∀ k (hk2 : 2 ≤ k), P k hk2 → P (k+1) (by omega) := by
    intro k hk2 ih hk1m
    have hkm : k ≤ m := by omega
    obtain ⟨u, huinj, hupath⟩ := ih hkm
    have hklt : k < m := by omega
    obtain ⟨c, d, hcd, hτk⟩ := hswap ⟨k, hklt⟩
    let j : Fin k := ⟨k-1, by omega⟩
    have hjval : (j : ℕ) = k - 1 := rfl
    let a : Fin (m+2) := u j.castSucc
    let b : Fin (m+2) := u (Fin.last k)
    have hjb : u j.succ = b := by
      show u j.succ = u (Fin.last k)
      exact congrArg u (Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega))
    have hplast : τ ⟨j.val, by omega⟩ = Equiv.swap a b := by
      rw [hupath j, hjb]
    have h3 : orderOf (Equiv.swap a b * Equiv.swap c d) = 3 := by
      have h := hadj ⟨j.val, by omega⟩ ⟨k, hklt⟩ (by simp only; omega)
      rw [hplast, hτk] at h
      exact h
    have huv : a ≠ b := by
      intro h
      have hfin : j.castSucc = Fin.last k := huinj h
      have hv := congrArg Fin.val hfin
      simp only [Fin.val_castSucc, Fin.val_last] at hv
      omega
    have hshared := l04fPM_share_of_order_three huv hcd h3
    let i2 : Fin k := ⟨k-2, by omega⟩
    have hi2 : i2.val + 2 ≤ k := by simp only [i2]; omega
    have hfar2 := hfar ⟨i2.val, by omega⟩ ⟨k, hklt⟩ (by simpa using hi2)
    obtain ⟨hcomm2, hne2⟩ := hfar2
    have hp2 : τ ⟨i2.val, by omega⟩ = Equiv.swap (u i2.castSucc) (u i2.succ) := hupath i2
    rw [hp2, hτk] at hcomm2 hne2
    have huv2 : u i2.castSucc ≠ u i2.succ := by
      intro h
      have hfin : i2.castSucc = i2.succ := huinj h
      have hv := congrArg Fin.val hfin
      simp only [Fin.val_castSucc, Fin.val_succ] at hv
      omega
    obtain ⟨_, hc_b2, _, hd_b2⟩ :=
      l04fPM_notMem_of_disjoint_swap huv2 hcd
        (l04fPM_disjoint_of_commute_ne huv2 hcd hcomm2 hne2)
    have hu_a : u i2.succ = a := by
      show u i2.succ = u j.castSucc
      exact congrArg u (Fin.ext (by simp only [i2, j, Fin.val_succ, Fin.val_castSucc]; omega))
    have hca : c ≠ a := fun h => hc_b2 (h.trans hu_a.symm)
    have hda : d ≠ a := fun h => hd_b2 (h.trans hu_a.symm)
    have hbc_or_bd : b = c ∨ b = d := by
      rcases hshared with h | h | h | h
      · exact absurd h.symm hca
      · exact absurd h.symm hda
      · exact Or.inl h
      · exact Or.inr h
    let x : Fin (m+2) := if c = b then d else c
    have hbx : Equiv.swap c d = Equiv.swap b x := by
      by_cases hcb : c = b
      · have hxd : x = d := by simp [x, hcb]
        rw [hxd, hcb]
      · have hbd' : b = d := by
          rcases hbc_or_bd with hbc | hbd
          · exact absurd hbc.symm hcb
          · exact hbd
        have hxc : x = c := by simp [x, hcb]
        rw [hxc, ← hbd', Equiv.swap_comm]
    have hxb : x ≠ b := by
      by_cases hcb : c = b
      · have hxd : x = d := by simp [x, hcb]
        rw [hxd]
        intro hdb
        exact hcd (hdb.trans hcb.symm).symm
      · have hxc : x = c := by simp [x, hcb]
        rw [hxc]
        exact hcb
    have havoid : ∀ i : Fin k, i.val + 2 ≤ k →
        c ≠ u i.castSucc ∧ c ≠ u i.succ ∧ d ≠ u i.castSucc ∧ d ≠ u i.succ := by
      intro i hi
      have hfar_i := hfar ⟨i.val, by omega⟩ ⟨k, hklt⟩ (by simpa using hi)
      obtain ⟨hcomm_i, hne_i⟩ := hfar_i
      have hpi := hupath i
      rw [hpi, hτk] at hcomm_i hne_i
      have huv_i : u i.castSucc ≠ u i.succ := by
        intro h
        have hfin : i.castSucc = i.succ := huinj h
        have hv := congrArg Fin.val hfin
        simp only [Fin.val_castSucc, Fin.val_succ] at hv
        omega
      exact l04fPM_notMem_of_disjoint_swap huv_i hcd
        (l04fPM_disjoint_of_commute_ne huv_i hcd hcomm_i hne_i)
    have hprefix : ∀ jj : Fin (k+1), jj.val < k → u jj ≠ c ∧ u jj ≠ d := by
      intro jj hj
      by_cases hcase : jj.val + 2 ≤ k
      · let i : Fin k := ⟨jj.val, hj⟩
        have hi : i.val + 2 ≤ k := hcase
        obtain ⟨h1, _, h3', _⟩ := havoid i hi
        have hjc : u i.castSucc = u jj := congrArg u (Fin.ext rfl)
        exact ⟨fun h => h1 (hjc.trans h).symm, fun h => h3' (hjc.trans h).symm⟩
      · have hjval' : jj.val = k - 1 := by omega
        let i : Fin k := ⟨k-2, by omega⟩
        have hi : i.val + 2 ≤ k := by simp only [i]; omega
        obtain ⟨_, h2, _, h4⟩ := havoid i hi
        have hjs : u i.succ = u jj :=
          congrArg u (Fin.ext (by simp only [i, Fin.val_succ]; omega))
        exact ⟨fun h => h2 (hjs.trans h).symm, fun h => h4 (hjs.trans h).symm⟩
    have hxrange : x ∉ Set.range u := by
      rintro ⟨jj, hjjx⟩
      by_cases hjlast : jj.val = k
      · have hjb' : u jj = b := by
          have hjeq : jj = j.succ := Fin.ext (by simp only [Fin.val_succ]; omega)
          rw [hjeq]
          exact hjb
        exact hxb (hjjx.symm.trans hjb')
      · have hjlt : jj.val < k := by omega
        obtain ⟨hcjj, hdjj⟩ := hprefix jj hjlt
        by_cases hcb : c = b
        · have hxc : x = d := by simp [x, hcb]
          exact hdjj (hjjx.trans hxc)
        · have hxc : x = c := by simp [x, hcb]
          exact hcjj (hjjx.trans hxc)
    let u' : Fin (k+2) → Fin (m+2) := Fin.snoc (α := fun _ => Fin (m+2)) u x
    have hu'inj : Function.Injective u' := by
      rw [Fin.snoc_injective_iff]
      exact ⟨huinj, hxrange⟩
    have hτk' : τ ⟨k, hklt⟩ = Equiv.swap b x := by rw [hτk, hbx]
    have hupath' : ∀ i : Fin (k+1),
        τ ⟨i.val, by omega⟩ = Equiv.swap (u' i.castSucc) (u' i.succ) := by
      intro i
      by_cases hi : i.val + 1 ≤ k
      · have hi_lt : i.val < k := by omega
        let i' : Fin k := ⟨i.val, hi_lt⟩
        have hpi := hupath i'
        have h1 : u' i.castSucc = u i'.castSucc := by
          rw [show i.castSucc = Fin.castSucc i'.castSucc from Fin.ext rfl,
            show u' = Fin.snoc (α := fun _ => Fin (m+2)) u x from rfl, Fin.snoc_castSucc]
        have h2 : u' i.succ = u i'.succ := by
          rw [show i.succ = Fin.castSucc i'.succ from Fin.ext rfl,
            show u' = Fin.snoc (α := fun _ => Fin (m+2)) u x from rfl, Fin.snoc_castSucc]
        rw [hpi, h1, h2]
      · have hival : i.val = k := by omega
        have hb' : u' i.castSucc = b := by
          rw [show i.castSucc = Fin.castSucc (Fin.last k) from Fin.ext (by simp [Fin.last, hival]),
            show u' = Fin.snoc (α := fun _ => Fin (m+2)) u x from rfl, Fin.snoc_castSucc]
        have hx' : u' i.succ = x := by
          rw [show i.succ = Fin.last (k+1) from Fin.ext (by simp [Fin.last, hival]),
            show u' = Fin.snoc (α := fun _ => Fin (m+2)) u x from rfl, Fin.snoc_last]
        rw [show τ ⟨i.val, by omega⟩ = τ ⟨k, hklt⟩ from congrArg τ (Fin.ext hival),
          hτk', hb', hx']
    exact ⟨u', hu'inj, hupath'⟩
  have hmdata : P m hm := Nat.le_induction (P := P) hbase hstep m hm
  obtain ⟨u, huinj, hupath⟩ := hmdata le_rfl
  have hcard : (Finset.univ.image u).card < (Finset.univ : Finset (Fin (m+2))).card := by
    rw [Finset.card_image_of_injective _ huinj]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨w, -, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hwrange : ∀ i, u i ≠ w := by
    intro i hi
    exact hw (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
  let t : Equiv.Perm (Fin (m+2)) := Equiv.swap (u (Fin.last m)) w
  have hut : u (Fin.last m) ≠ w := hwrange (Fin.last m)
  refine ⟨t, ⟨u (Fin.last m), w, hut, rfl⟩, ?_, ?_⟩
  · intro i hi
    have hpi := hupath i
    have his : u i.castSucc ≠ u i.succ := by
      intro h
      have hfin : i.castSucc = i.succ := huinj h
      have hv := congrArg Fin.val hfin
      simp only [Fin.val_castSucc, Fin.val_succ] at hv
      omega
    have hli : u (Fin.last m) ≠ u i.castSucc := by
      intro h
      have hfin : Fin.last m = i.castSucc := huinj h
      have hv := congrArg Fin.val hfin
      simp only [Fin.val_last, Fin.val_castSucc] at hv
      omega
    have hls : u (Fin.last m) ≠ u i.succ := by
      intro h
      have hfin : Fin.last m = i.succ := huinj h
      have hv := congrArg Fin.val hfin
      simp only [Fin.val_last, Fin.val_succ] at hv
      omega
    have hwi : w ≠ u i.castSucc := (hwrange i.castSucc).symm
    have hws : w ≠ u i.succ := (hwrange i.succ).symm
    constructor
    · rw [hpi]
      exact (Equiv.Perm.disjoint_swap_swap
        (l04fPM_nodup_four _ _ _ _ hut hli hls hwi hws his)).commute
    · intro h
      have hw1 : t w = u (Fin.last m) := by simp [t]
      have hw2 : τ i w = w := by
        rw [hpi, Equiv.swap_apply_of_ne_of_ne (hwrange i.castSucc).symm (hwrange i.succ).symm]
      have hEq : t w = τ i w := congrArg (fun σ : Equiv.Perm (Fin (m+2)) => σ w) h
      rw [hw1, hw2] at hEq
      exact hut hEq
  · intro jj hj
    have hpj := hupath jj
    have huju : u jj.succ = u (Fin.last m) := by
      show u jj.succ = u (Fin.last m)
      exact congrArg u (Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega))
    have hjc : u (Fin.last m) ≠ u jj.castSucc := by
      intro h
      have hfin : Fin.last m = jj.castSucc := huinj h
      have hv := congrArg Fin.val hfin
      simp only [Fin.val_last, Fin.val_castSucc] at hv
      omega
    have hwc : w ≠ u jj.castSucc := (hwrange jj.castSucc).symm
    rw [hpj, huju]
    rw [show t = Equiv.swap (u (Fin.last m)) w from rfl,
      Equiv.swap_comm (u jj.castSucc) (u (Fin.last m))]
    exact l04fPM_orderOf_swap_mul_swap_three hut hjc hwc

end CFSG.StandardType

end
