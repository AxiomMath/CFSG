module

public import CFSG.Quasithin.Background.HMathieuBits
public import CFSG.Quasithin.Background.HMathieuEnum
public import CFSG.Quasithin.Background.HMathieuStd

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.QuasithinUnique.Setup.X1

variable {V : Type*} [CommGroup V] {n : ℕ} {P : Type*} [Group P]

structure ChainAct (c : MaskCoords V n) (aut : P →* MulAut V) (act : P → ℕ → ℕ) : Prop where
  spec : ∀ s, ∀ m < 2 ^ n, aut s (c.vm m) = c.vm (act s m)
  lt : ∀ s, ∀ m < 2 ^ n, act s m < 2 ^ n

@[expose] def IsChainSub (aut : P →* MulAut V) (l : List P) (A : Subgroup (MulAut V)) : Prop :=
  ∀ a, a ∈ A ↔ ∃ s ∈ subprods l, a = aut s

@[expose] def fixMasks (n : ℕ) (act : P → ℕ → ℕ) (l : List P) : List ℕ :=
  (List.range (2 ^ n)).filter fun m => l.all fun s => act s m == m

theorem fix_subprods {aut : P →* MulAut V} {v : V} :
    ∀ {l : List P}, (∀ s ∈ l, aut s v = v) → ∀ t ∈ subprods l, aut t v = v
  | [], _, t, ht => by
    simp only [subprods, List.mem_singleton] at ht
    rw [ht, map_one, MulAut.one_apply]
  | y :: l, h, t, ht => by
    have hl := fix_subprods (l := l) fun s hs => h s (List.mem_cons_of_mem y hs)
    rcases mem_subprods_cons.1 ht with ht | ⟨w, hw, rfl⟩
    · exact hl t ht
    · rw [map_mul, MulAut.mul_apply, hl w hw, h y List.mem_cons_self]

section Chain

variable {c : MaskCoords V n} {aut : P →* MulAut V} {act : P → ℕ → ℕ} {l : List P}
  {A : Subgroup (MulAut V)}

theorem mem_fixV_iff_chain (hA : IsChainSub aut l A) (v : V) :
    v ∈ fixV A ↔ ∀ s ∈ l, aut s v = v := by
  rw [mem_fixV]
  constructor
  · intro h s hs
    exact h _ ((hA _).2 ⟨s, mem_subprods_of_mem hs, rfl⟩)
  · intro h a ha
    obtain ⟨t, ht, rfl⟩ := (hA a).1 ha
    exact fix_subprods h t ht

theorem vm_fix_iff (hc : ChainAct c aut act) (s : P) {m : ℕ} (hm : m < 2 ^ n) :
    aut s (c.vm m) = c.vm m ↔ act s m = m := by
  rw [hc.spec s m hm]
  exact ⟨fun h => c.vm_inj _ _ (hc.lt s m hm) hm h, fun h => by rw [h]⟩

theorem vm_mem_fixV_iff (hc : ChainAct c aut act) (hA : IsChainSub aut l A) {m : ℕ}
    (hm : m < 2 ^ n) : c.vm m ∈ fixV A ↔ (l.all fun s => act s m == m) = true := by
  rw [mem_fixV_iff_chain hA, List.all_eq_true]
  simp only [beq_iff_eq]
  exact forall₂_congr fun s _ => vm_fix_iff hc s hm

theorem card_fixV (hc : ChainAct c aut act) (hA : IsChainSub aut l A) :
    Nat.card (fixV A) = (fixMasks n act l).length :=
  c.card_eq _ _ fun _ hm => vm_mem_fixV_iff hc hA hm

theorem vm_mem_xiV (hc : ChainAct c aut act) (hA : IsChainSub aut l A)
    (hinj : Function.Injective aut) {s : P} (hs : s ∈ subprods l) (hs1 : s ≠ 1) {m : ℕ}
    (hm : m < 2 ^ n) (hfix : act s m = m) : c.vm m ∈ xiV A := by
  have ha : aut s ∈ A := (hA _).2 ⟨s, hs, rfl⟩
  have ha1 : aut s ≠ 1 := fun h => hs1 (hinj (h.trans (map_one aut).symm))
  have hfx : c.vm m ∈ fixV (Subgroup.zpowers (aut s)) := by
    rw [mem_fixV]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have h1 : aut s (c.vm m) = c.vm m := (vm_fix_iff hc s hm).2 hfix
    have key : ∀ k : ℕ, (aut s ^ k) (c.vm m) = c.vm m := by
      intro k
      induction k with
      | zero => rw [pow_zero, MulAut.one_apply]
      | succ k ih => rw [pow_succ, MulAut.mul_apply, h1, ih]
    rcases Int.eq_nat_or_neg k with ⟨j, rfl | rfl⟩
    · rw [zpow_natCast]
      exact key j
    · rw [zpow_neg, zpow_natCast]
      conv_lhs => rw [← key j]
      exact (aut s ^ j).symm_apply_apply (c.vm m)
  unfold xiV
  exact (le_iSup₂_of_le (aut s) ha (le_iSup_of_le
    (f := fun _ : aut s ≠ 1 => fixV (Subgroup.zpowers (aut s))) ha1 le_rfl) :
    fixV (Subgroup.zpowers (aut s)) ≤ _) hfx

@[expose] def fourSub {G : Type*} [Group G] (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : Subgroup G where
  carrier := {1, a, b, a * b}
  mul_mem' {x y} hx hy := by
    have h1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
    have h3 : b * (a * b) = a := by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]
    have h4 : a * b * a = b := by rw [mul_assoc, ← hab, ← mul_assoc, ha, one_mul]
    have h5 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
    have h6 : a * b * (a * b) = 1 := by rw [mul_assoc, h3, ha]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp [ha, hb, h1, h3, h4, h5, h6, hab.symm]
  one_mem' := Set.mem_insert 1 _
  inv_mem' {x} hx := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    rcases hx with rfl | rfl | rfl | rfl
    · left; exact inv_one
    · right; left; exact hai
    · right; right; left; exact hbi
    · right; right; right; rw [mul_inv_rev, hai, hbi, hab]

theorem mem_fourSub {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (x : G) :
    x ∈ fourSub a b ha hb hab ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := Iff.rfl

theorem card_fourSub {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    Nat.card (fourSub a b ha hb hab) = 4 := by
  classical
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hne
    have := congrArg (a * ·) h
    simp only [← mul_assoc, ha, one_mul, mul_one] at this
    exact this.symm
  have haba : a * b ≠ a := fun h => hb1 (by simpa using h)
  have habb : a * b ≠ b := fun h => ha1 (by simpa using h)
  have hcar : ((fourSub a b ha hb hab : Subgroup G) : Set G) =
      (({1, a, b, a * b} : Finset G) : Set G) := by
    ext x
    simp [fourSub]
  rw [← SetLike.coe_sort_coe, hcar, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    Finset.card_insert_of_notMem (by simp [Ne.symm ha1, Ne.symm hb1, Ne.symm hab1]),
    Finset.card_insert_of_notMem (by simp [hne, Ne.symm haba]),
    Finset.card_pair_eq_two_iff.2 (Ne.symm habb)]

theorem mul_comm_of_mem_subprods {l : List P} (h : IsCommInvol l) {s t : P}
    (hs : s ∈ subprods l) (ht : t ∈ subprods l) : s * t = t * s := by
  have hsl : ∀ x ∈ l, s * x = x * s := by
    intro x hx
    exact (commute_subprods (fun y hy => h.2 x hx y hy) s hs).symm
  exact commute_subprods hsl t ht

theorem vm_mem_iSup_four (hc : ChainAct c aut act) (hA : IsChainSub aut l A)
    (hinj : Function.Injective aut) (hl : IndepList l) {s t : P} (hs : s ∈ subprods l)
    (ht : t ∈ subprods l) (hs1 : s ≠ 1) (ht1 : t ≠ 1) (hst : s ≠ t) {m : ℕ}
    (hm : m < 2 ^ n) (hfs : act s m = m) (hft : act t m = m) :
    c.vm m ∈ ⨆ (B : Subgroup (MulAut V)) (_ : B ≤ A) (_ : Nat.card B = 4), fixV B := by
  have hci := isCommInvol_of_indepList hl
  have hss : aut s * aut s = 1 := by
    rw [← map_mul, sq_eq_one_of_mem_subprods hci s hs, map_one]
  have htt : aut t * aut t = 1 := by
    rw [← map_mul, sq_eq_one_of_mem_subprods hci t ht, map_one]
  have hcomm : aut s * aut t = aut t * aut s := by
    rw [← map_mul, ← map_mul, mul_comm_of_mem_subprods hci hs ht]
  have ha1 : aut s ≠ 1 := fun h => hs1 (hinj (h.trans (map_one aut).symm))
  have hb1 : aut t ≠ 1 := fun h => ht1 (hinj (h.trans (map_one aut).symm))
  have hne : aut s ≠ aut t := fun h => hst (hinj h)
  set B := fourSub (aut s) (aut t) hss htt hcomm with hBdef
  have hBA : B ≤ A := by
    intro x hx
    rcases (mem_fourSub hss htt hcomm x).1 hx with rfl | rfl | rfl | rfl
    · exact A.one_mem
    · exact (hA _).2 ⟨s, hs, rfl⟩
    · exact (hA _).2 ⟨t, ht, rfl⟩
    · exact (hA _).2 ⟨s * t, mul_mem_subprods hci s hs t ht, (map_mul aut s t).symm⟩
  have hfix : c.vm m ∈ fixV B := by
    rw [mem_fixV]
    intro x hx
    have h1 : aut s (c.vm m) = c.vm m := (vm_fix_iff hc s hm).2 hfs
    have h2 : aut t (c.vm m) = c.vm m := (vm_fix_iff hc t hm).2 hft
    rcases (mem_fourSub hss htt hcomm x).1 hx with rfl | rfl | rfl | rfl
    · rfl
    · exact h1
    · exact h2
    · rw [MulAut.mul_apply, h2, h1]
  exact (le_iSup₂_of_le B hBA (le_iSup_of_le (f := fun _ : Nat.card B = 4 => fixV B)
    (card_fourSub hss htt hcomm ha1 hb1 hne) le_rfl) : fixV B ≤ _) hfix

end Chain

section Avoid

variable [Finite V]

omit [Finite V] in
theorem prod_mul_pow_mem {U : Subgroup V} {p : V} :
    ∀ os : List V, (∀ o ∈ os, o * p ∈ U) → os.prod * p ^ os.length ∈ U
  | [], _ => by simp
  | o :: os, h => by
    have hrest := prod_mul_pow_mem os fun x hx => h x (List.mem_cons_of_mem o hx)
    have ho : o * p ∈ U := h o List.mem_cons_self
    rw [List.prod_cons, List.length_cons, pow_succ]
    have : o * os.prod * (p ^ os.length * p) = (o * p) * (os.prod * p ^ os.length) := by
      rw [mul_comm (p ^ os.length) p]
      simp only [mul_assoc, mul_left_comm]
    rw [this]
    exact U.mul_mem ho hrest

theorem rk_le_four_of_avoid (hV : ∀ v : V, v ^ 2 = 1) {X U : Subgroup V} {O : Set V} {d : ℕ}
    (hX : Nat.card X = 2 ^ d) (hUX : U ≤ X) (hUO : ∀ v ∈ U, v ∉ O)
    (hcert : d ≤ 4 ∨ (d = 5 ∧ ∃ o ∈ X, o ∈ O) ∨
      (d = 6 ∧ ∃ os : List V, (∀ o ∈ os, o ∈ X ∧ o ∈ O) ∧ os.length % 2 = 1 ∧
        os.prod = 1)) :
    rk U ≤ 4 := by
  have hrkX : rk X = d := by
    unfold rk
    rw [hX, padicValNat.prime_pow]
  have hUle : rk U ≤ d := hrkX ▸ rk_mono hUX
  by_contra hlt
  push Not at hlt
  rcases hcert with hd | ⟨rfl, o, hoX, hoO⟩ | ⟨rfl, os, hos, hodd, hprod⟩
  · omega
  · have hUeq : U = X := eq_of_le_of_rk_le hV hUX (by omega)
    exact hUO o (hUeq ▸ hoX) hoO
  · obtain ⟨o, os', rfl⟩ : ∃ o os', os = o :: os' := by
      cases os with
      | nil => simp at hodd
      | cons o os' => exact ⟨o, os', rfl⟩
    have hoX : o ∈ X := (hos o List.mem_cons_self).1
    have hoU : o ∉ U := fun h => hUO o h (hos o List.mem_cons_self).2
    by_cases h6 : rk U = 6
    · exact hoU ((eq_of_le_of_rk_le hV hUX (by omega)).symm ▸ hoX)
    ·
      have hoo : o * o = 1 := by rw [← sq]; exact hV o
      have hsupX : U ⊔ Subgroup.zpowers o ≤ X := sup_le hUX
        ((Subgroup.zpowers_le).2 hoX)
      have hlt' : U < U ⊔ Subgroup.zpowers o := lt_of_le_of_ne le_sup_left fun h =>
        hoU (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers o))
      have hrk' : rk U < rk (U ⊔ Subgroup.zpowers o : Subgroup V) := by
        have hc := Subgroup.card_lt_of_lt hlt'
        rw [card_eq_two_pow hV U, card_eq_two_pow hV (U ⊔ Subgroup.zpowers o)] at hc
        exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 hc
      have hsupeq : U ⊔ Subgroup.zpowers o = X := eq_of_le_of_rk_le hV hsupX (by
        have := rk_mono hsupX
        omega)
      have hp : ∀ x ∈ o :: os', x * o ∈ U := by
        intro x hx
        have hxX : x ∈ U ⊔ Subgroup.zpowers o := hsupeq ▸ (hos x hx).1
        exact ((mem_sup_zpowers_iff hoo x).1 hxX).resolve_left fun h => hUO x h (hos x hx).2
      have key := prod_mul_pow_mem (o :: os') hp
      rw [hprod, one_mul] at key
      have hpow : o ^ (o :: os').length = o := by
        obtain ⟨k, hk⟩ : ∃ k, (o :: os').length = 2 * k + 1 := ⟨(o :: os').length / 2, by omega⟩
        rw [hk, pow_succ, pow_mul, sq, hoo, one_pow, one_mul]
      rw [hpow] at key
      exact hoU key

end Avoid

end CFSG.Quasithin.H.Mathieu
