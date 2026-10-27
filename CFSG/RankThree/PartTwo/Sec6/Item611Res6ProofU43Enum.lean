module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofU43Perm

public section

namespace CFSG.RankThree.PartTwo.Sec6.Res611Res6.U43P

open CFSG.LieType.Multipliers.U43

@[expose] def bpt (j : ℕ) : ℕ := if j = 0 then 0 else if j = 1 then 1 else 9

theorem bpt_lt (j : ℕ) : bpt j < 820 := by
  unfold bpt
  split_ifs <;> norm_num

@[expose] def bptF (j : ℕ) : Fin 820 := ⟨bpt j, bpt_lt j⟩

@[expose] def ofChunks : List ℕ → ℕ
  | [] => 0
  | c :: l => c + 2 ^ 256 * ofChunks l

@[expose] def fld (t w i : ℕ) : ℕ := Nat.land (Nat.shiftRight t (w * i)) (2 ^ w - 1)

instance finite_X₀ : Finite X₀ := Nat.finite_of_card_ne_zero (by rw [card_X₀]; norm_num)

section Base


theorem eq_of_bpt {g h : X₀}
    (hb : ∀ j < 3, ((g • bptF j : Fin 820) : ℕ) = (h • bptF j : Fin 820)) :
    g = h :=
  eq_of_smul_base (hb 0 (by norm_num)) (hb 1 (by norm_num)) (hb 2 (by norm_num))

end Base

structure ETab where
  n : ℕ
  gens : List ℕ
  bi : ℕ
  par : ℕ
  gi : ℕ
  dep : ℕ
  cl : ℕ
  fuel : ℕ

namespace ETab

variable (T : ETab)

@[expose] def gw (i : ℕ) : ℕ := T.gens.getD i 0

@[expose] def b (k j : ℕ) : ℕ := lk T.bi (3 * k + j)

@[expose] def p (k : ℕ) : ℕ := lk T.par k

@[expose] def g (k : ℕ) : ℕ := lk T.gi k

@[expose] def d (k : ℕ) : ℕ := lk T.dep k

@[expose] def c (k i : ℕ) : ℕ := lk T.cl (k * T.gens.length + i)

@[expose] def key (k : ℕ) : ℕ := T.b k 0 * 1048576 + T.b k 1 * 1024 + T.b k 2

@[expose] def actF : ℕ → ℕ → ℕ → ℕ
  | 0, _, i => i
  | f + 1, k, i => if k = 0 then i else act (T.gw (T.g k)) (actF f (T.p k) i)

@[expose] noncomputable def elemF : ℕ → ℕ → X₀
  | 0, _ => 1
  | f + 1, k => if k = 0 then 1 else ev (T.gw (T.g k)) * elemF f (T.p k)

@[expose] def actE (k i : ℕ) : ℕ := T.actF T.fuel k i

@[expose] noncomputable def elem (k : ℕ) : X₀ := T.elemF T.fuel k

@[expose] noncomputable def H : Subgroup X₀ :=
  Subgroup.closure {x | ∃ i < T.gens.length, x = ev (T.gw i)}

theorem smul_elemF (f k : ℕ) (i : Fin 820) : ((T.elemF f k • i : Fin 820) : ℕ) = T.actF f k i := by
  induction f generalizing k i with
  | zero => simp [elemF, actF]
  | succ f ih =>
    by_cases hk : k = 0
    · simp [elemF, actF, hk]
    · simp only [elemF, actF, hk, ↓reduceIte, mul_smul]
      rw [act_spec, ih]

theorem smul_elem (k : ℕ) (i : Fin 820) : ((T.elem k • i : Fin 820) : ℕ) = T.actE k i :=
  T.smul_elemF T.fuel k i

@[expose] def chkBase : Bool := T.b 0 0 == 0 && T.b 0 1 == 1 && T.b 0 2 == 9 && T.d 0 == 0

@[expose] def chkTree : Bool :=
  (List.range T.n).all fun k => k == 0 || (decide (T.p k < T.n) && decide (T.d (T.p k) < T.d k) &&
    decide (T.d k < T.fuel) && decide (T.g k < T.gens.length) &&
    (List.range 3).all fun j => act (T.gw (T.g k)) (T.b (T.p k) j) == T.b k j)

@[expose] def chkClosed : Bool :=
  (List.range T.n).all fun k => (List.range T.gens.length).all fun i =>
    decide (T.c k i < T.n) && (List.range 3).all fun j => act (T.gw i) (T.b k j) == T.b (T.c k i) j

@[expose] def chkSorted : Bool :=
  (List.range (T.n - 1)).all fun k => decide (T.key k < T.key (k + 1))

theorem chkBase_spec (h : T.chkBase = true) : (∀ j < 3, T.b 0 j = bpt j) ∧ T.d 0 = 0 := by
  simp only [chkBase, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h9⟩, hd⟩ := h
  refine ⟨fun j hj => ?_, hd⟩
  interval_cases j
  · exact h0
  · exact h1
  · exact h9

theorem chkTree_spec (h : T.chkTree = true) {k : ℕ} (hk : k < T.n) (hk0 : k ≠ 0) :
    T.p k < T.n ∧ T.d (T.p k) < T.d k ∧ T.d k < T.fuel ∧ T.g k < T.gens.length ∧
      ∀ j < 3, act (T.gw (T.g k)) (T.b (T.p k) j) = T.b k j := by
  simp only [chkTree, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h k hk with h | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  · exact absurd h hk0
  · exact ⟨h1, h2, h3, h4, fun j hj => h5 j hj⟩

theorem smul_elemF_bpt (hb : T.chkBase = true) (ht : T.chkTree = true) :
    ∀ m k, k < T.n → T.d k ≤ m → ∀ f, T.d k < f → ∀ j < 3,
      ((T.elemF f k • bptF j : Fin 820) : ℕ) = T.b k j := by
  obtain ⟨hb0, hd0⟩ := T.chkBase_spec hb
  intro m
  induction m with
  | zero =>
    intro k hk hdk f hf j hj
    by_cases hk0 : k = 0
    · subst hk0
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      simp only [elemF, ↓reduceIte, one_smul]
      rw [hb0 j hj]
      rfl
    · obtain ⟨-, hlt, -⟩ := T.chkTree_spec ht hk hk0
      omega
  | succ m ih =>
    intro k hk hdk f hf j hj
    by_cases hk0 : k = 0
    · subst hk0
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      simp only [elemF, ↓reduceIte, one_smul]
      rw [hb0 j hj]
      rfl
    · obtain ⟨hp, hlt, -, -, hact⟩ := T.chkTree_spec ht hk hk0
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      simp only [elemF, hk0, ↓reduceIte, mul_smul]
      rw [act_spec, ih (T.p k) hp (by omega) f (by omega) j hj, hact j hj]

theorem elem_zero : T.elem 0 = 1 := by
  unfold elem
  cases T.fuel with
  | zero => rfl
  | succ f => simp [elemF]

theorem smul_elem_bpt (hb : T.chkBase = true) (ht : T.chkTree = true) {k : ℕ} (hk : k < T.n)
    {j : ℕ} (hj : j < 3) : ((T.elem k • bptF j : Fin 820) : ℕ) = T.b k j := by
  by_cases hk0 : k = 0
  · subst hk0
    rw [T.elem_zero, one_smul, (T.chkBase_spec hb).1 j hj]
    rfl
  · exact T.smul_elemF_bpt hb ht (T.d k) k hk le_rfl T.fuel (T.chkTree_spec ht hk hk0).2.2.1 j hj

theorem ev_gw_mem {i : ℕ} (hi : i < T.gens.length) : ev (T.gw i) ∈ T.H :=
  Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem elemF_mem (ht : T.chkTree = true) : ∀ f k, k < T.n → T.elemF f k ∈ T.H := by
  intro f
  induction f with
  | zero => intro k _; exact T.H.one_mem
  | succ f ih =>
    intro k hk
    by_cases hk0 : k = 0
    · simp only [elemF, hk0, ↓reduceIte]
      exact T.H.one_mem
    · obtain ⟨hp, -, -, hg, -⟩ := T.chkTree_spec ht hk hk0
      simp only [elemF, hk0, ↓reduceIte]
      exact T.H.mul_mem (T.ev_gw_mem hg) (ih _ hp)

theorem elem_mem (ht : T.chkTree = true) {k : ℕ} (hk : k < T.n) : T.elem k ∈ T.H :=
  T.elemF_mem ht T.fuel k hk

theorem key_lt (hs : T.chkSorted = true) :
    ∀ d k, k + d + 1 < T.n → T.key k < T.key (k + d + 1) := by
  simp only [chkSorted, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hs
  intro d
  induction d with
  | zero => intro k hk; exact hs k (by omega)
  | succ d ih =>
    intro k hk
    exact (ih k (by omega)).trans (hs (k + d + 1) (by omega))

theorem elem_injOn (hb : T.chkBase = true) (ht : T.chkTree = true) (hs : T.chkSorted = true)
    {k k' : ℕ} (hk : k < T.n) (hk' : k' < T.n) (h : T.elem k = T.elem k') : k = k' := by
  have e : ∀ j < 3, T.b k j = T.b k' j := fun j hj => by
    rw [← T.smul_elem_bpt hb ht hk hj, ← T.smul_elem_bpt hb ht hk' hj, h]
  have hkey : T.key k = T.key k' := by
    unfold key
    rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num)]
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · have := T.key_lt hs (k' - k - 1) k (by omega)
    rw [show k + (k' - k - 1) + 1 = k' by omega] at this
    omega
  · exact heq
  · have := T.key_lt hs (k - k' - 1) k' (by omega)
    rw [show k' + (k - k' - 1) + 1 = k by omega] at this
    omega

theorem chkClosed_spec (h : T.chkClosed = true) {k i : ℕ} (hk : k < T.n)
    (hi : i < T.gens.length) :
    T.c k i < T.n ∧ ∀ j < 3, act (T.gw i) (T.b k j) = T.b (T.c k i) j := by
  simp only [chkClosed, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h k hk i hi
  exact ⟨h1, fun j hj => h2 j hj⟩

section Closed


theorem mul_elem_eq (hb : T.chkBase = true) (ht : T.chkTree = true) (hc : T.chkClosed = true)
    {k i : ℕ} (hk : k < T.n) (hi : i < T.gens.length) :
    ev (T.gw i) * T.elem k = T.elem (T.c k i) := by
  obtain ⟨hck, hact⟩ := T.chkClosed_spec hc hk hi
  apply eq_of_bpt
  intro j hj
  rw [mul_smul, act_spec, T.smul_elem_bpt hb ht hk hj, hact j hj, T.smul_elem_bpt hb ht hck hj]

theorem pow_mul_elem (hb : T.chkBase = true) (ht : T.chkTree = true) (hc : T.chkClosed = true)
    {i : ℕ} (hi : i < T.gens.length) :
    ∀ m k, k < T.n → ∃ k' < T.n, ev (T.gw i) ^ m * T.elem k = T.elem k' := by
  intro m
  induction m with
  | zero => intro k hk; exact ⟨k, hk, by rw [pow_zero, one_mul]⟩
  | succ m ih =>
    intro k hk
    obtain ⟨k', hk', e⟩ := ih k hk
    refine ⟨T.c k' i, (T.chkClosed_spec hc hk' hi).1, ?_⟩
    rw [pow_succ', mul_assoc, e, T.mul_elem_eq hb ht hc hk' hi]

theorem exists_eq_elem (hb : T.chkBase = true) (ht : T.chkTree = true) (hc : T.chkClosed = true)
    (hn : 0 < T.n) {x : X₀} (hx : x ∈ T.H) : ∃ k < T.n, x = T.elem k := by
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨0, hn, T.elem_zero.symm⟩
  | mul_left s hs y hy ih =>
    obtain ⟨i, hi, rfl⟩ := hs
    obtain ⟨k, hk, rfl⟩ := ih
    exact ⟨T.c k i, (T.chkClosed_spec hc hk hi).1, T.mul_elem_eq hb ht hc hk hi⟩
  | inv_mul_cancel s hs y hy ih =>
    obtain ⟨i, hi, rfl⟩ := hs
    obtain ⟨k, hk, rfl⟩ := ih
    set u := ev (T.gw i)
    have hu : u⁻¹ = u ^ (orderOf u - 1) := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos u), pow_orderOf_eq_one]
    obtain ⟨k', hk', e⟩ := T.pow_mul_elem hb ht hc hi (orderOf u - 1) k hk
    exact ⟨k', hk', by rw [hu, e]⟩

theorem card_H (hb : T.chkBase = true) (ht : T.chkTree = true) (hc : T.chkClosed = true)
    (hs : T.chkSorted = true) (hn : 0 < T.n) : Nat.card T.H = T.n := by
  have hbij : Function.Bijective fun k : Fin T.n => (⟨T.elem k, T.elem_mem ht k.2⟩ : T.H) := by
    refine ⟨fun k k' h => Fin.ext (T.elem_injOn hb ht hs k.2 k'.2 (congrArg Subtype.val h)),
      fun x => ?_⟩
    obtain ⟨k, hk, e⟩ := T.exists_eq_elem hb ht hc hn x.2
    exact ⟨⟨k, hk⟩, Subtype.ext e.symm⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

end Closed

end ETab

end CFSG.RankThree.PartTwo.Sec6.Res611Res6.U43P
