module

public import CFSG.LieType.Steinberg.Classical.Symplectic

public section

namespace CFSG.Timmesfeld.Transvection.Pres

open Matrix CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.LieType.RootSystem TauCeti.GLSymplecticFin
open scoped commutatorElement

variable {n : ℕ}

@[expose] def idx : Fin n ⊕ Fin n → Fin n := Sum.elim id id

@[simp] theorem idx_inl (i : Fin n) : idx (Sum.inl i : Fin n ⊕ Fin n) = i := rfl

@[simp] theorem idx_inr (i : Fin n) : idx (Sum.inr i : Fin n ⊕ Fin n) = i := rfl

@[simp] theorem idx_swap (a : Fin n ⊕ Fin n) : idx (Sum.swap a) = idx a := by
  rcases a with i | i <;> rfl

theorem eq_or_eq_swap_of_idx_eq {a b : Fin n ⊕ Fin n} (h : idx a = idx b) :
    b = a ∨ b = Sum.swap a := by
  rcases a with i | i <;> rcases b with j | j <;> simp_all [idx]

theorem idx_ne_of_ne {a b : Fin n ⊕ Fin n} (h₁ : b ≠ a) (h₂ : b ≠ Sum.swap a) :
    idx a ≠ idx b := fun h => (eq_or_eq_swap_of_idx_eq h).elim h₁ h₂

theorem ne_of_idx_ne {a b : Fin n ⊕ Fin n} (h : idx a ≠ idx b) : b ≠ a := by
  rintro rfl
  exact h rfl

theorem ne_swap_of_idx_ne {a b : Fin n ⊕ Fin n} (h : idx a ≠ idx b) : b ≠ Sum.swap a := by
  rintro rfl
  exact h (idx_swap a).symm

theorem swap_ne_self (a : Fin n ⊕ Fin n) : Sum.swap a ≠ a := by
  rcases a with i | i <;> simp

theorem wt_dot_swap (a : Fin n ⊕ Fin n) : wt a ⬝ᵥ wt (Sum.swap a) = -1 := by
  rw [Sp.wt_swap, dotProduct_neg, Sp.dot_wt_self]

theorem wt_dot_of_idx_ne {a b : Fin n ⊕ Fin n} (h : idx a ≠ idx b) : wt a ⬝ᵥ wt b = 0 := by
  rcases a with i | i <;> rcases b with j | j <;>
    simp only [idx_inl, idx_inr] at h <;> simp [wt, h]

theorem wt_dot_wt (a b : Fin n ⊕ Fin n) :
    wt a ⬝ᵥ wt b = if b = a then 1 else if b = Sum.swap a then -1 else 0 := by
  by_cases h₁ : b = a
  · subst h₁
    rw [ite_eq_left rfl, Sp.dot_wt_self]
  by_cases h₂ : b = Sum.swap a
  · subst h₂
    rw [ite_eq_right h₁, ite_eq_left rfl, wt_dot_swap]
  · rw [ite_eq_right h₁, ite_eq_right h₂, wt_dot_of_idx_ne (idx_ne_of_ne h₁ h₂)]

theorem wt_dot_nonneg {a b : Fin n ⊕ Fin n} (h : b ≠ Sum.swap a) : 0 ≤ wt a ⬝ᵥ wt b := by
  rw [wt_dot_wt]
  split_ifs <;> simp_all

@[expose] def rt (a b : Fin n ⊕ Fin n) : Fin n → ℤ := wt a + wt b

theorem rt_comm (a b : Fin n ⊕ Fin n) : rt a b = rt b a := add_comm _ _

theorem rt_swap_swap (a b : Fin n ⊕ Fin n) : rt (Sum.swap a) (Sum.swap b) = -rt a b := by
  simp only [rt, Sp.wt_swap, neg_add]

theorem rt_inl_inl (i : Fin n) : rt (Sum.inl i) (Sum.inl i) = 2 • Pi.single i 1 := by
  rw [rt, two_nsmul]
  rfl

theorem rt_inr_inr (i : Fin n) : rt (Sum.inr i) (Sum.inr i) = -(2 • Pi.single i 1) := by
  rw [rt, two_nsmul, neg_add]
  rfl

theorem rt_inl_inr (i j : Fin n) : rt (Sum.inl i) (Sum.inr j) = Pi.single i 1 - Pi.single j 1 := by
  rw [rt, sub_eq_add_neg]
  rfl

theorem rt_inl_inl' (i j : Fin n) : rt (Sum.inl i) (Sum.inl j) = Pi.single i 1 + Pi.single j 1 :=
  rfl

theorem rt_inr_inr' (i j : Fin n) :
    rt (Sum.inr i) (Sum.inr j) = -Pi.single i 1 - Pi.single j 1 := by
  rw [rt, sub_eq_add_neg]
  rfl

theorem ofPos_ne {a b : Fin n ⊕ Fin n} (h : b ≠ Sum.swap a) : a ≠ Sum.swap b := by
  rintro rfl
  exact h (Sum.swap_swap b).symm

@[expose] noncomputable def rtIdx (a b : Fin n ⊕ Fin n) : RootSubgroupIndex n :=
  ofPos a (Sum.swap b)

theorem stdVec_rtIdx {a b : Fin n ⊕ Fin n} (h : b ≠ Sum.swap a) : stdVec (rtIdx a b) = rt a b := by
  rw [rtIdx, stdVec_ofPos (ofPos_ne h), Sp.wt_swap, sub_neg_eq_add, rt]

theorem rtIdx_comm {a b : Fin n ⊕ Fin n} (h : b ≠ Sum.swap a) : rtIdx b a = rtIdx a b := by
  have h' : a ≠ Sum.swap b := ofPos_ne h
  exact stdVec_injective (by rw [stdVec_rtIdx h', stdVec_rtIdx h, rt_comm])

theorem rt_mem {a b : Fin n ⊕ Fin n} (h : b ≠ Sum.swap a) : rt a b ∈ Set.range (stdVec (n := n)) :=
  ⟨rtIdx a b, stdVec_rtIdx h⟩

@[expose] def sp (r : RootSubgroupIndex n) : (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) :=
  ((pos1 r).1, Sum.swap (pos1 r).2)

theorem sp_ne (r : RootSubgroupIndex n) : (sp r).2 ≠ Sum.swap (sp r).1 := by
  intro h
  have : (pos1 r).2 = (pos1 r).1 := by
    have := congrArg Sum.swap h
    simpa [sp] using this
  exact pos1_ne r this.symm

theorem rt_sp (r : RootSubgroupIndex n) : rt (sp r).1 (sp r).2 = stdVec r := by
  rw [rt, sp, Sp.wt_swap, ← sub_eq_add_neg, wt_pos1]

theorem pos2_eq (r : RootSubgroupIndex n) :
    pos2 r = (Sum.swap (pos1 r).2, Sum.swap (pos1 r).1) := by
  cases r <;> rfl

theorem eq_sp_of_rt_eq {a b : Fin n ⊕ Fin n} {r : RootSubgroupIndex n} (h : rt a b = stdVec r) :
    (a, b) = sp r ∨ (b, a) = sp r := by
  have hw : wt a - wt (Sum.swap b) = stdVec r := by
    rw [Sp.wt_swap, sub_neg_eq_add]
    exact h
  rcases eq_pos_of_wt_sub r a (Sum.swap b) hw with h1 | h1
  · left
    rw [sp, ← h1]
    simp
  · right
    rw [pos2_eq] at h1
    simp only [Prod.mk.injEq] at h1
    obtain ⟨h1, h2⟩ := h1
    rw [sp]
    have e1 : (pos1 r).2 = Sum.swap a := by rw [h1, Sum.swap_swap]
    have e2 : (pos1 r).1 = b := by
      have := congrArg Sum.swap h2
      simpa using this.symm
    rw [e1, e2, Sum.swap_swap]

theorem rt_eq_rt_iff {a b c d : Fin n ⊕ Fin n} (hcd : d ≠ Sum.swap c) :
    rt a b = rt c d ↔ (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  constructor
  · intro h
    have h1 := eq_sp_of_rt_eq (h.trans (stdVec_rtIdx hcd).symm)
    have h2 := eq_sp_of_rt_eq (stdVec_rtIdx hcd).symm
    simp only [Prod.ext_iff] at h1 h2
    rcases h1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases h2 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩
    · exact Or.inl ⟨h2.trans h1.symm, h2'.trans h1'.symm⟩
    · exact Or.inr ⟨h2'.trans h1'.symm, h2.trans h1.symm⟩
    · exact Or.inr ⟨h2.trans h1.symm, h2'.trans h1'.symm⟩
    · exact Or.inl ⟨h2'.trans h1'.symm, h2.trans h1.symm⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact rt_comm _ _

theorem exists_rt_eq (r : RootSubgroupIndex n) :
    ∃ a b : Fin n ⊕ Fin n, b ≠ Sum.swap a ∧ rt a b = stdVec r :=
  ⟨_, _, sp_ne r, rt_sp r⟩

theorem rt_dot_rt (a b : Fin n ⊕ Fin n) :
    rt a b ⬝ᵥ rt a b = 2 + 2 * (wt a ⬝ᵥ wt b) := by
  simp only [rt, add_dotProduct, dotProduct_add, Sp.dot_wt_self, dotProduct_comm (wt b) (wt a)]
  ring

theorem dot_of_mem {v : Fin n → ℤ} (hv : v ∈ Set.range (stdVec (n := n))) :
    v ⬝ᵥ v = 2 ∨ v ⬝ᵥ v = 4 := by
  obtain ⟨r, rfl⟩ := hv
  exact dot_stdVec r

theorem notMem_of_dot {v : Fin n → ℤ} (h₂ : v ⬝ᵥ v ≠ 2) (h₄ : v ⬝ᵥ v ≠ 4) :
    v ∉ Set.range (stdVec (n := n)) := fun hv => (dot_of_mem hv).elim h₂ h₄

section Constants

variable {K : Type} [Field K]

@[expose] def coef (K : Type) [Field K] (u v : Fin n → ℤ) (p : ℕ × ℕ) : K :=
  if p = (1, 1) ∧ (u + v) ⬝ᵥ (u + v) ≠ 2 then 0 else 1

theorem intCast_eq_one_of_natAbs [CharP K 2] {z : ℤ} (h : z.natAbs = 1) : (z : K) = 1 := by
  rcases Int.natAbs_eq_iff.1 h with rfl | rfl
  · simp
  · simp [CharTwo.neg_eq]

theorem pos1_snd_of_long {t : RootSubgroupIndex n} (h : stdVec t ⬝ᵥ stdVec t = 4) :
    (pos1 t).2 = Sum.swap (pos1 t).1 := by
  cases t with
  | positiveLong i => rfl
  | negativeLong i => rfl
  | difference i j hij => simp [stdVec, dotProduct_sub, hij, Ne.symm hij] at h
  | positiveSum i j hij => simp [stdVec, dotProduct_add, hij.ne, hij.ne'] at h
  | negativeSum i j hij => simp [stdVec, dotProduct_add, hij.ne, hij.ne'] at h

theorem Ez_mul_Ez_apply_swap (r s : RootSubgroupIndex n) (x : Fin n ⊕ Fin n) :
    (Sp.Ez s * Sp.Ez r) x (Sum.swap x) = -(Sp.Ez r * Sp.Ez s) x (Sum.swap x) := by
  rw [Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_neg_distrib]
  rw [← (Equiv.sumComm (Fin n) (Fin n)).sum_comp]
  refine Finset.sum_congr rfl fun z _ => ?_
  change Sp.Ez s x (Sum.swap z) * Sp.Ez r (Sum.swap z) (Sum.swap x) = _
  rw [Sp.Ez_symm s x (Sum.swap z), Sp.Ez_symm r (Sum.swap z) (Sum.swap x), Sum.swap_swap,
    Sum.swap_swap]
  have hk := Sp.κ_swap_mul x z
  linear_combination (Sp.Ez r x z * Sp.Ez s z (Sum.swap x)) * hk

theorem even_commC_one_one {α β : Fin n → ℤ} (hα : α ∈ roots (isFiniteType_cartanC n) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) (hαβ : α + β ≠ 0)
    (hr : α + β ∈ roots (isFiniteType_cartanC n) ∅)
    (h4 : toStd n (α + β) ⬝ᵥ toStd n (α + β) = 4) : Even (Sp.commC α β (1, 1)) := by
  obtain ⟨r, hr'⟩ := exists_stdVec_of_mem_roots hα
  obtain ⟨s, hs⟩ := exists_stdVec_of_mem_roots hβ
  obtain ⟨t, ht⟩ := exists_stdVec_of_mem_roots hr
  rw [Sp.commC_one_one hαβ, Sp.Exz_eq hr', Sp.Exz_eq hs, Sp.entryAt_eq _ ht,
    pos1_snd_of_long (by rw [ht]; exact h4), Matrix.sub_apply, Ez_mul_Ez_apply_swap r s]
  exact ⟨(Sp.Ez r * Sp.Ez s) (pos1 t).1 (Sum.swap (pos1 t).1), by ring⟩

theorem natAbs_commC_two_one {α β : Fin n → ℤ} (hα : α ∈ roots (isFiniteType_cartanC n) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) (hαβ : α + β ≠ 0)
    (hr : 2 • α + β ∈ roots (isFiniteType_cartanC n) ∅) : (Sp.commC α β (2, 1)).natAbs = 1 := by
  obtain ⟨r, hr'⟩ := exists_stdVec_of_mem_roots hα
  obtain ⟨s, hs⟩ := exists_stdVec_of_mem_roots hβ
  obtain ⟨t, ht⟩ := exists_stdVec_of_mem_roots hr
  rw [Sp.commC_two_one hαβ, Sp.Exz_eq hr', Sp.Exz_eq hs, Sp.entryAt_eq _ ht, Matrix.neg_apply,
    Int.natAbs_neg]
  refine Sp.coeff21_spec (ht.trans (by rw [toStd_add', toStd_nsmul', hr', hs])) ?_
  rw [hr', hs]
  exact Sp.toStd_add_ne_zero hαβ

theorem cast_commC [CharP K 2] {α β : Fin n → ℤ} (hα : α ∈ roots (isFiniteType_cartanC n) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) (hαβ : α + β ≠ 0) {p : ℕ × ℕ}
    (hp : p ∈ expPairs (Sp.Φ n K) α β) :
    (Sp.commC α β p : K) = coef K (toStd n α) (toStd n β) p := by
  have hpS := Sp.mem_expS_of_mem_expPairs hα hβ hαβ hp
  have hpr := hp.2.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpS
  rcases hpS with rfl | rfl | rfl
  · simp only [one_smul] at hpr
    obtain ⟨t, ht⟩ := exists_stdVec_of_mem_roots hpr
    have hsum : toStd n α + toStd n β = stdVec t := by rw [← toStd_add', ht]
    rcases dot_stdVec t with h2 | h4
    · rw [coef, ite_eq_right (fun h => h.2 (by rw [hsum]; exact h2))]
      exact intCast_eq_one_of_natAbs
        (Sp.natAbs_commC_one_one hα hβ hαβ hpr (by rw [← ht]; exact h2))
    · rw [coef, ite_eq_left ⟨rfl, by rw [hsum, h4]; norm_num⟩]
      obtain ⟨m, hm⟩ := even_commC_one_one hα hβ hαβ hpr (by rw [← ht]; exact h4)
      rw [hm, Int.cast_add, CharTwo.add_self_eq_zero]
  · rw [coef, ite_eq_right (fun h => absurd h.1 (by decide))]
    simp only [one_smul] at hpr
    exact intCast_eq_one_of_natAbs (natAbs_commC_two_one hα hβ hαβ hpr)
  · rw [coef, ite_eq_right (fun h => absurd h.1 (by decide))]
    simp only [one_smul] at hpr
    exact intCast_eq_one_of_natAbs (Sp.natAbs_commC_one_two hα hβ hαβ hpr)

end Constants

section Norms

variable {a b d : Fin n ⊕ Fin n}

theorem dot_two (hab : idx a ≠ idx b) (p q : ℤ) :
    (p • wt a + q • wt b) ⬝ᵥ (p • wt a + q • wt b) = p * p + q * q := by
  simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, Sp.dot_wt_self,
    wt_dot_of_idx_ne hab, wt_dot_of_idx_ne hab.symm, smul_eq_mul]
  ring

theorem dot_three (hab : idx a ≠ idx b) (hbd : idx b ≠ idx d) (had : idx a ≠ idx d)
    (p q r : ℤ) :
    (p • wt a + q • wt b + r • wt d) ⬝ᵥ (p • wt a + q • wt b + r • wt d) =
      p * p + q * q + r * r := by
  simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, Sp.dot_wt_self,
    wt_dot_of_idx_ne hab, wt_dot_of_idx_ne hab.symm, wt_dot_of_idx_ne hbd,
    wt_dot_of_idx_ne hbd.symm, wt_dot_of_idx_ne had, wt_dot_of_idx_ne had.symm, smul_eq_mul]
  ring

end Norms

section Word

theorem mem_roots_iff (γ : Fin n → ℤ) :
    γ ∈ roots (isFiniteType_cartanC n) ∅ ↔ toStd n γ ∈ Set.range (stdVec (n := n)) := by
  rw [roots_eq]
  rfl

open Classical in
@[expose] noncomputable def epsList (u v : Fin n → ℤ) : List (ℕ × ℕ) :=
  ([(1, 1), (2, 1), (1, 2)] : List (ℕ × ℕ)).filter fun p =>
    decide (p.1 • u + p.2 • v ∈ Set.range (stdVec (n := n)))

open Classical in
@[expose] noncomputable def spOrder (n : ℕ) (K : Type) [Field K] : CommOrder (Sp.Φ n K) where
  list α β := epsList (toStd n α) (toStd n β)
  nodup α β := List.Nodup.filter _ (by decide)
  mem_iff α hα β hβ hαβ p := by
    rw [Sp.mem_expPairs_iff hα hβ hαβ, epsList, List.mem_filter, decide_eq_true_iff,
      mem_roots_iff, Sp.toStd_comb]
    simp

theorem list_spOrder (K : Type) [Field K] (α β : Fin n → ℤ) :
    (spOrder n K).list α β = epsList (toStd n α) (toStd n β) := rfl

variable {K : Type} [Field K] {G : Type*} [Group G]

@[expose] noncomputable def epsWord (ξ : (Fin n → ℤ) → K → G) (u v : Fin n → ℤ) (s t : K) : G :=
  ((epsList u v).map fun p => ξ (p.1 • u + p.2 • v) (coef K u v p * s ^ p.1 * t ^ p.2)).prod

open Classical in
theorem epsWord_eq (ξ : (Fin n → ℤ) → K → G) (u v : Fin n → ℤ) (s t : K) :
    epsWord ξ u v s t =
      (if u + v ∈ Set.range (stdVec (n := n)) then ξ (u + v) (coef K u v (1, 1) * s * t)
        else 1) *
      ((if 2 • u + v ∈ Set.range (stdVec (n := n)) then ξ (2 • u + v) (s ^ 2 * t) else 1) *
        (if u + 2 • v ∈ Set.range (stdVec (n := n)) then ξ (u + 2 • v) (s * t ^ 2) else 1)) := by
  have h21 : coef K u v (2, 1) = 1 := by rw [coef, ite_eq_right (fun h => absurd h.1 (by decide))]
  have h12 : coef K u v (1, 2) = 1 := by rw [coef, ite_eq_right (fun h => absurd h.1 (by decide))]
  rw [epsWord, epsList]
  simp only [List.filter_cons, List.filter_nil, one_smul]
  by_cases h1 : u + v ∈ Set.range (stdVec (n := n)) <;>
    by_cases h2 : 2 • u + v ∈ Set.range (stdVec (n := n)) <;>
    by_cases h3 : u + 2 • v ∈ Set.range (stdVec (n := n)) <;>
    simp only [h1, h2, h3, decide_true, decide_false, ite_true, ite_false, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_mul, pow_one, h21, h12,
      Bool.false_eq_true, one_smul]

theorem coef_one_one_of_eq {u v : Fin n → ℤ} (h : (u + v) ⬝ᵥ (u + v) = 2) :
    coef K u v (1, 1) = 1 :=
  ite_eq_right fun h' => h'.2 h

theorem coef_one_one_of_ne {u v : Fin n → ℤ} (h : (u + v) ⬝ᵥ (u + v) ≠ 2) :
    coef K u v (1, 1) = 0 :=
  ite_eq_left ⟨rfl, h⟩

end Word

section Families

variable {K : Type} [Field K] {G : Type*} [Group G] (ξ : (Fin n → ℤ) → K → G)
  {a b c d : Fin n ⊕ Fin n}

theorem epsWord_short (hab : idx a ≠ idx b) (hbd : idx b ≠ idx d) (had : idx a ≠ idx d)
    (s t : K) : epsWord ξ (rt a b) (rt (Sum.swap b) d) s t = ξ (rt a d) (s * t) := by
  have e1 : rt a b + rt (Sum.swap b) d = rt a d := by simp only [rt, Sp.wt_swap]; abel
  have e2 : 2 • rt a b + rt (Sum.swap b) d = (2 : ℤ) • wt a + (1 : ℤ) • wt b + (1 : ℤ) • wt d :=
    by simp only [rt, Sp.wt_swap]; module
  have e3 : rt a b + 2 • rt (Sum.swap b) d = (1 : ℤ) • wt a + (-1 : ℤ) • wt b + (2 : ℤ) • wt d :=
    by simp only [rt, Sp.wt_swap]; module
  have hn : rt a d ⬝ᵥ rt a d = 2 := by rw [rt_dot_rt, wt_dot_of_idx_ne had]; norm_num
  have h2 : 2 • rt a b + rt (Sum.swap b) d ∉ Set.range (stdVec (n := n)) := by
    rw [e2]
    exact notMem_of_dot (by rw [dot_three hab hbd had]; norm_num)
      (by rw [dot_three hab hbd had]; norm_num)
  have h3 : rt a b + 2 • rt (Sum.swap b) d ∉ Set.range (stdVec (n := n)) := by
    rw [e3]
    exact notMem_of_dot (by rw [dot_three hab hbd had]; norm_num)
      (by rw [dot_three hab hbd had]; norm_num)
  rw [epsWord_eq, ite_eq_right h2, ite_eq_right h3, coef_one_one_of_eq (by rw [e1, hn]), e1,
    ite_eq_left (rt_mem (ne_swap_of_idx_ne had)), one_mul, mul_one, mul_one]

theorem epsWord_shortLong (hab : idx a ≠ idx b) (s t : K) :
    epsWord ξ (rt a b) (rt (Sum.swap b) (Sum.swap b)) s t =
      ξ (rt a (Sum.swap b)) (s * t) * ξ (rt a a) (s ^ 2 * t) := by
  have hab' : idx a ≠ idx (Sum.swap b) := by rwa [idx_swap]
  have e1 : rt a b + rt (Sum.swap b) (Sum.swap b) = rt a (Sum.swap b) := by
    simp only [rt, Sp.wt_swap]; abel
  have e2 : 2 • rt a b + rt (Sum.swap b) (Sum.swap b) = rt a a := by
    simp only [rt, Sp.wt_swap]; module
  have e3 : rt a b + 2 • rt (Sum.swap b) (Sum.swap b) = (1 : ℤ) • wt a + (-3 : ℤ) • wt b := by
    simp only [rt, Sp.wt_swap]; module
  have hn : rt a (Sum.swap b) ⬝ᵥ rt a (Sum.swap b) = 2 := by
    rw [rt_dot_rt, wt_dot_of_idx_ne hab']; norm_num
  have h3 : rt a b + 2 • rt (Sum.swap b) (Sum.swap b) ∉ Set.range (stdVec (n := n)) := by
    rw [e3]
    exact notMem_of_dot (by rw [dot_two hab]; norm_num) (by rw [dot_two hab]; norm_num)
  rw [epsWord_eq, ite_eq_right h3, coef_one_one_of_eq (by rw [e1, hn]), e1, e2,
    ite_eq_left (rt_mem (ne_swap_of_idx_ne hab')), ite_eq_left (rt_mem (Ne.symm (swap_ne_self a))),
    one_mul, mul_one]

theorem epsWord_longShort (had : idx a ≠ idx d) (s t : K) :
    epsWord ξ (rt a a) (rt (Sum.swap a) d) s t =
      ξ (rt a d) (s * t) * ξ (rt d d) (s * t ^ 2) := by
  have e1 : rt a a + rt (Sum.swap a) d = rt a d := by simp only [rt, Sp.wt_swap]; abel
  have e2 : 2 • rt a a + rt (Sum.swap a) d = (3 : ℤ) • wt a + (1 : ℤ) • wt d := by
    simp only [rt, Sp.wt_swap]; module
  have e3 : rt a a + 2 • rt (Sum.swap a) d = rt d d := by
    simp only [rt, Sp.wt_swap]; module
  have hn : rt a d ⬝ᵥ rt a d = 2 := by rw [rt_dot_rt, wt_dot_of_idx_ne had]; norm_num
  have h2 : 2 • rt a a + rt (Sum.swap a) d ∉ Set.range (stdVec (n := n)) := by
    rw [e2]
    exact notMem_of_dot (by rw [dot_two had]; norm_num) (by rw [dot_two had]; norm_num)
  rw [epsWord_eq, ite_eq_right h2, coef_one_one_of_eq (by rw [e1, hn]), e1, e3,
    ite_eq_left (rt_mem (ne_swap_of_idx_ne had)), ite_eq_left (rt_mem (Ne.symm (swap_ne_self d))),
    one_mul, one_mul]

theorem epsWord_commLong (h0 : ∀ w, ξ w 0 = 1) (hab : idx a ≠ idx b) (s t : K) :
    epsWord ξ (rt a b) (rt a (Sum.swap b)) s t = 1 := by
  have e1 : rt a b + rt a (Sum.swap b) = rt a a := by simp only [rt, Sp.wt_swap]; abel
  have e2 : 2 • rt a b + rt a (Sum.swap b) = (3 : ℤ) • wt a + (1 : ℤ) • wt b := by
    simp only [rt, Sp.wt_swap]; module
  have e3 : rt a b + 2 • rt a (Sum.swap b) = (3 : ℤ) • wt a + (-1 : ℤ) • wt b := by
    simp only [rt, Sp.wt_swap]; module
  have hn : rt a a ⬝ᵥ rt a a = 4 := by rw [rt_dot_rt, Sp.dot_wt_self]; norm_num
  have h2 : 2 • rt a b + rt a (Sum.swap b) ∉ Set.range (stdVec (n := n)) := by
    rw [e2]
    exact notMem_of_dot (by rw [dot_two hab]; norm_num) (by rw [dot_two hab]; norm_num)
  have h3 : rt a b + 2 • rt a (Sum.swap b) ∉ Set.range (stdVec (n := n)) := by
    rw [e3]
    exact notMem_of_dot (by rw [dot_two hab]; norm_num) (by rw [dot_two hab]; norm_num)
  rw [epsWord_eq, ite_eq_right h2, ite_eq_right h3,
    coef_one_one_of_ne (by rw [e1, hn]; norm_num), zero_mul, zero_mul, h0]
  simp

theorem epsWord_comm (h0 : ∀ w, ξ w 0 = 1) (hab : b ≠ Sum.swap a) (hcd : d ≠ Sum.swap c)
    (hca : c ≠ Sum.swap a) (hcb : c ≠ Sum.swap b) (hda : d ≠ Sum.swap a) (hdb : d ≠ Sum.swap b)
    (s t : K) : epsWord ξ (rt a b) (rt c d) s t = 1 := by
  have huv : 0 ≤ rt a b ⬝ᵥ rt c d := by
    simp only [rt, add_dotProduct, dotProduct_add]
    have := wt_dot_nonneg hca
    have := wt_dot_nonneg hda
    have := wt_dot_nonneg hcb
    have := wt_dot_nonneg hdb
    omega
  have hu := rt_dot_rt a b
  have hv := rt_dot_rt c d
  have hab0 := wt_dot_nonneg hab
  have hcd0 := wt_dot_nonneg hcd
  have hsum : (rt a b + rt c d) ⬝ᵥ (rt a b + rt c d) =
      rt a b ⬝ᵥ rt a b + 2 * (rt a b ⬝ᵥ rt c d) + rt c d ⬝ᵥ rt c d := Sp.dot_add_self _ _
  have h2 : 2 • rt a b + rt c d ∉ Set.range (stdVec (n := n)) := by
    have e : (2 • rt a b + rt c d) ⬝ᵥ (2 • rt a b + rt c d) =
        4 * (rt a b ⬝ᵥ rt a b) + 4 * (rt a b ⬝ᵥ rt c d) + rt c d ⬝ᵥ rt c d := by
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
        dotProduct_comm (rt c d) (rt a b)]
      simp only [nsmul_eq_mul]
      push_cast
      ring
    exact notMem_of_dot (by rw [e]; omega) (by rw [e]; omega)
  have h3 : rt a b + 2 • rt c d ∉ Set.range (stdVec (n := n)) := by
    have e : (rt a b + 2 • rt c d) ⬝ᵥ (rt a b + 2 • rt c d) =
        rt a b ⬝ᵥ rt a b + 4 * (rt a b ⬝ᵥ rt c d) + 4 * (rt c d ⬝ᵥ rt c d) := by
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
        dotProduct_comm (rt c d) (rt a b)]
      simp only [nsmul_eq_mul]
      push_cast
      ring
    exact notMem_of_dot (by rw [e]; omega) (by rw [e]; omega)
  rw [epsWord_eq, ite_eq_right h2, ite_eq_right h3, coef_one_one_of_ne (by rw [hsum]; omega),
    zero_mul, zero_mul, h0]
  simp

end Families

end CFSG.Timmesfeld.Transvection.Pres
