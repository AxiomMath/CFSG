module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5Defs

public section

namespace CFSG.Quasithin.Stroth.G5

open Subgroup CFSG.Quasithin.OperatorJH

variable {G : Type} [Group G] {n : ℕ}

private theorem qv_zero_eq (Q₁ Q₂ : Subgroup G) (x₁ x₂ : G) : qv Q₁ Q₂ x₁ x₂ 0 = Q₁ := by
  ext y
  rw [mem_qv_iff]
  simp [trackElt, trackPar]

private theorem qv_one_eq (Q₁ Q₂ : Subgroup G) (x₁ x₂ : G) : qv Q₁ Q₂ x₁ x₂ 1 = Q₂ := by
  ext y
  rw [mem_qv_iff]
  simp [trackElt, trackPar]

private theorem relIndex_ne_zero_of_fin [Finite G] (H K : Subgroup G) : H.relIndex K ≠ 0 := by
  intro h
  have h1 := relIndex_dvd_card (H := H) (K := K)
  rw [h, zero_dvd_iff] at h1
  exact Nat.card_pos.ne' h1

private theorem le_iff_le_findGreatest {e : ℕ → ℕ} {k : ℕ} (hk : 1 ≤ k) (h1 : k ≤ e 1)
    (hanti : ∀ i j, 1 ≤ i → i ≤ j → e j ≤ e i) (hbd : ∀ m, 1 ≤ m → 1 ≤ e m → m ≤ 21) {m : ℕ}
    (hm : 1 ≤ m) : k ≤ e m ↔ m ≤ Nat.findGreatest (fun m => k ≤ e m) 21 := by
  constructor
  · intro h
    exact Nat.le_findGreatest (hbd m hm (hk.trans h)) h
  · intro h
    have hspec : k ≤ e (Nat.findGreatest (fun m => k ≤ e m) 21) :=
      Nat.findGreatest_spec (P := fun m => k ≤ e m) (m := 1) (by norm_num) h1
    exact hspec.trans (hanti m _ hm h)

namespace Conf

@[expose] noncomputable def dropExpS (c : Conf G n) (m : ℕ) : ℕ :=
  Nat.log (2 ^ n) (dropS c.Q₁ c.Q₂ c.x₁ c.x₂ m)

@[expose] noncomputable def dropExpL (c : Conf G n) (m : ℕ) : ℕ :=
  Nat.log (2 ^ n) (dropL c.Q₁ c.Q₂ c.x₁ c.x₂ m)

@[expose] noncomputable def pattern (c : Conf G n) : Pattern :=
  ⟨Nat.findGreatest (fun m => 2 ≤ c.dropExpS m) 21,
    Nat.findGreatest (fun m => 1 ≤ c.dropExpS m) 21,
    Nat.findGreatest (fun m => 1 ≤ c.dropExpL m) 21⟩

private theorem one_lt_q (c : Conf G n) : 1 < 2 ^ n :=
  Nat.one_lt_two_pow (by have := c.three_le; omega)

private theorem dropS_one (c : Conf G n) : dropS c.Q₁ c.Q₂ c.x₁ c.x₂ 1 = (2 ^ n) ^ 2 := by
  rw [dropS, Nat.cast_one, win_self, qv_zero_eq, qv_one_eq, c.relIndex₁]

private theorem dropL_one (c : Conf G n) : dropL c.Q₁ c.Q₂ c.x₁ c.x₂ 1 = 2 ^ n := by
  rw [dropL, Nat.cast_one, sub_self, win_self, qv_zero_eq, qv_one_eq, c.relIndex₂]

private theorem dropExpS_one (c : Conf G n) : c.dropExpS 1 = 2 := by
  rw [dropExpS, dropS_one, Nat.log_pow c.one_lt_q]

private theorem dropExpL_one (c : Conf G n) : c.dropExpL 1 = 1 := by
  have h := Nat.log_pow c.one_lt_q 1
  rw [pow_one] at h
  rw [dropExpL, dropL_one, h]

private theorem dropExpS_spec (c : Conf G n) {m : ℕ} (hm : 1 ≤ m) :
    c.dropExpS m ≤ 2 ∧ dropS c.Q₁ c.Q₂ c.x₁ c.x₂ m = (2 ^ n) ^ c.dropExpS m := by
  obtain ⟨d, hd, hdrop, -⟩ := c.baseS m hm
  have h : c.dropExpS m = d := by rw [dropExpS, hdrop, Nat.log_pow c.one_lt_q]
  rw [h]
  exact ⟨hd, hdrop⟩

private theorem dropExpL_spec (c : Conf G n) {m : ℕ} (hm : 1 ≤ m) :
    c.dropExpL m ≤ 1 ∧ dropL c.Q₁ c.Q₂ c.x₁ c.x₂ m = (2 ^ n) ^ c.dropExpL m := by
  obtain ⟨d, hd, hdrop, -⟩ := c.baseL m hm
  have h : c.dropExpL m = d := by rw [dropExpL, hdrop, Nat.log_pow c.one_lt_q]
  rw [h]
  exact ⟨hd, hdrop⟩

private theorem dropS_succ_le [Finite G] (c : Conf G n) (m : ℕ) :
    dropS c.Q₁ c.Q₂ c.x₁ c.x₂ (m + 1) ≤ dropS c.Q₁ c.Q₂ c.x₁ c.x₂ m := by
  unfold dropS
  exact relIndex_le_of_le_right (win_mono le_rfl (by omega)) (relIndex_ne_zero_of_fin _ _)

private theorem dropL_succ_le [Finite G] (c : Conf G n) (m : ℕ) :
    dropL c.Q₁ c.Q₂ c.x₁ c.x₂ (m + 1) ≤ dropL c.Q₁ c.Q₂ c.x₁ c.x₂ m := by
  unfold dropL
  exact relIndex_le_of_le_right (win_mono (by omega) le_rfl) (relIndex_ne_zero_of_fin _ _)

private theorem dropExpS_anti [Finite G] (c : Conf G n) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    c.dropExpS j ≤ c.dropExpS i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have h1 := (c.dropExpS_spec (hi.trans hij)).2
    have h2 := (c.dropExpS_spec (Nat.le_succ_of_le (hi.trans hij))).2
    have h3 := c.dropS_succ_le j
    rw [h1, h2] at h3
    exact ((Nat.pow_le_pow_iff_right c.one_lt_q).mp h3).trans ih

private theorem dropExpL_anti [Finite G] (c : Conf G n) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    c.dropExpL j ≤ c.dropExpL i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have h1 := (c.dropExpL_spec (hi.trans hij)).2
    have h2 := (c.dropExpL_spec (Nat.le_succ_of_le (hi.trans hij))).2
    have h3 := c.dropL_succ_le j
    rw [h1, h2] at h3
    exact ((Nat.pow_le_pow_iff_right c.one_lt_q).mp h3).trans ih

private theorem card_win_step (c : Conf G n) (a : ℤ) (m : ℕ) :
    Nat.card (win c.Q₁ c.Q₂ c.x₁ c.x₂ a (a + m - 1)) =
      (if Even (a + (m : ℤ)) then dropS c.Q₁ c.Q₂ c.x₁ c.x₂ m else dropL c.Q₁ c.Q₂ c.x₁ c.x₂ m) *
        Nat.card (win c.Q₁ c.Q₂ c.x₁ c.x₂ a (a + m)) := by
  rw [← c.track.rightDrop_eq c.le_normalizer₁ c.le_normalizer₂ a m]
  have hw : win c.Q₁ c.Q₂ c.x₁ c.x₂ a (a + m) =
      win c.Q₁ c.Q₂ c.x₁ c.x₂ a (a + m - 1) ⊓ qv c.Q₁ c.Q₂ c.x₁ c.x₂ (a + m) := by
    have := win_add_one_right (Q₁ := c.Q₁) (Q₂ := c.Q₂) (x₁ := c.x₁) (x₂ := c.x₂)
      (a := a) (b := a + m - 1) (by omega)
    rwa [sub_add_cancel] at this
  rw [hw, inf_comm, relIndex_mul_card]

private theorem card_win_mul_pow [Finite G] (c : Conf G n) (a : ℤ) {m : ℕ} (hm : 1 ≤ m) :
    Nat.card (win c.Q₁ c.Q₂ c.x₁ c.x₂ a (a + m - 1)) *
        (2 ^ n) ^ (∑ j ∈ Finset.Ico 1 m,
          if Even (a + (j : ℤ)) then c.dropExpS j else c.dropExpL j) =
      Nat.card (qv c.Q₁ c.Q₂ c.x₁ c.x₂ a) := by
  induction m, hm using Nat.le_induction with
  | base => simp [win_self]
  | succ m hm ih =>
    rw [Finset.sum_Ico_succ_top hm, pow_add]
    have h1 := c.card_win_step a m
    have h2 : (if Even (a + (m : ℤ)) then dropS c.Q₁ c.Q₂ c.x₁ c.x₂ m
        else dropL c.Q₁ c.Q₂ c.x₁ c.x₂ m) =
        (2 ^ n) ^ (if Even (a + (m : ℤ)) then c.dropExpS m else c.dropExpL m) := by
      split_ifs
      · exact (c.dropExpS_spec hm).2
      · exact (c.dropExpL_spec hm).2
    rw [h2] at h1
    have h3 : a + ((m + 1 : ℕ) : ℤ) - 1 = a + m := by push_cast; ring
    rw [h3, ← ih, h1]
    ring

private theorem card_win_eq_pow [Finite G] (c : Conf G n) (a : ℤ) {N : ℕ}
    (hN : Nat.card (qv c.Q₁ c.Q₂ c.x₁ c.x₂ a) = (2 ^ n) ^ N) {m : ℕ} (hm : 1 ≤ m) :
    (∑ j ∈ Finset.Ico 1 m, if Even (a + (j : ℤ)) then c.dropExpS j else c.dropExpL j) ≤ N ∧
      Nat.card (win c.Q₁ c.Q₂ c.x₁ c.x₂ a (a + m - 1)) = (2 ^ n) ^ (N - ∑ j ∈ Finset.Ico 1 m,
        if Even (a + (j : ℤ)) then c.dropExpS j else c.dropExpL j) := by
  have h := c.card_win_mul_pow a hm
  rw [hN] at h
  generalize (∑ j ∈ Finset.Ico 1 m,
    if Even (a + (j : ℤ)) then c.dropExpS j else c.dropExpL j) = s at h ⊢
  have hs : s ≤ N := (Nat.pow_dvd_pow_iff_le_right c.one_lt_q).mp (Dvd.intro_left _ h)
  refine ⟨hs, ?_⟩
  refine Nat.eq_of_mul_eq_mul_right (m := (2 ^ n) ^ s) (by positivity) ?_
  rw [h, ← pow_add, Nat.sub_add_cancel hs]

private theorem even_one_add_natCast (j : ℕ) : Even ((1 : ℤ) + j) ↔ ¬Even j := by
  rw [add_comm, Int.even_add_one, Int.even_coe_nat]

private theorem card_win_zero_pow [Finite G] (c : Conf G n) {m : ℕ} (hm : 1 ≤ m) :
    (∑ j ∈ Finset.Ico 1 m, if Even j then c.dropExpS j else c.dropExpL j) ≤ 10 ∧
      Nat.card (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 ((m : ℤ) - 1)) = (2 ^ n) ^ (10 - ∑ j ∈ Finset.Ico 1 m,
        if Even j then c.dropExpS j else c.dropExpL j) := by
  have := c.card_win_eq_pow 0 (N := 10) (by rw [qv_zero_eq, c.card₁]) hm
  simpa only [zero_add, Int.even_coe_nat] using this

private theorem card_win_one_pow [Finite G] (c : Conf G n) {m : ℕ} (hm : 1 ≤ m) :
    (∑ j ∈ Finset.Ico 1 m, if Even j then c.dropExpL j else c.dropExpS j) ≤ 11 ∧
      Nat.card (win c.Q₁ c.Q₂ c.x₁ c.x₂ 1 (m : ℤ)) = (2 ^ n) ^ (11 - ∑ j ∈ Finset.Ico 1 m,
        if Even j then c.dropExpL j else c.dropExpS j) := by
  have := c.card_win_eq_pow 1 (N := 11) (by rw [qv_one_eq, c.card₂]) hm
  simpa only [even_one_add_natCast, ite_not, add_sub_cancel_left] using this

private theorem le_twentyOne [Finite G] (c : Conf G n) {m : ℕ} (hm : 1 ≤ m)
    (h : 1 ≤ c.dropExpS m ∨ 1 ≤ c.dropExpL m) : m ≤ 21 := by
  have h0 := (c.card_win_zero_pow (m := m + 1) (by omega)).1
  have h1 := (c.card_win_one_pow (m := m + 1) (by omega)).1
  have hterm : ∀ j ∈ Finset.Ico 1 (m + 1), 1 ≤ (if Even j then c.dropExpS j else c.dropExpL j) +
      (if Even j then c.dropExpL j else c.dropExpS j) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hS := c.dropExpS_anti hj.1 (by omega : j ≤ m)
    have hL := c.dropExpL_anti hj.1 (by omega : j ≤ m)
    split_ifs <;> omega
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one] at hsum
  omega

private theorem le_two_dropExpS_iff [Finite G] (c : Conf G n) {m : ℕ} (hm : 1 ≤ m) :
    2 ≤ c.dropExpS m ↔ m ≤ c.pattern.s2 :=
  le_iff_le_findGreatest (e := c.dropExpS) (k := 2) (by norm_num) c.dropExpS_one.ge
    (fun _ _ hi hij => c.dropExpS_anti hi hij) (fun _ hm h => c.le_twentyOne hm (Or.inl h)) hm

private theorem one_le_dropExpS_iff [Finite G] (c : Conf G n) {m : ℕ} (hm : 1 ≤ m) :
    1 ≤ c.dropExpS m ↔ m ≤ c.pattern.s1 :=
  le_iff_le_findGreatest (e := c.dropExpS) (k := 1) le_rfl
    (by have := c.dropExpS_one; omega) (fun _ _ hi hij => c.dropExpS_anti hi hij)
    (fun _ hm h => c.le_twentyOne hm (Or.inl h)) hm

private theorem one_le_dropExpL_iff [Finite G] (c : Conf G n) {m : ℕ} (hm : 1 ≤ m) :
    1 ≤ c.dropExpL m ↔ m ≤ c.pattern.l1 :=
  le_iff_le_findGreatest (e := c.dropExpL) (k := 1) le_rfl c.dropExpL_one.ge
    (fun _ _ hi hij => c.dropExpL_anti hi hij) (fun _ hm h => c.le_twentyOne hm (Or.inr h)) hm

private theorem dropExpS_eq_dS [Finite G] (c : Conf G n) {m : ℕ} (hm : 1 ≤ m) :
    c.dropExpS m = c.pattern.dS m := by
  have h2 := c.le_two_dropExpS_iff hm
  have h1 := c.one_le_dropExpS_iff hm
  have hle := (c.dropExpS_spec hm).1
  unfold Pattern.dS
  split_ifs <;> omega

private theorem dropExpL_eq_dL [Finite G] (c : Conf G n) {m : ℕ} (hm : 1 ≤ m) :
    c.dropExpL m = c.pattern.dL m := by
  have h1 := c.one_le_dropExpL_iff hm
  have hle := (c.dropExpL_spec hm).1
  unfold Pattern.dL
  split_ifs <;> omega

theorem dropS_eq_pow [Finite G] (c : Conf G n) {m : ℕ} (hm : 1 ≤ m) :
    dropS c.Q₁ c.Q₂ c.x₁ c.x₂ m = (2 ^ n) ^ c.pattern.dS m := by
  rw [← c.dropExpS_eq_dS hm]
  exact (c.dropExpS_spec hm).2

theorem dropL_eq_pow [Finite G] (c : Conf G n) {m : ℕ} (hm : 1 ≤ m) :
    dropL c.Q₁ c.Q₂ c.x₁ c.x₂ m = (2 ^ n) ^ c.pattern.dL m := by
  rw [← c.dropExpL_eq_dL hm]
  exact (c.dropExpL_spec hm).2

theorem exists_ySeries_baseS [Finite G] (c : Conf G n) {m : ℕ} (hm : 1 ≤ m) :
    ∃ l, IsYSeries c.H (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 m) l (win c.Q₁ c.Q₂ c.x₁ c.x₂ 1 m) ∧
      facMultiset (chiLab c.ζ c.d₁ c.d₂) l (win c.Q₁ c.Q₂ c.x₁ c.x₂ 1 m) =
        clsSets (Pattern.contrib c.k₀ c.m₀ (-1) 0 (c.pattern.dS m)) := by
  obtain ⟨d, -, hdrop, l, hl, hfac⟩ := c.baseS m hm
  have hd : d = c.pattern.dS m :=
    Nat.pow_right_injective (Nat.succ_le_of_lt c.one_lt_q) (hdrop.symm.trans (c.dropS_eq_pow hm))
  subst hd
  exact ⟨l, hl, hfac⟩

theorem exists_ySeries_baseL [Finite G] (c : Conf G n) {m : ℕ} (hm : 1 ≤ m) :
    ∃ l, IsYSeries c.H (win c.Q₁ c.Q₂ c.x₁ c.x₂ (1 - m) 1) l
        (win c.Q₁ c.Q₂ c.x₁ c.x₂ (1 - m) 0) ∧
      facMultiset (chiLab c.ζ c.d₁ c.d₂) l (win c.Q₁ c.Q₂ c.x₁ c.x₂ (1 - m) 0) =
        clsSets (Pattern.contrib c.k₀ c.m₀ 1 1 (c.pattern.dL m)) := by
  obtain ⟨d, -, hdrop, l, hl, hfac⟩ := c.baseL m hm
  have hd : d = c.pattern.dL m :=
    Nat.pow_right_injective (Nat.succ_le_of_lt c.one_lt_q) (hdrop.symm.trans (c.dropL_eq_pow hm))
  subst hd
  exact ⟨l, hl, hfac⟩

private theorem eS_eq [Finite G] (c : Conf G n) (m : ℕ) :
    c.pattern.eS m = 10 - ((∑ j ∈ Finset.Ico 1 m,
      if Even j then c.dropExpS j else c.dropExpL j : ℕ) : ℤ) := by
  unfold Pattern.eS
  congr 1
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
  rw [c.dropExpS_eq_dS hj1, c.dropExpL_eq_dL hj1]

private theorem oS_eq [Finite G] (c : Conf G n) (m : ℕ) :
    c.pattern.oS m = 11 - ((∑ j ∈ Finset.Ico 1 m,
      if Even j then c.dropExpL j else c.dropExpS j : ℕ) : ℤ) := by
  unfold Pattern.oS
  congr 1
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
  rw [c.dropExpS_eq_dS hj1, c.dropExpL_eq_dL hj1]

theorem pattern_admissible [Finite G] (c : Conf G n) : c.pattern.Admissible := by
  have hs2 : 1 ≤ c.pattern.s2 := (c.le_two_dropExpS_iff le_rfl).mp c.dropExpS_one.ge
  refine ⟨hs2, ?_, ?_, ?_, ?_, ?_⟩
  · have h := (c.le_two_dropExpS_iff hs2).mpr le_rfl
    exact (c.one_le_dropExpS_iff hs2).mp (by omega)
  · exact (c.one_le_dropExpL_iff le_rfl).mp c.dropExpL_one.ge
  · intro m hm
    rw [c.eS_eq]
    have := (c.card_win_zero_pow hm).1
    omega
  · intro m hm
    rw [c.oS_eq]
    have := (c.card_win_one_pow hm).1
    omega
  · intro m hm he
    rw [c.eS_eq, c.oS_eq]
    obtain ⟨h0, h0'⟩ := c.card_win_zero_pow hm
    obtain ⟨h1, h1'⟩ := c.card_win_one_pow hm
    have h := c.track.card_win_zero_eq c.le_normalizer₁ c.le_normalizer₂ (m : ℤ)
      ((Int.even_coe_nat m).mpr he)
    rw [h0', h1'] at h
    have h2 := Nat.pow_right_injective (Nat.succ_le_of_lt c.one_lt_q) h
    omega

theorem card_win_zero [Finite G] (c : Conf G n) {m : ℕ} (hm : 1 ≤ m) :
    Nat.card (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 ((m : ℤ) - 1)) = (2 ^ n) ^ (c.pattern.eS m).toNat := by
  obtain ⟨h0, h0'⟩ := c.card_win_zero_pow hm
  rw [h0', c.eS_eq]
  congr 1
  omega

private theorem dropS_eq_one [Finite G] (c : Conf G n) {m : ℕ} (hm : c.pattern.J < m) :
    dropS c.Q₁ c.Q₂ c.x₁ c.x₂ m = 1 := by
  have h0 : c.pattern.dS m = 0 := by
    have hs := c.pattern_admissible.2.1
    unfold Pattern.dS
    unfold Pattern.J at hm
    split_ifs <;> omega
  rw [c.dropS_eq_pow (by omega), h0, pow_zero]

private theorem dropL_eq_one [Finite G] (c : Conf G n) {m : ℕ} (hm : c.pattern.J < m) :
    dropL c.Q₁ c.Q₂ c.x₁ c.x₂ m = 1 := by
  have h0 : c.pattern.dL m = 0 := by
    unfold Pattern.dL
    unfold Pattern.J at hm
    split_ifs <;> omega
  rw [c.dropL_eq_pow (by omega), h0, pow_zero]

private theorem win_succ_right [Finite G] (c : Conf G n) (a b : ℤ) (h : a + c.pattern.J ≤ b) :
    win c.Q₁ c.Q₂ c.x₁ c.x₂ a (b + 1) = win c.Q₁ c.Q₂ c.x₁ c.x₂ a b := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = b - a + 1 :=
    ⟨(b - a + 1).toNat, Int.toNat_of_nonneg (by omega)⟩
  have h1 := c.track.rightDrop_eq c.le_normalizer₁ c.le_normalizer₂ a m
  have e1 : a + (m : ℤ) = b + 1 := by omega
  have e2 : a + (m : ℤ) - 1 = b := by omega
  have hJ : c.pattern.J < m := by omega
  rw [e2, e1, c.dropS_eq_one hJ, c.dropL_eq_one hJ, ite_self, relIndex_eq_one] at h1
  have hw := win_add_one_right (Q₁ := c.Q₁) (Q₂ := c.Q₂) (x₁ := c.x₁) (x₂ := c.x₂)
    (a := a) (b := b) (by omega)
  rw [hw]
  exact inf_eq_left.mpr h1

private theorem win_pred_left [Finite G] (c : Conf G n) (a b : ℤ) (h : a + c.pattern.J ≤ b) :
    win c.Q₁ c.Q₂ c.x₁ c.x₂ (a - 1) b = win c.Q₁ c.Q₂ c.x₁ c.x₂ a b := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = b - a + 1 :=
    ⟨(b - a + 1).toNat, Int.toNat_of_nonneg (by omega)⟩
  have h1 := c.track.leftDrop_eq c.le_normalizer₁ c.le_normalizer₂ b m
  have e1 : b - (m : ℤ) = a - 1 := by omega
  have e2 : b - (m : ℤ) + 1 = a := by omega
  have hJ : c.pattern.J < m := by omega
  rw [e2, e1, c.dropS_eq_one hJ, c.dropL_eq_one hJ, ite_self, relIndex_eq_one] at h1
  have hw := win_sub_one_left (Q₁ := c.Q₁) (Q₂ := c.Q₂) (x₁ := c.x₁) (x₂ := c.x₂)
    (a := a) (b := b) (by omega)
  rw [hw]
  exact inf_eq_right.mpr h1

theorem win_eq_of_le [Finite G] (c : Conf G n) {a b : ℤ} (h : a + c.pattern.J ≤ b) :
    win c.Q₁ c.Q₂ c.x₁ c.x₂ a b = win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J := by
  have step : ∀ a : ℤ, win c.Q₁ c.Q₂ c.x₁ c.x₂ a (a + c.pattern.J) =
      win c.Q₁ c.Q₂ c.x₁ c.x₂ (a + 1) (a + 1 + c.pattern.J) := by
    intro a
    have h1 := c.win_succ_right a (a + c.pattern.J) le_rfl
    have h2 := c.win_pred_left (a + 1) (a + c.pattern.J + 1) (by omega)
    rw [add_sub_cancel_right] at h2
    rw [← h1, h2, show a + 1 + (c.pattern.J : ℤ) = a + c.pattern.J + 1 by ring]
  have all : ∀ a : ℤ, win c.Q₁ c.Q₂ c.x₁ c.x₂ a (a + c.pattern.J) =
      win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J := by
    intro a
    induction a using Int.induction_on with
    | zero => rw [zero_add]
    | succ i ih => rw [← step, ih]
    | pred i ih => rw [step, sub_add_cancel, ih]
  have ext : ∀ (k : ℕ) (a : ℤ), win c.Q₁ c.Q₂ c.x₁ c.x₂ a (a + c.pattern.J + k) =
      win c.Q₁ c.Q₂ c.x₁ c.x₂ a (a + c.pattern.J) := by
    intro k a
    induction k with
    | zero => rw [Nat.cast_zero, add_zero]
    | succ k ih =>
      rw [Nat.cast_succ, ← add_assoc, c.win_succ_right a (a + c.pattern.J + k) (by omega), ih]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, b = a + c.pattern.J + k := ⟨(b - a - c.pattern.J).toNat, by omega⟩
  rw [hk, ext, all]

theorem card_win_J [Finite G] (c : Conf G n) :
    Nat.card (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J) = (2 ^ n) ^ c.pattern.ell := by
  have h := c.card_win_zero (m := c.pattern.J + 1) (by omega)
  have e : (((c.pattern.J + 1 : ℕ) : ℤ) - 1) = (c.pattern.J : ℤ) := by push_cast; ring
  rw [e] at h
  exact h

theorem win_zero_seven_eq_bot [Finite G] (c : Conf G n) (h : c.pattern = Pattern.target) :
    win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 7 = ⊥ := by
  have hJ : c.pattern.J = 7 := by rw [h]; rfl
  have hell : c.pattern.ell = 0 := by rw [h]; decide
  have h1 := c.card_win_J
  rw [hell, pow_zero] at h1
  rw [c.win_eq_of_le (a := 0) (b := 7) (by omega)]
  exact eq_bot_of_card_eq _ h1

end Conf

end CFSG.Quasithin.Stroth.G5

end
