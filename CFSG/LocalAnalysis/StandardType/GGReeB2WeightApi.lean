module

public import CFSG.LocalAnalysis.StandardType.GGReeB2WeightDefs
public import Mathlib.Combinatorics.Colex
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.StandardType.ReeB2Fixed

private theorem sum_range_two_pow (e : ℕ) :
    (∑ i ∈ Finset.range e, 2 ^ i : ℕ) = 2 ^ e - 1 := by
  have h := geom_sum_mul_of_one_le (x := (2 : ℕ)) (n := e) (by norm_num)
  simpa using h

private theorem sum_univ_two_pow (e : ℕ) :
    (∑ i : Fin e, 2 ^ (i : ℕ) : ℕ) = 2 ^ e - 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => 2 ^ i) e]
  exact sum_range_two_pow e

private theorem sum_filter_testBit (e n : ℕ) (hn : n < 2 ^ e) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin e => n.testBit (j : ℕ)), 2 ^ (j : ℕ)) = n := by
  rw [Finset.sum_filter]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if n.testBit i then 2 ^ i else 0) e]
  rw [← Finset.sum_filter]
  have hbits : (Finset.range e).filter (fun i => n.testBit i) = n.bitIndices.toFinset := by
    ext i
    rw [Finset.mem_filter, Finset.mem_range, List.mem_toFinset, Nat.mem_bitIndices]
    constructor
    · rintro ⟨_, hi⟩; exact hi
    · intro hi
      refine ⟨?_, hi⟩
      have h2 : 2 ^ i ≤ n := Nat.two_pow_le_of_mem_bitIndices (Nat.mem_bitIndices.mpr hi)
      have h3 : 2 ^ i < 2 ^ e := lt_of_le_of_lt h2 hn
      exact (pow_lt_pow_iff_right₀ (by norm_num : 1 < (2 : ℕ))).mp h3
  rw [hbits, Finset.sum_toFinset_bitIndices_two_pow]

private theorem two_pow_e_eq_one (m : ℕ) :
    (2 : ZMod (2 ^ (2 * m + 1) - 1)) ^ (2 * m + 1) = 1 := by
  have h1 : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
  have h2 : 2 ^ (2 * m + 1) = (2 ^ (2 * m + 1) - 1) + 1 := (Nat.sub_add_cancel h1).symm
  have h : ((2 ^ (2 * m + 1) : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) = 1 := by
    rw [h2, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add]
  rwa [Nat.cast_pow] at h

private theorem theta_mul_r (m : ℕ) :
    (2 ^ m : ZMod (2 ^ (2 * m + 1) - 1)) * 2 ^ (m + 1) = 1 := by
  rw [← pow_add]
  have hm : m + (m + 1) = 2 * m + 1 := by omega
  rw [hm]
  exact two_pow_e_eq_one m

private theorem one_add_theta_mul_R (m : ℕ) :
    (1 + 2 ^ m : ZMod (2 ^ (2 * m + 1) - 1)) * R (2 * m + 1) = 2 ^ m := by
  have hθr : (2 ^ m : ZMod (2 ^ (2 * m + 1) - 1)) * 2 ^ (m + 1) = 1 := theta_mul_r m
  have hr : (2 : ZMod (2 ^ (2 * m + 1) - 1)) ^ (m + 1) = 2 * 2 ^ m := by
    rw [pow_succ]; ring
  unfold R
  have hhalf : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  rw [hhalf]
  have h1 : (1 + 2 ^ m : ZMod (2 ^ (2 * m + 1) - 1)) * 2 ^ (m + 1) = 2 ^ (m + 1) + 1 := by
    rw [add_mul, one_mul, hθr]
  have h2 : (1 + 2 ^ m : ZMod (2 ^ (2 * m + 1) - 1)) * (2 ^ (m + 1) - 1)
      = 2 ^ (m + 1) - 2 ^ m := by
    rw [mul_sub, mul_one, h1, hr]; ring
  rw [h2, hr]; ring

private theorem one_add_theta_mul_inv (m : ℕ) :
    (1 + 2 ^ m : ZMod (2 ^ (2 * m + 1) - 1)) * (R (2 * m + 1) * 2 ^ (m + 1)) = 1 := by
  rw [← mul_assoc, one_add_theta_mul_R, theta_mul_r]

private theorem one_add_theta_mul_left_cancel (m : ℕ) {a b : ZMod (2 ^ (2 * m + 1) - 1)}
    (h : (1 + 2 ^ m) * a = (1 + 2 ^ m) * b) : a = b := by
  have huv := one_add_theta_mul_inv m
  have hvu : (R (2 * m + 1) * 2 ^ (m + 1)) * (1 + 2 ^ m) = 1 := by
    rw [mul_comm (R (2 * m + 1) * 2 ^ (m + 1)) (1 + 2 ^ m)]; exact huv
  have h1 : a = (R (2 * m + 1) * 2 ^ (m + 1)) * ((1 + 2 ^ m) * a) := by
    rw [← mul_assoc, hvu, one_mul]
  have h2 : (R (2 * m + 1) * 2 ^ (m + 1)) * ((1 + 2 ^ m) * a)
      = (R (2 * m + 1) * 2 ^ (m + 1)) * ((1 + 2 ^ m) * b) := by rw [h]
  have h3 : (R (2 * m + 1) * 2 ^ (m + 1)) * ((1 + 2 ^ m) * b) = b := by
    rw [← mul_assoc, hvu, one_mul]
  exact h1.trans (h2.trans h3)

private theorem one_add_theta_mul_eq_zero (m : ℕ) {a : ZMod (2 ^ (2 * m + 1) - 1)}
    (h : (1 + 2 ^ m) * a = 0) : a = 0 := by
  have h0 : (1 + 2 ^ m) * a = (1 + 2 ^ m) * 0 := by rw [h, mul_zero]
  exact one_add_theta_mul_left_cancel m h0

private theorem S_univ_eq_zero (m : ℕ) :
    S (2 * m + 1) (Finset.univ : Finset (Fin (2 * m + 1))) = 0 := by
  unfold S
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (2 : ZMod (2 ^ (2 * m + 1) - 1)) ^ i)]
  have hnat : (∑ i ∈ Finset.range (2 * m + 1), 2 ^ i : ℕ) = 2 ^ (2 * m + 1) - 1 :=
    sum_range_two_pow (2 * m + 1)
  have hcast : (∑ i ∈ Finset.range (2 * m + 1), (2 : ZMod (2 ^ (2 * m + 1) - 1)) ^ i)
      = ((∑ i ∈ Finset.range (2 * m + 1), 2 ^ i : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) := by
    push_cast; rfl
  rw [hcast, hnat]
  exact ZMod.natCast_self _

private theorem S_mem_Lam (m : ℕ) (J : Finset (Fin (2 * m + 1))) :
    S (2 * m + 1) J ∈ Lam (2 * m + 1) J := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro j _; simp [units]
  · simp [S]

private theorem neg_mem_units (m : ℕ) {u : ZMod (2 ^ (2 * m + 1) - 1)}
    (hu : u ∈ units (2 * m + 1)) : -u ∈ units (2 * m + 1) := by
  simp only [units, Finset.mem_insert, Finset.mem_singleton] at hu ⊢
  rcases hu with rfl | rfl | rfl | rfl <;> simp

private theorem neg_mem_Lam (m : ℕ) {J : Finset (Fin (2 * m + 1))}
    {z : ZMod (2 ^ (2 * m + 1) - 1)} (hz : z ∈ Lam (2 * m + 1) J) :
    -z ∈ Lam (2 * m + 1) J := by
  obtain ⟨c, hc, rfl⟩ := hz
  refine ⟨fun j => -c j, fun j hj => neg_mem_units m (hc j hj), ?_⟩
  have hneg : (∑ j ∈ J, (-c j) * 2 ^ (j : ℕ)) = -(∑ j ∈ J, c j * 2 ^ (j : ℕ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hneg]

private theorem theta_mul_eq_zero_iff (m : ℕ) (z : ZMod (2 ^ (2 * m + 1) - 1)) :
    (2 ^ m : ZMod (2 ^ (2 * m + 1) - 1)) * z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hvu : (2 ^ (m + 1) : ZMod (2 ^ (2 * m + 1) - 1)) * 2 ^ m = 1 := by
      rw [mul_comm (2 ^ (m + 1)) (2 ^ m)]; exact theta_mul_r m
    calc z = 1 * z := (one_mul z).symm
      _ = (2 ^ (m + 1) * 2 ^ m) * z := by rw [hvu]
      _ = 2 ^ (m + 1) * (2 ^ m * z) := by rw [mul_assoc]
      _ = 2 ^ (m + 1) * 0 := by rw [h]
      _ = 0 := mul_zero _
  · intro h; rw [h, mul_zero]

private theorem two_mul_eq_zero_iff (m : ℕ) (z : ZMod (2 ^ (2 * m + 1) - 1)) :
    (2 : ZMod (2 ^ (2 * m + 1) - 1)) * z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have h2 : (2 : ZMod (2 ^ (2 * m + 1) - 1)) * 2 ^ (2 * m) = 1 := by
      rw [← pow_succ']
      exact two_pow_e_eq_one m
    have hvu : (2 ^ (2 * m) : ZMod (2 ^ (2 * m + 1) - 1)) * 2 = 1 := by
      rw [mul_comm (2 ^ (2 * m)) 2]; exact h2
    calc z = 1 * z := (one_mul z).symm
      _ = (2 ^ (2 * m) * 2) * z := by rw [hvu]
      _ = 2 ^ (2 * m) * (2 * z) := by rw [mul_assoc]
      _ = 2 ^ (2 * m) * 0 := by rw [h]
      _ = 0 := mul_zero _
  · intro h; rw [h, mul_zero]

private theorem theta_mul_eq_iff (m : ℕ) (a b : ZMod (2 ^ (2 * m + 1) - 1)) :
    (2 ^ m : ZMod (2 ^ (2 * m + 1) - 1)) * a = 2 ^ m * b ↔ a = b := by
  constructor
  · intro h
    have h' : (2 ^ m : ZMod (2 ^ (2 * m + 1) - 1)) * (a - b) = 0 := by
      rw [mul_sub, h, sub_self]
    exact sub_eq_zero.mp ((theta_mul_eq_zero_iff m (a - b)).mp h')
  · intro h; rw [h]

private theorem theta_mul_sub_eq_zero_iff (m : ℕ) (x y : ZMod (2 ^ (2 * m + 1) - 1)) :
    (2 ^ m : ZMod (2 ^ (2 * m + 1) - 1)) * (y - x) = 0 ↔ y = x := by
  rw [theta_mul_eq_zero_iff, sub_eq_zero]

private theorem theta_mul_add_eq_zero_iff (m : ℕ) (x y : ZMod (2 ^ (2 * m + 1) - 1)) :
    (2 ^ m : ZMod (2 ^ (2 * m + 1) - 1)) * (x + y) = 0 ↔ y = -x := by
  rw [theta_mul_eq_zero_iff, add_eq_zero_iff_eq_neg']

private theorem theta_mul_sub_eq_mul_add_iff (m : ℕ) (x y : ZMod (2 ^ (2 * m + 1) - 1)) :
    (2 ^ m : ZMod (2 ^ (2 * m + 1) - 1)) * (y - x) = 2 ^ m * (x + y) ↔ x = 0 := by
  rw [theta_mul_eq_iff]
  constructor
  · intro h
    have h2 : (2 : ZMod (2 ^ (2 * m + 1) - 1)) * x = 0 := by
      have h3 : -(2 * x) = 0 := by
        have h4 : y - x - (x + y) = 0 := sub_eq_zero.mpr h
        rw [← h4]; ring
      exact neg_eq_zero.mp h3
    exact (two_mul_eq_zero_iff m x).mp h2
  · intro h; rw [h]; ring

private theorem theta_mul_sub_eq_neg_mul_add_iff (m : ℕ) (x y : ZMod (2 ^ (2 * m + 1) - 1)) :
    (2 ^ m : ZMod (2 ^ (2 * m + 1) - 1)) * (y - x) = -(2 ^ m * (x + y)) ↔ y = 0 := by
  rw [← mul_neg, theta_mul_eq_iff]
  constructor
  · intro h
    have h2 : (2 : ZMod (2 ^ (2 * m + 1) - 1)) * y = 0 := by
      have h3 : 2 * y = 0 := by
        have h4 : y - x - (-(x + y)) = 0 := sub_eq_zero.mpr h
        have h5 : y - x + (x + y) = 0 := by rw [← h4]; ring
        rw [← h5]; ring
      exact h3
    exact (two_mul_eq_zero_iff m y).mp h2
  · intro h; rw [h]; ring

private theorem sum_val_image {e : ℕ} (A : Finset (Fin e)) {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) : (∑ i ∈ A, f (i : ℕ)) = ∑ k ∈ A.image Fin.val, f k := by
  refine Finset.sum_bij (s := A) (t := A.image Fin.val)
    (f := fun i : Fin e => f (i : ℕ)) (g := f) (fun i _ => (i : ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  · intro i1 _ i2 _ h
    exact Fin.ext h
  · intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨i, hi, rfl⟩
  · intro i _
    rfl

theorem S_digits (m : ℕ) (x : ZMod (2 ^ (2 * m + 1) - 1)) :
    S (2 * m + 1) (digits (2 * m + 1) x) = x := by
  haveI : NeZero (2 ^ (2 * m + 1) - 1) :=
    ⟨by have h : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow; omega⟩
  have hlt : x.val < 2 ^ (2 * m + 1) := by
    have h1 : x.val < 2 ^ (2 * m + 1) - 1 := ZMod.val_lt x
    have h2 : 0 < 2 ^ (2 * m + 1) := Nat.two_pow_pos _
    omega
  unfold S digits
  calc ∑ j ∈ Finset.univ.filter (fun j : Fin (2 * m + 1) => x.val.testBit (j : ℕ)), 2 ^ (j : ℕ)
      = ((∑ j ∈ Finset.univ.filter (fun j : Fin (2 * m + 1) => x.val.testBit (j : ℕ)), 2 ^ (j : ℕ) : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) := by
        push_cast; rfl
    _ = (x.val : ZMod (2 ^ (2 * m + 1) - 1)) := by
        rw [sum_filter_testBit (2 * m + 1) x.val hlt]
    _ = x := ZMod.natCast_zmod_val x

theorem digits_S (m : ℕ) {A : Finset (Fin (2 * m + 1))} (hA : A ≠ Finset.univ) :
    digits (2 * m + 1) (S (2 * m + 1) A) = A := by
  set s : ℕ := ∑ i ∈ A, 2 ^ (i : ℕ) with hs
  have hS : S (2 * m + 1) A = (s : ZMod (2 ^ (2 * m + 1) - 1)) := by
    rw [hs]; unfold S; push_cast; rfl
  have hlt : s < 2 ^ (2 * m + 1) - 1 := by
    obtain ⟨j0, hj0⟩ : ∃ j0 : Fin (2 * m + 1), j0 ∉ A := by
      by_contra h
      push_neg at h
      exact hA (Finset.eq_univ_of_forall h)
    have hdisj : Disjoint A ({j0} : Finset (Fin (2 * m + 1))) := by
      rw [Finset.disjoint_singleton_right]; exact hj0
    have hle : (∑ i ∈ A ∪ {j0}, 2 ^ (i : ℕ)) ≤ ∑ i : Fin (2 * m + 1), 2 ^ (i : ℕ) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [Finset.sum_union hdisj, Finset.sum_singleton] at hle
    rw [sum_univ_two_pow] at hle
    rw [← hs] at hle
    have : 1 ≤ 2 ^ (j0 : ℕ) := Nat.one_le_two_pow
    omega
  have hval : (S (2 * m + 1) A).val = s := by
    rw [hS]; exact ZMod.val_natCast_of_lt hlt
  unfold digits
  rw [hval]
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hbits : s.bitIndices.toFinset = A.image Fin.val := by
    rw [hs, sum_val_image A (fun k => 2 ^ k)]
    exact Finset.toFinset_bitIndices_sum_two_pow _
  have hmem : s.testBit (j : ℕ) ↔ (j : ℕ) ∈ s.bitIndices.toFinset := by
    simp only [List.mem_toFinset, Nat.mem_bitIndices]
  rw [hmem, hbits, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, hav⟩
    rwa [Fin.ext hav] at ha
  · intro hj
    exact ⟨j, hj, rfl⟩

theorem hw_inj (m : ℕ) {I J : Finset (Fin (2 * m + 1))} (h : hw m I = hw m J)
    (h0 : hw m I ≠ 0) : I = J := by
  unfold hw at h
  have hcancel : S (2 * m + 1) I = S (2 * m + 1) J := one_add_theta_mul_left_cancel m h
  have hSI : S (2 * m + 1) I ≠ 0 := by
    intro hs
    apply h0
    unfold hw
    rw [hs, mul_zero]
  have hI : I ≠ Finset.univ := by
    intro hIu
    apply hSI
    rw [hIu]
    exact S_univ_eq_zero m
  have hJ : J ≠ Finset.univ := by
    intro hJu
    apply hSI
    rw [hcancel, hJu]
    exact S_univ_eq_zero m
  calc I = digits (2 * m + 1) (S (2 * m + 1) I) := (digits_S m hI).symm
    _ = digits (2 * m + 1) (S (2 * m + 1) J) := by rw [hcancel]
    _ = J := digits_S m hJ

theorem hw_mem_wtSet (m : ℕ) (J : Finset (Fin (2 * m + 1))) : hw m J ∈ wtSet m J := by
  unfold wtSet
  exact ⟨S (2 * m + 1) J, S_mem_Lam m J, rfl⟩

theorem exists_onLines_of_not_admissible (m : ℕ) {I J : Finset (Fin (2 * m + 1))}
    (h : ¬ Admissible (2 * m + 1) I J) : ∃ x ∈ wtSet m I, ∃ y ∈ wtSet m J, OnLines x y := by
  classical
  unfold Admissible Good at h
  rw [not_and_or, not_and_or] at h
  rcases h with hI | hJ | hD
  · have h0 : (0 : ZMod (2 ^ (2 * m + 1) - 1)) ∈ Lam (2 * m + 1) I := by
      by_contra hc
      exact hI (by simpa [Good] using hc)
    exact ⟨0, ⟨0, h0, by simp⟩, hw m J, hw_mem_wtSet m J, Or.inl rfl⟩
  · have h0 : (0 : ZMod (2 ^ (2 * m + 1) - 1)) ∈ Lam (2 * m + 1) J := by
      by_contra hc
      exact hJ (by simpa [Good] using hc)
    exact ⟨hw m I, hw_mem_wtSet m I, 0, ⟨0, h0, by simp⟩, Or.inr (Or.inl rfl)⟩
  · obtain ⟨z, hzI, hzJ⟩ := Set.not_disjoint_iff.mp hD
    exact ⟨(1 + 2 ^ m) * z, ⟨z, hzI, rfl⟩, (1 + 2 ^ m) * z, ⟨z, hzJ, rfl⟩,
      Or.inr (Or.inr (Or.inl rfl))⟩

theorem not_onLines_of_admissible (m : ℕ) {I J : Finset (Fin (2 * m + 1))}
    (h : Admissible (2 * m + 1) I J) {x y : ZMod (2 ^ (2 * m + 1) - 1)} (hx : x ∈ wtSet m I)
    (hy : y ∈ wtSet m J) : ¬ OnLines x y := by
  unfold Admissible Good at h
  obtain ⟨hgoodI, hgoodJ, hdisj⟩ := h
  obtain ⟨a, haI, rfl⟩ := hx
  obtain ⟨b, hbJ, rfl⟩ := hy
  intro hOn
  rw [OnLines] at hOn
  rcases hOn with h0 | h0 | heq | hneg
  · have ha0 : a = 0 := one_add_theta_mul_eq_zero m h0
    rw [ha0] at haI
    exact hgoodI haI
  · have hb0 : b = 0 := one_add_theta_mul_eq_zero m h0
    rw [hb0] at hbJ
    exact hgoodJ hbJ
  · have hab : a = b := one_add_theta_mul_left_cancel m heq
    rw [← hab] at hbJ
    exact (Set.disjoint_left.mp hdisj haI) hbJ
  · have hneg' : (1 + 2 ^ m) * a = (1 + 2 ^ m) * (-b) := by
      rw [mul_neg]; exact hneg
    have hab : a = -b := one_add_theta_mul_left_cancel m hneg'
    have hnb : -b ∈ Lam (2 * m + 1) J := neg_mem_Lam m hbJ
    rw [← hab] at hnb
    exact (Set.disjoint_left.mp hdisj haI) hnb

theorem onLines_sa_iff (m : ℕ) (x y : ZMod (2 ^ (2 * m + 1) - 1)) :
    OnLines (sa m (x, y)).1 (sa m (x, y)).2 ↔ OnLines x y := by
  simp only [sa, OnLines]
  rw [theta_mul_sub_eq_zero_iff, theta_mul_add_eq_zero_iff, theta_mul_sub_eq_mul_add_iff,
    theta_mul_sub_eq_neg_mul_add_iff]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inr (Or.inr (Or.inl h.symm))
    · exact Or.inr (Or.inr (Or.inr (by rw [h, neg_neg])))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rintro (h | h | h | h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl (by rw [h, neg_neg]))

end CFSG.StandardType.ReeB2Fixed
