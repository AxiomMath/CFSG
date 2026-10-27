module

public import CFSG.LocalAnalysis.StandardType.GGDepASmall
public import Certificates.Data.DepASmall
public import CFSG.LocalAnalysis.StandardType.GGDepAPerm

public section

namespace CFSG.StandardType

open Certificates.DepASmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggDepANToZ (p N : ℕ) (l : List ℕ) : GGDepAE p N :=
  fun j => ((l.getD j.val 0 : ℕ) : ZMod p)

private lemma l05nNA_dot_eq_one {p N : ℕ} (a v : GGDepAE p N) (i : Fin N)
    (hzero : ∀ j : Fin N, j ≠ i → a j = 0) :
    ggDepAdot a v = a i * v i := by
  rw [ggDepAdot]
  rw [← Finset.sum_subset (Finset.subset_univ ({i} : Finset (Fin N))) (by
    intro x _ hx
    simp only [Finset.mem_singleton] at hx
    rw [hzero x hx, zero_mul])]
  rw [Finset.sum_singleton]

private lemma l05nNA_dot_sub {p N : ℕ} (a v w : GGDepAE p N) :
    ggDepAdot a (v - w) = ggDepAdot a v - ggDepAdot a w := by
  simp only [ggDepAdot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private lemma l05nNA_dot_add {p N : ℕ} (a v w : GGDepAE p N) :
    ggDepAdot a (v + w) = ggDepAdot a v + ggDepAdot a w := by
  simp only [ggDepAdot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma l05nNA_dot_one {p N : ℕ} (a : GGDepAE p N) :
    ggDepAdot a (1 : GGDepAE p N) = ∑ j : Fin N, a j := by
  simp only [ggDepAdot, Pi.one_apply, mul_one]

private lemma l05nNA_dot_single {p N : ℕ} (a : GGDepAE p N) (i : Fin N) :
    ggDepAdot a (Pi.single i 1) = a i := by
  rw [ggDepAdot]
  rw [← Finset.sum_subset (Finset.subset_univ ({i} : Finset (Fin N))) (by
    intro x _ hx
    simp only [Finset.mem_singleton] at hx
    rw [Pi.single_apply, if_neg hx, mul_zero])]
  rw [Finset.sum_singleton, Pi.single_eq_same, mul_one]

private lemma l05nNA_dot_x {p N : ℕ} (hN : 1 ≤ N) (a : GGDepAE p N) :
    ggDepAdot a (ggDepAx p N) = a ⟨N-1, by omega⟩ := by
  rw [ggDepAdot]
  rw [← Finset.sum_subset (Finset.subset_univ ({⟨N-1, by omega⟩} : Finset (Fin N))) (by
    intro x _ hx
    simp only [Finset.mem_singleton] at hx
    rw [ggDepAx, if_neg (by intro hh; exact hx (Fin.ext (by simp only [Fin.val_mk]; omega))),
      mul_zero])]
  rw [Finset.sum_singleton, ggDepAx, if_pos (by omega : N - 1 + 1 = N), mul_one]

private lemma l05nNA_sum_univ_last {p N : ℕ} (hN : 1 ≤ N) (f : Fin N → ZMod p) :
    (∑ j : Fin N, f j) = (∑ j : Fin (N-1), f ⟨j.val, by omega⟩) + f ⟨N-1, by omega⟩ := by
  have keyN : (∑ j : Fin N, f ⟨j.val, by omega⟩) =
      ∑ i ∈ Finset.range N, (if h : i < N then f ⟨i, h⟩ else 0) := by
    calc (∑ j : Fin N, f ⟨j.val, by omega⟩)
        = ∑ j : Fin N, (if h : j.val < N then f ⟨j.val, h⟩ else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [dif_pos j.isLt]
      _ = ∑ i ∈ Finset.range N, (if h : i < N then f ⟨i, h⟩ else 0) :=
          Fin.sum_univ_eq_sum_range (fun i => if h : i < N then f ⟨i, h⟩ else 0) N
  have keyN1 : (∑ j : Fin (N-1), f ⟨j.val, by omega⟩) =
      ∑ i ∈ Finset.range (N-1), (if h : i < N then f ⟨i, h⟩ else 0) := by
    calc (∑ j : Fin (N-1), f ⟨j.val, by omega⟩)
        = ∑ j : Fin (N-1), (if h : j.val < N then f ⟨j.val, h⟩ else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [dif_pos (by omega : j.val < N)]
      _ = ∑ i ∈ Finset.range (N-1), (if h : i < N then f ⟨i, h⟩ else 0) :=
          Fin.sum_univ_eq_sum_range (fun i => if h : i < N then f ⟨i, h⟩ else 0) (N-1)
  have hfin : (∑ j : Fin N, f j) = ∑ j : Fin N, f ⟨j.val, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro j _
    rfl
  rw [hfin, keyN, keyN1]
  have hr : Finset.range N = Finset.range (N - 1 + 1) := by rw [Nat.sub_add_cancel hN]
  rw [hr, Finset.sum_range_succ]
  congr 1
  rw [dif_pos (by omega : N - 1 < N)]

private lemma l05nNA_h_last_eq {p N : ℕ} (c : Fin (N-1)) (hc : c.val + 2 = N) :
    ggDepAh p N c = (1 : GGDepAE p N) - ggDepAx p N + Pi.single ⟨N-2, by omega⟩ 1 := by
  funext j
  simp only [ggDepAh, ggDepAx, Pi.sub_apply, Pi.add_apply, Pi.one_apply, Pi.single_apply]
  by_cases h : j.val + 1 = N
  · rw [if_pos h, if_pos h]
    have h3 : ¬ (j = ⟨N-2, by omega⟩) := by
      intro hh; rw [Fin.ext_iff] at hh; simp only [Fin.val_mk] at hh; omega
    rw [if_neg h3]
    ring
  · rw [if_neg h, if_neg h, if_pos hc]
    by_cases hjv : j.val = c.val
    · have hje : j = ⟨N-2, by omega⟩ := by
        apply Fin.ext; simp only [Fin.val_mk]; omega
      rw [if_pos hjv, if_neg (by omega : ¬ (j.val = c.val + 1)), if_pos hje]
    · have hje : ¬ (j = ⟨N-2, by omega⟩) := by
        intro hh; rw [Fin.ext_iff] at hh; simp only [Fin.val_mk] at hh; omega
      rw [if_neg hjv, if_neg (by omega : ¬ (j.val = c.val + 1)), if_neg hje]
      ring

private lemma l05nNA_dot_h_last {p N : ℕ} (hN : 1 ≤ N) (aa : GGDepAE p N) (c : Fin (N-1))
    (hc : c.val + 2 = N) :
    ggDepAdot aa (ggDepAh p N c) =
      (∑ j : Fin (N-1), aa ⟨j.val, by omega⟩) + aa ⟨N-2, by omega⟩ := by
  rw [l05nNA_h_last_eq c hc, l05nNA_dot_add, l05nNA_dot_sub, l05nNA_dot_one, l05nNA_dot_x hN,
      l05nNA_dot_single,
    l05nNA_sum_univ_last hN aa]
  rw [add_sub_cancel_right]

private lemma l05nNA_alpha_apply {p N : ℕ} (c : Fin (N - 1)) (hc : c.val + 2 < N) (j : Fin N) :
    ggDepAα p N c j = (if j.val = c.val then 1 else 0) - (if j.val = c.val + 1 then 1 else 0) := by
  simp only [ggDepAα]
  by_cases h : j.val + 1 = N
  · rw [if_pos h]
    have h1 : j.val ≠ c.val := by omega
    have h2 : j.val ≠ c.val + 1 := by omega
    rw [if_neg h1, if_neg h2, sub_zero]
  · rw [if_neg h]

private lemma l05nNA_h_apply_short {p N : ℕ} (c : Fin (N - 1)) (hc : c.val + 2 < N) (j : Fin N) :
    ggDepAh p N c j = (if j.val = c.val then 1 else 0) - (if j.val = c.val + 1 then 1 else 0) := by
  simp only [ggDepAh]
  by_cases h : j.val + 1 = N
  · rw [if_pos h]
    have h1 : j.val ≠ c.val := by omega
    have h2 : j.val ≠ c.val + 1 := by omega
    rw [if_neg h1, if_neg h2]
    ring
  · rw [if_neg h, if_neg (by omega : ¬ (c.val + 2 = N)), add_zero]

private lemma l05nNA_dot_eq_two {p N : ℕ} (a v : GGDepAE p N) (i k : Fin N) (hik : i ≠ k)
    (hzero : ∀ j : Fin N, j ≠ i → j ≠ k → a j = 0) :
    ggDepAdot a v = a i * v i + a k * v k := by
  rw [ggDepAdot]
  rw [← Finset.sum_subset (Finset.subset_univ ({i, k} : Finset (Fin N)))]
  · rw [Finset.sum_pair hik]
  · intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    push Not at hx
    rw [hzero x hx.1 hx.2, zero_mul]

private lemma l05nNA_dot_eq_two' {p N : ℕ} (v a : GGDepAE p N) (i k : Fin N) (hik : i ≠ k)
    (hzero : ∀ j : Fin N, j ≠ i → j ≠ k → a j = 0) :
    ggDepAdot v a = v i * a i + v k * a k := by
  have h : ggDepAdot v a = ggDepAdot a v := by
    simp only [ggDepAdot]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
  rw [h, l05nNA_dot_eq_two a v i k hik hzero]
  ring

private lemma l05nNA_dot_alpha_short {p N : ℕ} (ha : GGDepAE p N) (c : Fin (N-1))
    (hc : c.val + 2 < N) :
    ggDepAdot (ggDepAα p N c) ha = ha ⟨c.val, by omega⟩ - ha ⟨c.val+1, by omega⟩ := by
  have hzero : ∀ j : Fin N, j ≠ ⟨c.val, by omega⟩ → j ≠ ⟨c.val+1, by omega⟩ →
      ggDepAα p N c j = 0 := by
    intro j hj1 hj2
    rw [l05nNA_alpha_apply c hc j, if_neg (fun hh => hj1 (Fin.ext hh)),
      if_neg (fun hh => hj2 (Fin.ext hh))]
    ring
  rw [l05nNA_dot_eq_two (ggDepAα p N c) ha ⟨c.val, by omega⟩ ⟨c.val+1, by omega⟩
    (by intro hh; rw [Fin.ext_iff] at hh; simp only [Fin.val_mk] at hh; omega) hzero]
  have h1 : ggDepAα p N c ⟨c.val, by omega⟩ = 1 := by
    rw [l05nNA_alpha_apply c hc]
    rw [if_pos rfl, if_neg (by omega : ¬ (c.val = c.val + 1))]
    ring
  have h2 : ggDepAα p N c ⟨c.val+1, by omega⟩ = -1 := by
    rw [l05nNA_alpha_apply c hc]
    rw [if_neg (by omega : ¬ (c.val + 1 = c.val)), if_pos rfl]
    ring
  rw [h1, h2]
  ring

private lemma l05nNA_dot_alpha_last {p N : ℕ} (ha : GGDepAE p N) (c : Fin (N-1))
    (hc : c.val + 2 = N) :
    ggDepAdot (ggDepAα p N c) ha = ha ⟨N-2, by omega⟩ := by
  have hzero : ∀ j : Fin N, j ≠ ⟨N-2, by omega⟩ → ggDepAα p N c j = 0 := by
    intro j hj
    simp only [ggDepAα]
    by_cases h : j.val + 1 = N
    · rw [if_pos h]
    · rw [if_neg h]
      have h1 : j.val ≠ c.val := by
        intro hh; exact hj (Fin.ext (by simp only [Fin.val_mk]; omega))
      have h2 : j.val ≠ c.val + 1 := by omega
      rw [if_neg h1, if_neg h2, sub_zero]
  rw [l05nNA_dot_eq_one (ggDepAα p N c) ha ⟨N-2, by omega⟩ hzero]
  have hone : ggDepAα p N c ⟨N-2, by omega⟩ = 1 := by
    simp only [ggDepAα]
    rw [if_neg (by omega : ¬ (N - 2 + 1 = N)),
      if_pos (by omega : (N - 2 : ℕ) = c.val),
      if_neg (by omega : ¬ ((N - 2 : ℕ) = c.val + 1))]
    ring
  rw [hone, one_mul]

private lemma l05nNA_dot_h_short {p N : ℕ} (aa : GGDepAE p N) (c : Fin (N-1))
    (hc : c.val + 2 < N) :
    ggDepAdot aa (ggDepAh p N c) = aa ⟨c.val, by omega⟩ - aa ⟨c.val+1, by omega⟩ := by
  rw [l05nNA_dot_eq_two' aa (ggDepAh p N c) ⟨c.val, by omega⟩ ⟨c.val+1, by omega⟩
    (by intro hh; rw [Fin.ext_iff] at hh; simp only [Fin.val_mk] at hh; omega) (by
      intro j hj1 hj2
      rw [l05nNA_h_apply_short c hc j, if_neg (fun hh => hj1 (Fin.ext hh)),
        if_neg (fun hh => hj2 (Fin.ext hh))]
      ring)]
  have h1 : ggDepAh p N c ⟨c.val, by omega⟩ = 1 := by
    rw [l05nNA_h_apply_short c hc]
    rw [if_pos rfl, if_neg (by omega : ¬ (c.val = c.val + 1))]
    ring
  have h2 : ggDepAh p N c ⟨c.val+1, by omega⟩ = -1 := by
    rw [l05nNA_h_apply_short c hc]
    rw [if_neg (by omega : ¬ (c.val + 1 = c.val)), if_pos rfl]
    ring
  rw [h1, h2]
  ring

private lemma l05nNA_sum_fin_lt {p : ℕ} (m : ZMod p) {M c : ℕ} (hc : c ≤ M) :
    (∑ i : Fin M, (if i.val < c then m else 0)) = (c : ZMod p) * m := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (if i < c then m else 0)) M]
  have hM : c + (M - c) = M := by omega
  conv_lhs => rw [← hM]
  rw [Finset.sum_range_add]
  have h1 : (∑ x ∈ Finset.range c, (if x < c then m else 0)) = c • m := by
    rw [Finset.sum_congr rfl (fun x hx => by rw [if_pos (Finset.mem_range.mp hx)])]
    rw [Finset.sum_const, Finset.card_range]
  have h2 : (∑ x ∈ Finset.range (M - c), (if c + x < c then m else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [if_neg (by omega)]
  rw [h1, h2, add_zero, nsmul_eq_mul]

private lemma l05nNA_tail_eq {p : ℕ} (f : ℕ → ZMod p) (n0 : ZMod p) (c M : ℕ)
    (hcM : c ≤ M) (hM : f M = if c = M then n0 else 0)
    (hstep : ∀ k, 1 ≤ k → k < M → f k = f (k + 1) + if k = c then n0 else 0) :
    ∀ k, 1 ≤ k → k ≤ M → f k = if k ≤ c then n0 else 0 := by
  suffices h : ∀ d k, M - k = d → 1 ≤ k → k ≤ M → f k = if k ≤ c then n0 else 0 by
    intro k hk1 hkM
    exact h (M - k) k rfl hk1 hkM
  intro d
  induction d with
  | zero =>
    intro k hd hk1 hkM
    have hkM' : k = M := by omega
    rw [hkM', hM]
    by_cases h : c = M
    · rw [if_pos h, if_pos (by omega : M ≤ c)]
    · rw [if_neg h, if_neg (by omega : ¬ (M ≤ c))]
  | succ d ih =>
    intro k hd hk1 hkM
    have hklt : k < M := by omega
    have ih' := ih (k+1) (by omega) (by omega) (by omega)
    rw [hstep k hk1 hklt, ih']
    by_cases h1 : k = c
    · rw [if_neg (by omega : ¬ (k + 1 ≤ c)), if_pos h1, if_pos (by omega : k ≤ c)]
      ring
    · by_cases h2 : k < c
      · rw [if_pos (by omega : k + 1 ≤ c), if_neg h1, if_pos (by omega : k ≤ c)]
        ring
      · rw [if_neg (by omega : ¬ (k + 1 ≤ c)), if_neg h1, if_neg (by omega : ¬ (k ≤ c))]
        ring

private lemma l05nNA_prefix_eq {p : ℕ} (f : ℕ → ZMod p) (n0 : ZMod p) (c M : ℕ)
    (hcM : c ≤ M) (h0 : f 0 = 0)
    (hstep : ∀ k, k < M → f (k + 1) = f k - (if k = c then n0 else 0)) :
    ∀ k, k ≤ M → f k = if k ≤ c then 0 else -n0 := by
  suffices h : ∀ k, k ≤ M → f k = if k ≤ c then 0 else -n0 by
    intro k hk; exact h k hk
  intro k
  induction k with
  | zero => intro _; rw [h0, if_pos (by omega : 0 ≤ c)]
  | succ k ih =>
    intro hk1
    have hklt : k < M := by omega
    rw [hstep k hklt, ih (by omega)]
    by_cases h1 : k = c
    · rw [if_pos (by omega : k ≤ c), if_pos h1, if_neg (by omega : ¬ (k + 1 ≤ c))]
      ring
    · by_cases h2 : k < c
      · rw [if_pos (by omega : k ≤ c), if_neg h1, if_pos (by omega : k + 1 ≤ c)]
        ring
      · rw [if_neg (by omega : ¬ (k ≤ c)), if_neg h1, if_neg (by omega : ¬ (k + 1 ≤ c))]
        ring

@[simp] private lemma l05nNA_getD_map_range {N : ℕ} (F : ℕ → ℕ) (j : ℕ) (hj : j < N) :
    (((List.range N).map F).getD j 0) = F j := by
  simp [List.getD_eq_getElem?_getD, hj]

private lemma l05nNA_getD_paramHa {p N b c0 n s t : ℕ} (j : ℕ) (hj : j < N) :
    ((ggDepANHaParam p N b c0 n s t).getD j 0) =
      (if j + 1 = N then t % p
       else if b = 0 then (if j = 0 then s % p else if j ≤ c0 then n % p else 0)
       else (s + (if j ≤ c0 then n else 0)) % p) := by
  rw [ggDepANHaParam]
  exact l05nNA_getD_map_range (fun k => if k + 1 = N then t % p
    else if b = 0 then (if k = 0 then s % p else if k ≤ c0 then n % p else 0)
    else (s + (if k ≤ c0 then n else 0)) % p) j hj

private lemma l05nNA_getD_paramAa {p N b c0 m u v : ℕ} (j : ℕ) (hj : j < N) :
    ((ggDepANAaParam p N b c0 m u v).getD j 0) =
      (if j + 1 = N then v % p
       else if b = 0 then
        (if j = 0 then (if c0 + 2 = N then (m + u) % p else (u + (p - (m * c0) % p)) % p)
          else if c0 + 2 = N then u % p else if j ≤ c0 then (u + m) % p else u % p)
       else (u + (if j ≤ c0 then m else 0)) % p) := by
  rw [ggDepANAaParam]
  exact l05nNA_getD_map_range (fun k => if k + 1 = N then v % p
    else if b = 0 then
      (if k = 0 then (if c0 + 2 = N then (m + u) % p else (u + (p - (m * c0) % p)) % p)
        else if c0 + 2 = N then u % p else if k ≤ c0 then (u + m) % p else u % p)
    else (u + (if k ≤ c0 then m else 0)) % p) j hj

private lemma l05nNA_sum_fin_pred {p N : ℕ} (hN : 2 ≤ N) (f : Fin (N-1) → ZMod p) :
    (∑ j : Fin (N-1), f j) = (∑ i : Fin (N-2), f ⟨i.val + 1, by omega⟩) + f ⟨0, by omega⟩ := by
  have keyN : (∑ j : Fin (N-1), f j) =
      ∑ j ∈ Finset.range (N-1), (if h : j < N-1 then f ⟨j,h⟩ else 0) := by
    calc (∑ j : Fin (N-1), f j) =
        ∑ j : Fin (N-1), (if h : j.val < N-1 then f ⟨j.val,h⟩ else 0) := by
          apply Finset.sum_congr rfl; intro j _; rw [dif_pos j.isLt]
      _ = ∑ j ∈ Finset.range (N-1), (if h : j < N-1 then f ⟨j,h⟩ else 0) :=
          Fin.sum_univ_eq_sum_range (fun j => if h : j < N-1 then f ⟨j,h⟩ else 0) (N-1)
  have keyN1 : (∑ i : Fin (N-2), f ⟨i.val + 1, by omega⟩) =
      ∑ i ∈ Finset.range (N-2), (if h : i + 1 < N-1 then f ⟨i+1, h⟩ else 0) := by
    calc (∑ i : Fin (N-2), f ⟨i.val + 1, by omega⟩)
        = ∑ i : Fin (N-2), (if h : i.val + 1 < N-1 then f ⟨i.val+1, h⟩ else 0) := by
          apply Finset.sum_congr rfl; intro i _; rw [dif_pos (by omega : i.val+1 < N-1)]
      _ = ∑ i ∈ Finset.range (N-2), (if h : i + 1 < N-1 then f ⟨i+1, h⟩ else 0) :=
          Fin.sum_univ_eq_sum_range (fun i => if h : i + 1 < N-1 then f ⟨i+1, h⟩ else 0) (N-2)
  have hr : Finset.range (N-1) = Finset.range (N - 2 + 1) := by congr 1; omega
  rw [keyN, keyN1, hr, Finset.sum_range_succ', dif_pos (by omega : 0 < N-1)]

private lemma l05nNA_natCast_psub {p k : ℕ} (hk : k ≤ p) :
    ((p - k : ℕ) : ZMod p) = -((k : ℕ) : ZMod p) := by
  have h : ((p - k : ℕ) : ZMod p) + (k : ZMod p) = 0 := by
    rw [← Nat.cast_add, Nat.sub_add_cancel hk, ZMod.natCast_self]
  exact eq_neg_of_add_eq_zero_left h

private lemma l05nNA_fin_if_eq {p N : ℕ} (k : ℕ) (hk : k < N - 1) (c0 : Fin (N - 1))
    (a b : ZMod p) :
    (if (⟨k, hk⟩ : Fin (N - 1)) = c0 then a else b) = (if k = c0.val then a else b) := by
  by_cases hh : k = c0.val
  · rw [if_pos (by apply Fin.ext; simp only [Fin.val_mk]; exact hh), if_pos hh]
  · have hne : (⟨k, hk⟩ : Fin (N - 1)) ≠ c0 := by
      intro hh'; rw [Fin.ext_iff] at hh'; simp only [Fin.val_mk] at hh'; exact hh hh'
    rw [if_neg hne, if_neg hh]

private lemma l05nNA_fin_if_eq' {p N : ℕ} (k : ℕ) (hk : k < N - 1) (c0 : Fin (N - 1))
    (a b : ZMod p) :
    (if (⟨k, hk⟩ : Fin (N - 1)) = c0 then a else b) = (if c0.val = k then a else b) := by
  by_cases hh : c0.val = k
  · rw [if_pos (by apply Fin.ext; simp only [Fin.val_mk]; omega), if_pos hh]
  · have hne : (⟨k, hk⟩ : Fin (N - 1)) ≠ c0 := by
      intro hh'; rw [Fin.ext_iff] at hh'; simp only [Fin.val_mk] at hh'; exact hh hh'.symm
    rw [if_neg hne, if_neg hh]

private lemma l05nNA_hc_lt {N k : ℕ} (hk : k < N - 1) (h : k + 2 < N) :
    ((⟨k, hk⟩ : Fin (N - 1)).val + 2 < N) := by simpa [Fin.val_mk] using h

private lemma l05nNA_hc_eq {N k : ℕ} (hk : k < N - 1) (h : k + 2 = N) :
    ((⟨k, hk⟩ : Fin (N - 1)).val + 2 = N) := by simpa [Fin.val_mk] using h

private lemma l05nNA_fin_ne {N : ℕ} (k : ℕ) (hk : k < N - 1) (b : Fin (N - 1)) (h : k ≠ b.val) :
    (⟨k, hk⟩ : Fin (N - 1)) ≠ b := by
  intro hh; exact h (by simpa [Fin.val_mk] using congrArg Fin.val hh)

private lemma l05nNA_fin_eq_of_val {N : ℕ} (j : Fin N) (k : ℕ) (hk : k < N) (h : j.val = k) :
    j = ⟨k, hk⟩ := Fin.ext h

private lemma l05nNA_fin_eq_of_val' {N : ℕ} (k : ℕ) (hk : k < N - 1) (c0 : Fin (N - 1))
    (h : k = c0.val) : (⟨k, hk⟩ : Fin (N - 1)) = c0 := Fin.ext h

private lemma l05nNA_fin_eq_last {N : ℕ} (j : Fin N) (h : j.val + 1 = N) :
    j = ⟨N - 1, by omega⟩ := by
  apply Fin.ext; show j.val = N - 1; omega

theorem ggDepANHa_complete {p N : ℕ} [Fact p.Prime] (hN : 5 ≤ N) (b c0 : Fin (N - 1))
    (hb : b.val = 0 ∨ b.val + 2 = N) (hbc : c0 ≠ b) (n : ℕ) (ha : GGDepAE p N)
    (h : ∀ c : Fin (N - 1), c ≠ b →
      ggDepAdot (ggDepAα p N c) ha = if c = c0 then (n : ZMod p) else 0) :
    ∃ s t : ℕ, ha = ggDepANToZ p N (ggDepANHaParam p N b.val c0.val n s t) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rcases hb with hb0 | hbN
  · refine ⟨(ha ⟨0, by omega⟩).val, (ha ⟨N-1, by omega⟩).val, ?_⟩
    have htail : ∀ k, 1 ≤ k → k ≤ N - 2 →
        (if h : k < N then ha ⟨k, h⟩ else 0) = if k ≤ c0.val then (n : ZMod p) else 0 := by
      apply l05nNA_tail_eq (fun k => if h : k < N then ha ⟨k, h⟩ else 0) (n : ZMod p) c0.val (N - 2)
      · have := c0.isLt; omega
      · rw [dif_pos (by omega : N - 2 < N)]
        have hc' := l05nNA_fin_ne (N-2) (by omega) b (by omega)
        have hcon := h ⟨N - 2, by omega⟩ hc'
        rw [l05nNA_dot_alpha_last ha ⟨N - 2, by omega⟩ (l05nNA_hc_eq (by omega) (by omega))] at hcon
        rw [hcon, l05nNA_fin_if_eq' (N - 2) (by omega) c0]
      · intro k hk1 hklt
        rw [dif_pos (by omega : k < N), dif_pos (by omega : k + 1 < N)]
        have hc' := l05nNA_fin_ne k (by omega) b (by omega)
        have hcon := h ⟨k, by omega⟩ hc'
        rw [l05nNA_dot_alpha_short ha ⟨k, by omega⟩ (l05nNA_hc_lt (by omega) (by omega)),
          sub_eq_iff_eq_add] at hcon
        rw [hcon, l05nNA_fin_if_eq k (by omega) c0]
        ring
    funext j
    show ha j = (((ggDepANHaParam p N b.val c0.val n (ha ⟨0, by omega⟩).val
      (ha ⟨N - 1, by omega⟩).val).getD j.val 0 : ℕ) : ZMod p)
    rw [l05nNA_getD_paramHa j.val j.isLt, if_pos hb0]
    by_cases hj1 : j.val + 1 = N
    · rw [if_pos hj1, l05nNA_fin_eq_last j hj1, ZMod.natCast_mod]
      exact (ZMod.natCast_zmod_val (ha ⟨N - 1, by omega⟩)).symm
    · rw [if_neg hj1]
      by_cases hj0 : j.val = 0
      · rw [if_pos hj0, l05nNA_fin_eq_of_val j 0 (by omega) (by omega), ZMod.natCast_mod]
        exact (ZMod.natCast_zmod_val (ha ⟨0, by omega⟩)).symm
      · rw [if_neg hj0]
        have hcoord := htail j.val (by omega) (by omega)
        rw [dif_pos (by omega : j.val < N)] at hcoord
        have hcast : ((if j.val ≤ c0.val then n % p else 0 : ℕ) : ZMod p) =
            (if j.val ≤ c0.val then (n : ZMod p) else 0) := by
          by_cases hh : j.val ≤ c0.val <;> simp [hh, ZMod.natCast_mod]
        rw [hcast]
        simpa using hcoord
  · refine ⟨(ha ⟨0, by omega⟩ - (n : ZMod p)).val, (ha ⟨N-1, by omega⟩).val, ?_⟩
    have hpref : ∀ k, k ≤ N - 2 →
        (if h : k < N then ha ⟨k, h⟩ else 0) - ha ⟨0, by omega⟩ =
          if k ≤ c0.val then 0 else -(n : ZMod p) := by
      apply l05nNA_prefix_eq (fun k => (if h : k < N then ha ⟨k, h⟩ else 0) - ha ⟨0, by omega⟩)
        (n : ZMod p) c0.val (N - 2)
      · have := c0.isLt; omega
      · rw [dif_pos (by omega : 0 < N)]; ring
      · intro k hklt
        rw [dif_pos (by omega : k < N), dif_pos (by omega : k + 1 < N)]
        have hc' := l05nNA_fin_ne k (by omega) b (by omega)
        have hcon := h ⟨k, by omega⟩ hc'
        rw [l05nNA_dot_alpha_short ha ⟨k, by omega⟩ (l05nNA_hc_lt (by omega) (by omega)),
          sub_eq_iff_eq_add] at hcon
        rw [hcon, l05nNA_fin_if_eq k (by omega) c0]
        ring
    funext j
    show ha j = (((ggDepANHaParam p N b.val c0.val n (ha ⟨0, by omega⟩ - (n : ZMod p)).val
      (ha ⟨N - 1, by omega⟩).val).getD j.val 0 : ℕ) : ZMod p)
    rw [l05nNA_getD_paramHa j.val j.isLt, if_neg (by omega : ¬ (b.val = 0))]
    by_cases hj1 : j.val + 1 = N
    · rw [if_pos hj1, l05nNA_fin_eq_last j hj1, ZMod.natCast_mod]
      exact (ZMod.natCast_zmod_val (ha ⟨N - 1, by omega⟩)).symm
    · rw [if_neg hj1]
      have hcoord : ha j = (ha ⟨0, by omega⟩ - (n : ZMod p)) +
          (if j.val ≤ c0.val then (n : ZMod p) else 0) := by
        have hk := hpref j.val (by omega)
        rw [dif_pos (by omega : j.val < N), sub_eq_iff_eq_add] at hk
        have hk' : ha j = (if j.val ≤ c0.val then 0 else -(n : ZMod p)) + ha ⟨0, by omega⟩ := by
          simpa using hk
        rw [hk']
        by_cases hh : j.val ≤ c0.val
        · simp only [if_pos hh]; ring
        · simp only [if_neg hh]; ring
      have hcast : ((if j.val ≤ c0.val then n else 0 : ℕ) : ZMod p) =
          (if j.val ≤ c0.val then (n : ZMod p) else 0) := by
        by_cases hh : j.val ≤ c0.val <;> simp [hh]
      rw [ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_zmod_val, hcast]
      exact hcoord

theorem ggDepANAa_complete {p N : ℕ} [Fact p.Prime] (hpN : p ∣ N) (hN : 5 ≤ N)
    (b c0 : Fin (N - 1)) (hb : b.val = 0 ∨ b.val + 2 = N) (hbc : c0 ≠ b) (m : ℕ)
    (aa : GGDepAE p N)
    (h : ∀ c : Fin (N - 1), c ≠ b →
      ggDepAdot aa (ggDepAh p N c) = if c = c0 then (m : ZMod p) else 0) :
    ∃ u v : ℕ, aa = ggDepANToZ p N (ggDepANAaParam p N b.val c0.val m u v) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hpN' : (N : ZMod p) = 0 := by
    obtain ⟨k, hk⟩ := hpN
    rw [hk, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have hNm1 : ((N - 1 : ℕ) : ZMod p) = -1 := by
    have h1 : ((N - 1 : ℕ) : ZMod p) + 1 = 0 := by
      have h2 : ((N - 1 : ℕ) : ZMod p) + 1 = ((N - 1 + 1 : ℕ) : ZMod p) := by
        push_cast; ring
      rw [h2, Nat.sub_add_cancel (by omega : 1 ≤ N), hpN']
    exact eq_neg_of_add_eq_zero_left h1
  have hNm2 : ((N - 2 : ℕ) : ZMod p) = -2 := by
    have hsub : ((N - 2 : ℕ) : ZMod p) = ((N - 1 : ℕ) : ZMod p) - 1 := by
      have h2 : ((N - 2 : ℕ) : ZMod p) + 1 = ((N - 1 : ℕ) : ZMod p) := by
        have h3 : ((N - 2 : ℕ) : ZMod p) + 1 = ((N - 2 + 1 : ℕ) : ZMod p) := by
          push_cast; ring
        rw [h3, show N - 2 + 1 = N - 1 by omega]
      exact eq_sub_of_add_eq h2
    rw [hsub, hNm1]; ring
  rcases hb with hb0 | hbN
  · by_cases hc0N : c0.val + 2 = N
    · refine ⟨(aa ⟨N-2, by omega⟩).val, (aa ⟨N-1, by omega⟩).val, ?_⟩
      have hconst : ∀ k, 1 ≤ k → k ≤ N - 2 →
          (if h : k < N then aa ⟨k, h⟩ else 0) = (aa ⟨N-2, by omega⟩ : ZMod p) := by
        have hf := l05nNA_tail_eq (fun k =>
            (if h : k < N then aa ⟨k, h⟩ else 0) - aa ⟨N-2, by omega⟩)
          (0 : ZMod p) c0.val (N - 2)
          (by have := c0.isLt; omega)
          (by rw [dif_pos (by omega : N-2 < N)]; split_ifs <;> ring)
          (by
            intro k hk1 hklt
            rw [dif_pos (by omega : k < N), dif_pos (by omega : k + 1 < N)]
            have hc' := l05nNA_fin_ne k (by omega) b (by omega)
            have hcon := h ⟨k, by omega⟩ hc'
            rw [l05nNA_dot_h_short aa ⟨k, by omega⟩ (l05nNA_hc_lt (by omega) (by omega)),
              l05nNA_fin_if_eq k (by omega) c0, if_neg (by omega : ¬ (k = c0.val)),
              sub_eq_zero] at hcon
            rw [if_neg (by omega : ¬ (k = c0.val)), hcon]
            ring)
        intro k hk1 hk2
        have hk := hf k hk1 hk2
        rw [dif_pos (by omega : k < N)] at hk
        have hk0 : (if k ≤ c0.val then (0 : ZMod p) else 0) = 0 := by split_ifs <;> rfl
        rw [hk0, sub_eq_zero] at hk
        rw [dif_pos (by omega : k < N)]
        exact hk
      have hlast : (∑ j : Fin (N-1), aa ⟨j.val, by omega⟩) + aa ⟨N-2, by omega⟩ = (m : ZMod p) := by
        have hc' := l05nNA_fin_ne (N-2) (by omega) b (by omega)
        have hcon := h ⟨N-2, by omega⟩ hc'
        rw [l05nNA_dot_h_last (by omega : 1 ≤ N) aa ⟨N-2, by omega⟩
            (l05nNA_hc_eq (by omega) (by omega))] at hcon
        have hif : (⟨N-2, by omega⟩ : Fin (N-1)) = c0 :=
          l05nNA_fin_eq_of_val' (N-2) (by omega) c0 (by omega)
        rwa [if_pos hif] at hcon
      have hsum : (∑ j : Fin (N-1), aa ⟨j.val, by omega⟩) =
          (N - 2) • (aa ⟨N-2, by omega⟩ : ZMod p) + aa ⟨0, by omega⟩ := by
        rw [l05nNA_sum_fin_pred (by omega : 2 ≤ N) (fun j : Fin (N-1) => aa ⟨j.val, by omega⟩)]
        have h1 : (∑ i : Fin (N-2), aa ⟨i.val+1, by omega⟩) =
            (N - 2) • (aa ⟨N-2, by omega⟩ : ZMod p) := by
          trans ∑ i : Fin (N-2), (aa ⟨N-2, by omega⟩ : ZMod p)
          · apply Finset.sum_congr rfl
            intro i _
            have := hconst (i.val+1) (by omega) (by omega)
            rwa [dif_pos (by omega : i.val+1 < N)] at this
          · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        rw [h1]
      have haa0 : aa ⟨0, by omega⟩ = (aa ⟨N-2, by omega⟩ : ZMod p) + (m : ZMod p) := by
        rw [hsum, nsmul_eq_mul, hNm2] at hlast
        linear_combination hlast
      funext j
      show aa j = (((ggDepANAaParam p N b.val c0.val m (aa ⟨N-2, by omega⟩).val
        (aa ⟨N-1, by omega⟩).val).getD j.val 0 : ℕ) : ZMod p)
      simp only [l05nNA_getD_paramAa j.val j.isLt, if_pos hb0, if_pos hc0N]
      by_cases hj1 : j.val + 1 = N
      · rw [if_pos hj1, l05nNA_fin_eq_last j hj1, ZMod.natCast_mod]
        exact (ZMod.natCast_zmod_val (aa ⟨N-1, by omega⟩)).symm
      · rw [if_neg hj1]
        by_cases hj0 : j.val = 0
        · rw [if_pos hj0, l05nNA_fin_eq_of_val j 0 (by omega) (by omega)]
          rw [ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_zmod_val, haa0]
          ring
        · rw [if_neg hj0, ZMod.natCast_mod, ZMod.natCast_zmod_val]
          have := hconst j.val (by omega) (by omega)
          rw [dif_pos (by omega : j.val < N)] at this
          simpa using this
    · refine ⟨(aa ⟨1, by omega⟩ - (m : ZMod p)).val, (aa ⟨N-1, by omega⟩).val, ?_⟩
      have hg : ∀ k, k ≤ N - 3 →
          (if h : k + 1 < N then aa ⟨k+1, h⟩ else 0) - aa ⟨1, by omega⟩ =
            if k ≤ c0.val - 1 then 0 else -(m : ZMod p) := by
        apply l05nNA_prefix_eq (fun k =>
            (if h : k+1 < N then aa ⟨k+1, h⟩ else 0) - aa ⟨1, by omega⟩)
          (m : ZMod p) (c0.val - 1) (N - 3)
        · have := c0.isLt; omega
        · rw [dif_pos (by omega : 0 + 1 < N)]; ring
        · intro k hklt
          rw [dif_pos (by omega : k + 1 < N), dif_pos (by omega : k + 2 < N)]
          have hc' := l05nNA_fin_ne (k+1) (by omega) b (by omega)
          have hcon := h ⟨k+1, by omega⟩ hc'
          rw [l05nNA_dot_h_short aa ⟨k+1, by omega⟩ (l05nNA_hc_lt (by omega) (by omega)),
            sub_eq_iff_eq_add] at hcon
          rw [l05nNA_fin_if_eq (k+1) (by omega) c0] at hcon
          have hif2 : (if k + 1 = c0.val then (m : ZMod p) else 0) =
              if k = c0.val - 1 then (m : ZMod p) else 0 := by
            by_cases hh : k = c0.val - 1
            · rw [if_pos (by omega), if_pos hh]
            · rw [if_neg (by omega), if_neg hh]
          rw [hif2] at hcon
          have hb : aa ⟨k+2, by omega⟩ = aa ⟨k+1, by omega⟩ -
              (if k = c0.val - 1 then (m : ZMod p) else 0) := by rw [hcon]; ring
          rw [hb]; ring
      have hcoord : ∀ k, 1 ≤ k → k ≤ N - 2 →
          (if h : k < N then aa ⟨k, h⟩ else 0) = (aa ⟨1, by omega⟩ - (m : ZMod p)) +
            (if k ≤ c0.val then (m : ZMod p) else 0) := by
        intro k hk1 hk2
        have hk := hg (k - 1) (by omega)
        rw [Nat.sub_add_cancel hk1, dif_pos (by omega : k < N)] at hk
        have hcond : (if k - 1 ≤ c0.val - 1 then (0 : ZMod p) else -(m : ZMod p)) =
            (if k ≤ c0.val then 0 else -(m : ZMod p)) := by
          by_cases hh : k ≤ c0.val
          · rw [if_pos hh, if_pos (by omega)]
          · rw [if_neg hh, if_neg (by omega)]
        rw [hcond, sub_eq_iff_eq_add] at hk
        rw [dif_pos (by omega : k < N)]
        rw [hk]
        by_cases hh : k ≤ c0.val
        · simp only [if_pos hh]; ring
        · simp only [if_neg hh]; ring
      have hlast : (∑ j : Fin (N-1), aa ⟨j.val, by omega⟩) + aa ⟨N-2, by omega⟩ = 0 := by
        have hc' := l05nNA_fin_ne (N-2) (by omega) b (by omega)
        have hcon := h ⟨N-2, by omega⟩ hc'
        rw [l05nNA_dot_h_last (by omega : 1 ≤ N) aa ⟨N-2, by omega⟩
            (l05nNA_hc_eq (by omega) (by omega))] at hcon
        have hne : ¬ ((⟨N-2, by omega⟩ : Fin (N-1)) = c0) := by
          intro hh
          have h1 : N - 2 = c0.val := by simpa [Fin.val_mk] using congrArg Fin.val hh
          omega
        rwa [if_neg hne] at hcon
      have hN2 : aa ⟨N-2, by omega⟩ = (aa ⟨1, by omega⟩ - (m : ZMod p)) := by
        have hk := hcoord (N - 2) (by omega) (by omega)
        rw [dif_pos (by omega : N - 2 < N), if_neg (by omega : ¬ (N - 2 ≤ c0.val))] at hk
        rw [hk]; ring
      have hsum : (∑ j : Fin (N-1), aa ⟨j.val, by omega⟩) =
          (N - 2) • (aa ⟨1, by omega⟩ - (m : ZMod p)) +
            (c0.val : ZMod p) * (m : ZMod p) + aa ⟨0, by omega⟩ := by
        rw [l05nNA_sum_fin_pred (by omega : 2 ≤ N) (fun j : Fin (N-1) => aa ⟨j.val, by omega⟩)]
        have h1 : (∑ i : Fin (N-2), aa ⟨i.val+1, by omega⟩) =
            (N - 2) • (aa ⟨1, by omega⟩ - (m : ZMod p)) + (c0.val : ZMod p) * (m : ZMod p) := by
          trans ∑ i : Fin (N-2), ((aa ⟨1, by omega⟩ - (m : ZMod p)) +
              (if i.val < c0.val then (m : ZMod p) else 0))
          · apply Finset.sum_congr rfl
            intro i _
            have := hcoord (i.val+1) (by omega) (by omega)
            rw [dif_pos (by omega : i.val+1 < N)] at this
            rw [this]
            by_cases hh : i.val < c0.val
            · simp only [if_pos (by omega : i.val+1 ≤ c0.val), if_pos hh]
            · simp only [if_neg (by omega : ¬ (i.val+1 ≤ c0.val)), if_neg hh]
          · rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              l05nNA_sum_fin_lt (m : ZMod p) (by omega : c0.val ≤ N-2)]
        rw [h1]
      have haa0 : aa ⟨0, by omega⟩ = (aa ⟨1, by omega⟩ - (m : ZMod p)) -
          (c0.val : ZMod p) * (m : ZMod p) := by
        rw [hsum, nsmul_eq_mul, hNm2, hN2] at hlast
        linear_combination hlast
      funext j
      show aa j = (((ggDepANAaParam p N b.val c0.val m (aa ⟨1, by omega⟩ - (m : ZMod p)).val
        (aa ⟨N-1, by omega⟩).val).getD j.val 0 : ℕ) : ZMod p)
      simp only [l05nNA_getD_paramAa j.val j.isLt, if_pos hb0, if_neg hc0N]
      by_cases hj1 : j.val + 1 = N
      · rw [if_pos hj1, l05nNA_fin_eq_last j hj1, ZMod.natCast_mod]
        exact (ZMod.natCast_zmod_val (aa ⟨N-1, by omega⟩)).symm
      · rw [if_neg hj1]
        by_cases hj0 : j.val = 0
        · rw [if_pos hj0, l05nNA_fin_eq_of_val j 0 (by omega) (by omega)]
          rw [ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_zmod_val, haa0,
            l05nNA_natCast_psub (le_of_lt (Nat.mod_lt _ (Fact.out : p.Prime).pos)),
                ZMod.natCast_mod,
            Nat.cast_mul]
          ring
        · rw [if_neg hj0]
          have hk := hcoord j.val (by omega) (by omega)
          rw [dif_pos (by omega : j.val < N)] at hk
          by_cases hh : j.val ≤ c0.val
          · rw [if_pos hh] at hk
            rw [if_pos hh, ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_zmod_val, hk]
            try ring
          · rw [if_neg hh] at hk
            rw [if_neg hh, ZMod.natCast_mod, ZMod.natCast_zmod_val, hk]
            try ring
  · refine ⟨(aa ⟨0, by omega⟩ - (m : ZMod p)).val, (aa ⟨N-1, by omega⟩).val, ?_⟩
    have hpref : ∀ k, k ≤ N - 2 →
        (if h : k < N then aa ⟨k, h⟩ else 0) - aa ⟨0, by omega⟩ =
          if k ≤ c0.val then 0 else -(m : ZMod p) := by
      apply l05nNA_prefix_eq (fun k => (if h : k < N then aa ⟨k, h⟩ else 0) - aa ⟨0, by omega⟩)
        (m : ZMod p) c0.val (N - 2)
      · have := c0.isLt; omega
      · rw [dif_pos (by omega : 0 < N)]; ring
      · intro k hklt
        rw [dif_pos (by omega : k < N), dif_pos (by omega : k + 1 < N)]
        have hc' := l05nNA_fin_ne k (by omega) b (by omega)
        have hcon := h ⟨k, by omega⟩ hc'
        rw [l05nNA_dot_h_short aa ⟨k, by omega⟩ (l05nNA_hc_lt (by omega) (by omega)),
          sub_eq_iff_eq_add] at hcon
        rw [hcon, l05nNA_fin_if_eq k (by omega) c0]
        ring
    funext j
    show aa j = (((ggDepANAaParam p N b.val c0.val m (aa ⟨0, by omega⟩ - (m : ZMod p)).val
      (aa ⟨N-1, by omega⟩).val).getD j.val 0 : ℕ) : ZMod p)
    simp only [l05nNA_getD_paramAa j.val j.isLt, if_neg (by omega : ¬ (b.val = 0))]
    by_cases hj1 : j.val + 1 = N
    · rw [if_pos hj1, l05nNA_fin_eq_last j hj1, ZMod.natCast_mod]
      exact (ZMod.natCast_zmod_val (aa ⟨N-1, by omega⟩)).symm
    · rw [if_neg hj1]
      have hcoord : aa j = (aa ⟨0, by omega⟩ - (m : ZMod p)) +
          (if j.val ≤ c0.val then (m : ZMod p) else 0) := by
        have hk := hpref j.val (by omega)
        rw [dif_pos (by omega : j.val < N), sub_eq_iff_eq_add] at hk
        have hk' : aa j = (if j.val ≤ c0.val then 0 else -(m : ZMod p)) + aa ⟨0, by omega⟩ := by
          simpa using hk
        rw [hk']
        by_cases hh : j.val ≤ c0.val
        · simp only [if_pos hh]; ring
        · simp only [if_neg hh]; ring
      have hcast : ((if j.val ≤ c0.val then m else 0 : ℕ) : ZMod p) =
          (if j.val ≤ c0.val then (m : ZMod p) else 0) := by
        by_cases hh : j.val ≤ c0.val <;> simp [hh]
      rw [ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_zmod_val, hcast]
      exact hcoord

private lemma l05nNB_sum_zipWith_fin {p : ℕ} :
    ∀ (a b : List ℕ), a.length = b.length →
      ((List.zipWith (fun x y => ((x * y : ℕ) : ZMod p)) a b).sum) =
        ∑ j : Fin a.length,
          ((a.getD j.val 0 : ℕ) : ZMod p) * ((b.getD j.val 0 : ℕ) : ZMod p) := by
  intro a
  induction a with
  | nil =>
      intro b h
      have hb : b = [] := List.length_eq_zero_iff.mp h.symm
      subst hb
      simp
  | cons x as ih =>
      intro b h
      cases b with
      | nil => simp at h
      | cons y bs =>
          have h' : as.length = bs.length := Nat.succ.inj h
          rw [List.zipWith, List.sum_cons, ih bs h', List.length_cons,
            Fin.sum_univ_succ (n := as.length)]
          simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ]
          rw [Nat.cast_mul]

theorem ggDepANDot_cast {p N : ℕ} [Fact p.Prime] (a b : List ℕ) (ha : a.length = N)
    (hb : b.length = N) :
    ((ggDepANDot p a b : ℕ) : ZMod p) = ggDepAdot (ggDepANToZ p N a) (ggDepANToZ p N b) := by
  subst N
  have hlen : a.length = b.length := hb.symm
  unfold ggDepANDot ggDepAdot ggDepANToZ
  rw [ZMod.natCast_mod, Nat.cast_list_sum, List.map_zipWith, l05nNB_sum_zipWith_fin a b hlen]

private lemma l05nNB_form_apply {p N : ℕ} (f v : GGDepAE p N) :
    ggDepAform f v = ggDepAdot f v := by
  simp [ggDepAform, ggDepAdot]

private lemma l05nNB_refl_apply {p N : ℕ} (c f v : GGDepAE p N) :
    ggDepARefl c f v = v - ggDepAdot f v • c := by
  simp [ggDepARefl, l05nNB_form_apply]

private lemma l05nNB_dot_sub {p N : ℕ} (a v w : GGDepAE p N) :
    ggDepAdot a (v - w) = ggDepAdot a v - ggDepAdot a w := by
  rw [← l05nNB_form_apply a (v - w), map_sub, l05nNB_form_apply a v, l05nNB_form_apply a w]

private lemma l05nNB_dot_add {p N : ℕ} (a v w : GGDepAE p N) :
    ggDepAdot a (v + w) = ggDepAdot a v + ggDepAdot a w := by
  rw [← l05nNB_form_apply a (v + w), map_add, l05nNB_form_apply a v, l05nNB_form_apply a w]

private lemma l05nNB_dot_smul {p N : ℕ} (a : GGDepAE p N) (k : ZMod p) (v : GGDepAE p N) :
    ggDepAdot a (k • v) = k * ggDepAdot a v := by
  rw [← l05nNB_form_apply a (k • v), map_smul, l05nNB_form_apply a v]
  simp

private lemma l05nNB_dot_sub_left {p N : ℕ} (a b v : GGDepAE p N) :
    ggDepAdot (a - b) v = ggDepAdot a v - ggDepAdot b v := by
  simp only [ggDepAdot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma l05nNB_dot_smul_left {p N : ℕ} (k : ZMod p) (a v : GGDepAE p N) :
    ggDepAdot (k • a) v = k * ggDepAdot a v := by
  simp only [ggDepAdot, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [← Finset.mul_sum]

private lemma l05nNB_form_ne_zero {p N : ℕ} (f : GGDepAE p N) (hf : f ≠ 0) :
    ggDepAform f ≠ 0 := by
  intro h
  apply hf
  ext j
  have h1 := congrArg (fun g : GGDepAE p N →ₗ[ZMod p] ZMod p => g (Pi.single j 1)) h
  rw [l05nNB_form_apply] at h1
  have h2 : ggDepAdot f (Pi.single j 1) = f j := by
    rw [ggDepAdot, Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [h2] at h1
  simpa using h1

private lemma l05nNB_range_smulRight {p N : ℕ} [Fact p.Prime] (d f : GGDepAE p N)
    (hf : ggDepAform f ≠ 0) :
    LinearMap.range ((ggDepAform f).smulRight d) = Submodule.span (ZMod p) {d} := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    have hex : ∃ v, ggDepAform f v ≠ 0 := by
      by_contra hcon
      exact hf (LinearMap.ext fun v => not_not.mp (not_exists.mp hcon v))
    obtain ⟨v, hv⟩ := hex
    refine ⟨(ggDepAform f v)⁻¹ • v, ?_⟩
    rw [LinearMap.smulRight_apply, map_smul, smul_eq_mul, inv_mul_cancel₀ hv, one_smul]

private lemma l05nNB_isTv_one_add {p N : ℕ} [Fact p.Prime] (d f : GGDepAE p N)
    (hfd : ggDepAdot f d = 0) (hd : d ≠ 0) (hf : f ≠ 0) :
    GGDepAIsTv (1 + (ggDepAform f).smulRight d) := by
  constructor
  · have hsub : (1 + (ggDepAform f).smulRight d) - LinearMap.id =
        (ggDepAform f).smulRight d := by
      ext v; simp
    rw [hsub, l05nNB_range_smulRight d f (l05nNB_form_ne_zero f hf)]
    exact finrank_span_singleton hd
  · intro w
    have hg : ∀ x, (1 + (ggDepAform f).smulRight d) x = x + ggDepAdot f x • d := by
      intro x; simp [l05nNB_form_apply]
    rw [hg, hg]
    simp only [l05nNB_dot_add, l05nNB_dot_sub, l05nNB_dot_smul, hfd, mul_zero, zero_smul,
      add_zero, add_sub_cancel_left]

private lemma l05nNB_refl_mul_same {p N : ℕ} (c f1 f2 : GGDepAE p N)
    (h1 : ggDepAdot f1 c = 2) (h2 : ggDepAdot f2 c = 2) :
    ggDepARefl c f1 * ggDepARefl c f2 =
      1 + (ggDepAform (f2 - f1)).smulRight c := by
  apply LinearMap.ext; intro v
  ext j
  have hone : (1 : Module.End (ZMod p) (GGDepAE p N)) v = v := rfl
  simp only [Module.End.mul_apply, l05nNB_refl_apply, LinearMap.add_apply,
    LinearMap.smulRight_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    l05nNB_dot_sub, l05nNB_dot_smul, l05nNB_dot_sub_left, l05nNB_form_apply, h1, h2]
  rw [hone]
  ring

private lemma l05nNB_refl_mul_prop {p N : ℕ} [Fact p.Prime] (c1 c2 f1 f2 : GGDepAE p N)
    (k : ZMod p) (h1 : ggDepAdot f1 c1 = 2) (hf : f2 = k • f1) (hk0 : k ≠ 0)
    (hk : ggDepAdot f1 c2 = k⁻¹ * 2) :
    ggDepARefl c1 f1 * ggDepARefl c2 f2 =
      1 + (ggDepAform f1).smulRight (c1 - k • c2) := by
  subst hf
  apply LinearMap.ext; intro v
  ext j
  have hone : (1 : Module.End (ZMod p) (GGDepAE p N)) v = v := rfl
  simp only [Module.End.mul_apply, l05nNB_refl_apply, LinearMap.add_apply,
    LinearMap.smulRight_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    l05nNB_dot_sub, l05nNB_dot_smul, l05nNB_dot_smul_left, l05nNB_dot_sub_left,
    l05nNB_form_apply, h1]
  rw [hone, hk]
  field_simp
  ring

private lemma l05nNB_refl_smul_center {p N : ℕ} (c f : GGDepAE p N) (lam : ZMod p) :
    ggDepARefl (lam • c) f = ggDepARefl c (lam • f) := by
  apply LinearMap.ext; intro v
  rw [l05nNB_refl_apply, l05nNB_refl_apply, l05nNB_dot_smul_left]
  congr 1
  rw [smul_smul, mul_comm]

private lemma l05nNB_two_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  have hp2' : p = 2 := by
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    omega
  exact hp2 hp2'

private lemma l05nNB_natCast_mod_ne_zero {p x : ℕ} (hx : x % p ≠ 0) : (x : ZMod p) ≠ 0 := by
  intro h0
  exact hx (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff x p).mp h0))

private lemma l05nNB_natCast_eq_of_mod_eq {p x y : ℕ} (h : x % p = y % p) :
    (x : ZMod p) = (y : ZMod p) :=
  (ZMod.natCast_eq_natCast_iff' x y p).mpr h

private lemma l05nNB_firstNZ_spec {p : ℕ} {l : List ℕ} {i : ℕ}
    (h : ggDepANFirstNZ p l = some i) :
    i < l.length ∧ (l.getD i 0 % p != 0) = true := by
  rw [ggDepANFirstNZ] at h
  refine ⟨List.mem_range.mp (List.mem_of_find?_eq_some
    (p := fun j => l.getD j 0 % p != 0) (a := i) h), ?_⟩
  exact List.find?_some (p := fun j => l.getD j 0 % p != 0) (a := i) h

private lemma l05nNB_par_smul {p N : ℕ} [Fact p.Prime] (a b : List ℕ) (ha : a.length = N)
    (hb : b.length = N) (i : ℕ) (hfirst : ggDepANFirstNZ p a = some i)
    (hpar : ggDepANPar p a b = true) :
    ∃ lam : ZMod p, lam ≠ 0 ∧ ggDepANToZ p N b = lam • ggDepANToZ p N a := by
  have hi_pred : (a.getD i 0 % p != 0) = true := (l05nNB_firstNZ_spec hfirst).2
  have hai_mod : a.getD i 0 % p ≠ 0 := bne_iff_ne.mp hi_pred
  have hai : (a.getD i 0 : ZMod p) ≠ 0 := l05nNB_natCast_mod_ne_zero hai_mod
  rw [ggDepANPar, hfirst, Bool.and_eq_true] at hpar
  obtain ⟨hbi_pred, hall⟩ := hpar
  have hbi_mod : b.getD i 0 % p ≠ 0 := bne_iff_ne.mp hbi_pred
  have hbi : (b.getD i 0 : ZMod p) ≠ 0 := l05nNB_natCast_mod_ne_zero hbi_mod
  refine ⟨(b.getD i 0 : ZMod p) * (a.getD i 0 : ZMod p)⁻¹, mul_ne_zero hbi (inv_ne_zero hai), ?_⟩
  funext j
  simp only [ggDepANToZ, Pi.smul_apply, smul_eq_mul]
  have hj : j.val < a.length := by rw [ha]; exact j.isLt
  have hcross := (List.all_eq_true.mp hall) j.val (List.mem_range.mpr hj)
  have heq : (a.getD i 0 : ZMod p) * (b.getD j.val 0 : ZMod p)
      = (b.getD i 0 : ZMod p) * (a.getD j.val 0 : ZMod p) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul,
      l05nNB_natCast_eq_of_mod_eq (beq_iff_eq.mp hcross)]
  calc ((b.getD j.val 0 : ℕ) : ZMod p)
      = (a.getD i 0 : ZMod p)⁻¹ * ((a.getD i 0 : ZMod p) * (b.getD j.val 0 : ZMod p)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hai, one_mul]
    _ = (a.getD i 0 : ZMod p)⁻¹ * ((b.getD i 0 : ZMod p) * (a.getD j.val 0 : ZMod p)) := by
        rw [heq]
    _ = ((b.getD i 0 : ZMod p) * (a.getD i 0 : ZMod p)⁻¹) *
          ((a.getD j.val 0 : ℕ) : ZMod p) := by
        ring

private lemma l05nNB_eqScaled_false {p N : ℕ} (k₁ k₂ : ℕ) (u v : List ℕ)
    (hu : u.length = N) (hv : v.length = N) (lam : ZMod p)
    (hk₂ : (k₂ : ZMod p) = lam * (k₁ : ZMod p)) (hk₁ : (k₁ : ZMod p) ≠ 0)
    (ht : (!ggDepANEqScaled p k₁ u k₂ v) = true) :
    ggDepANToZ p N u ≠ lam • ggDepANToZ p N v := by
  have hfalse : (List.zipWith (fun x y => (k₁ * x) % p == (k₂ * y) % p) u v).all id = false := by
    simpa [ggDepANEqScaled] using ht
  rw [List.all_eq_false] at hfalse
  obtain ⟨z, hzmem, hznot⟩ := hfalse
  have hz : z = false := by simpa using hznot
  obtain ⟨k, hk, hzk⟩ := List.mem_iff_getElem.mp hzmem
  have hkmin : k < min u.length v.length := by rw [List.length_zipWith] at hk; exact hk
  have hku : k < u.length := lt_of_lt_of_le hkmin (Nat.min_le_left _ _)
  have hkv : k < v.length := lt_of_lt_of_le hkmin (Nat.min_le_right _ _)
  have hkN : k < N := by
    have hmin : min u.length v.length = min N N := by rw [hu, hv]
    rw [hmin] at hkmin
    simpa using hkmin
  have hzip := List.getElem_zipWith (f := fun x y => (k₁ * x) % p == (k₂ * y) % p)
    (l := u) (l' := v) (i := k) (h := hk)
  have hz0 : (List.zipWith (fun x y => (k₁ * x) % p == (k₂ * y) % p) u v)[k] = false := by
    rw [hzk, hz]
  have hbeq : ((k₁ * u[k]) % p == (k₂ * v[k]) % p) = false := by
    rw [← hzip]; exact hz0
  have hne : (k₁ * u[k]) % p ≠ (k₂ * v[k]) % p := beq_eq_false_iff_ne.mp hbeq
  have hne' : (k₁ * u.getD k 0) % p ≠ (k₂ * v.getD k 0) % p := by
    rw [List.getD_eq_getElem u 0 hku, List.getD_eq_getElem v 0 hkv]
    exact hne
  intro hvec
  have hcoord := congrFun hvec ⟨k, hkN⟩
  simp only [ggDepANToZ, Pi.smul_apply, smul_eq_mul] at hcoord
  apply hne'
  apply (ZMod.natCast_eq_natCast_iff' (k₁ * u.getD k 0) (k₂ * v.getD k 0) p).mp
  rw [Nat.cast_mul, Nat.cast_mul]
  calc (k₁ : ZMod p) * (u.getD k 0 : ZMod p)
      = (k₁ : ZMod p) * (lam * (v.getD k 0 : ZMod p)) := by rw [hcoord]
    _ = (k₂ : ZMod p) * (v.getD k 0 : ZMod p) := by rw [hk₂]; ring

theorem ggDepANTestPair_sound {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (q1 q2 : GGDepANPair)
    (h11 : q1.1.length = N) (h12 : q1.2.length = N) (h21 : q2.1.length = N)
    (h22 : q2.2.length = N) (hd1 : ggDepANDot p q1.2 q1.1 = 2 % p)
    (hd2 : ggDepANDot p q2.2 q2.1 = 2 % p) (ht : ggDepANTestPair p q1 q2 = true) :
    ggDepAdot (ggDepANToZ p N q1.1, ggDepANToZ p N q1.2).2 (ggDepANToZ p N q1.1, ggDepANToZ p N q1.2).1 = 2 ∧ ggDepAdot (ggDepANToZ p N q2.1, ggDepANToZ p N q2.2).2 (ggDepANToZ p N q2.1, ggDepANToZ p N q2.2).1 = 2 ∧
      GGDepAIsTv (ggDepARefl (ggDepANToZ p N q1.1, ggDepANToZ p N q1.2).1 (ggDepANToZ p N q1.1, ggDepANToZ p N q1.2).2 * ggDepARefl (ggDepANToZ p N q2.1, ggDepANToZ p N q2.2).1 (ggDepANToZ p N q2.1, ggDepANToZ p N q2.2).2) := by
  have h1 : ggDepAdot (ggDepANToZ p N q1.2) (ggDepANToZ p N q1.1) = 2 := by
    rw [← ggDepANDot_cast (p := p) q1.2 q1.1 h12 h11, hd1, ZMod.natCast_mod]
    rfl
  have h2 : ggDepAdot (ggDepANToZ p N q2.2) (ggDepANToZ p N q2.1) = 2 := by
    rw [← ggDepANDot_cast (p := p) q2.2 q2.1 h22 h21, hd2, ZMod.natCast_mod]
    rfl
  refine ⟨h1, h2, ?_⟩
  rw [ggDepANTestPair, Bool.or_eq_true] at ht
  rcases ht with hA | hB
  · cases hf1 : ggDepANFirstNZ p q1.1 with
    | none => rw [hf1] at hA; simp at hA
    | some i =>
        rw [hf1, Bool.and_eq_true] at hA
        obtain ⟨hpar, hneqScaled⟩ := hA
        obtain ⟨lam, hlam0, hc2eq⟩ := l05nNB_par_smul q1.1 q2.1 h11 h21 i hf1 hpar
        have hiN : i < N := h11 ▸ (l05nNB_firstNZ_spec hf1).1
        have hbi : ((q2.1.getD i 0 : ℕ) : ZMod p) = lam * ((q1.1.getD i 0 : ℕ) : ZMod p) := by
          have := congrFun hc2eq ⟨i, hiN⟩
          simpa [ggDepANToZ, Pi.smul_apply, smul_eq_mul] using this
        have hki : ((q1.1.getD i 0 : ℕ) : ZMod p) ≠ 0 :=
          l05nNB_natCast_mod_ne_zero (bne_iff_ne.mp (l05nNB_firstNZ_spec hf1).2)
        have hneqvec : ggDepANToZ p N q1.2 ≠ lam • ggDepANToZ p N q2.2 :=
          l05nNB_eqScaled_false (q1.1.getD i 0) (q2.1.getD i 0) q1.2 q2.2 h12 h22 lam hbi hki
            hneqScaled
        have h2prime : ggDepAdot (lam • ggDepANToZ p N q2.2) (ggDepANToZ p N q1.1) = 2 := by
          rw [l05nNB_dot_smul_left, ← l05nNB_dot_smul, ← hc2eq, h2]
        rw [hc2eq, l05nNB_refl_smul_center,
          l05nNB_refl_mul_same (p := p) (N := N) (ggDepANToZ p N q1.1) (ggDepANToZ p N q1.2)
            (lam • ggDepANToZ p N q2.2) h1 h2prime]
        refine l05nNB_isTv_one_add _ _ ?_ ?_ ?_
        · rw [l05nNB_dot_sub_left, h2prime, h1, sub_self]
        · intro hc1
          have hzero : (2 : ZMod p) = 0 := by
            rw [← h1, hc1]
            simp [ggDepAdot]
          exact l05nNB_two_ne_zero hp2 hzero
        · intro hzero
          exact hneqvec (sub_eq_zero.mp hzero).symm
  · cases hf2 : ggDepANFirstNZ p q1.2 with
    | none => rw [hf2] at hB; simp at hB
    | some j =>
        rw [hf2, Bool.and_eq_true] at hB
        obtain ⟨hpar, hneqScaled⟩ := hB
        obtain ⟨mu, hmu0, hf2eq⟩ := l05nNB_par_smul q1.2 q2.2 h12 h22 j hf2 hpar
        have hjN : j < N := h12 ▸ (l05nNB_firstNZ_spec hf2).1
        have hmu_j : ((q2.2.getD j 0 : ℕ) : ZMod p) = mu * ((q1.2.getD j 0 : ℕ) : ZMod p) := by
          have := congrFun hf2eq ⟨j, hjN⟩
          simpa [ggDepANToZ, Pi.smul_apply, smul_eq_mul] using this
        have hfj : ((q1.2.getD j 0 : ℕ) : ZMod p) ≠ 0 :=
          l05nNB_natCast_mod_ne_zero (bne_iff_ne.mp (l05nNB_firstNZ_spec hf2).2)
        have hneqvec : ggDepANToZ p N q1.1 ≠ mu • ggDepANToZ p N q2.1 :=
          l05nNB_eqScaled_false (q1.2.getD j 0) (q2.2.getD j 0) q1.1 q2.1 h11 h21 mu hmu_j hfj
            hneqScaled
        have hfj_ne : ggDepANToZ p N q1.2 ≠ 0 := by
          intro hf0
          have hcoord := congrFun hf0 ⟨j, hjN⟩
          simp only [ggDepANToZ, Pi.zero_apply] at hcoord
          exact hfj hcoord
        have hc2' : ggDepAdot (ggDepANToZ p N q1.2) (ggDepANToZ p N q2.1) = mu⁻¹ * 2 := by
          have hmul : mu * ggDepAdot (ggDepANToZ p N q1.2) (ggDepANToZ p N q2.1) = 2 := by
            rw [← l05nNB_dot_smul_left, ← hf2eq]
            exact h2
          calc ggDepAdot (ggDepANToZ p N q1.2) (ggDepANToZ p N q2.1)
              = mu⁻¹ * (mu * ggDepAdot (ggDepANToZ p N q1.2) (ggDepANToZ p N q2.1)) := by
                rw [← mul_assoc, inv_mul_cancel₀ hmu0, one_mul]
            _ = mu⁻¹ * 2 := by rw [hmul]
        rw [l05nNB_refl_mul_prop (p := p) (N := N) (ggDepANToZ p N q1.1) (ggDepANToZ p N q2.1)
          (ggDepANToZ p N q1.2) (ggDepANToZ p N q2.2) mu h1 hf2eq hmu0 hc2']
        refine l05nNB_isTv_one_add _ _ ?_ ?_ hfj_ne
        · rw [l05nNB_dot_sub, l05nNB_dot_smul, h1, hc2', ← mul_assoc, mul_inv_cancel₀ hmu0,
            one_mul, sub_self]
        · exact sub_ne_zero.mpr hneqvec

private lemma l05nNC_cast_hterm (p : ℕ) [Fact p.Prime] (x y z : ℕ) (hy : y ≤ p) :
    (((x + z + (p - y)) % p : ℕ) : ZMod p) = (x : ZMod p) + (z : ZMod p) - (y : ZMod p) := by
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_add, Nat.cast_sub hy, ZMod.natCast_self]
  ring

private lemma l05nNC_cast_aterm (p : ℕ) [Fact p.Prime] (x y : ℕ) (hy : y ≤ p) :
    (((x + (p - y)) % p : ℕ) : ZMod p) = (x : ZMod p) - (y : ZMod p) := by
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub hy, ZMod.natCast_self]
  ring

private lemma l05nNC_cast_sub (p : ℕ) [Fact p.Prime] (x y : ℕ) :
    (((x + (p - y % p)) % p : ℕ) : ZMod p) = (x : ZMod p) - (y : ZMod p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (le_of_lt (Nat.mod_lt y hp)),
    ZMod.natCast_self, ZMod.natCast_mod]
  ring

private lemma l05nNC_cast_hterm' (p : ℕ) [Fact p.Prime] (c1 c2 c3 : Prop)
    [Decidable c1] [Decidable c2] [Decidable c3] :
    ((((if c1 then 1 else 0) + (if c3 then 1 else 0) + (p - (if c2 then 1 else 0))) % p : ℕ) :
        ZMod p)
      = (if c1 then (1 : ZMod p) else 0) - (if c2 then (1 : ZMod p) else 0) +
          (if c3 then (1 : ZMod p) else 0) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hx : (((if c1 then 1 else 0 : ℕ)) : ZMod p) = (if c1 then (1 : ZMod p) else 0) := by
    split <;> simp
  have hy : (((if c2 then 1 else 0 : ℕ)) : ZMod p) = (if c2 then (1 : ZMod p) else 0) := by
    split <;> simp
  have hz : (((if c3 then 1 else 0 : ℕ)) : ZMod p) = (if c3 then (1 : ZMod p) else 0) := by
    split <;> simp
  rw [l05nNC_cast_hterm p _ _ _ (by split <;> omega), hx, hy, hz]
  ring

private lemma l05nNC_cast_aterm' (p : ℕ) [Fact p.Prime] (c1 c2 : Prop)
    [Decidable c1] [Decidable c2] :
    ((((if c1 then 1 else 0) + (p - (if c2 then 1 else 0))) % p : ℕ) : ZMod p)
      = (if c1 then (1 : ZMod p) else 0) - (if c2 then (1 : ZMod p) else 0) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hx : (((if c1 then 1 else 0 : ℕ)) : ZMod p) = (if c1 then (1 : ZMod p) else 0) := by
    split <;> simp
  have hy : (((if c2 then 1 else 0 : ℕ)) : ZMod p) = (if c2 then (1 : ZMod p) else 0) := by
    split <;> simp
  rw [l05nNC_cast_aterm p _ _ (by split <;> omega), hx, hy]

lemma l05nNC_toZ_H {p N i : ℕ} [Fact p.Prime] (h : i + 1 < N) :
    ggDepANToZ p N (ggDepANH p N i) = ggDepAh p N ⟨i, by omega⟩ := by
  funext j
  have hj : j.val < N := j.isLt
  have hjlen : j.val < (ggDepANH p N i).length := by simp [ggDepANH, hj]
  simp only [ggDepANToZ]
  rw [List.getD_eq_getElem (l := ggDepANH p N i) (d := 0) (n := j.val) hjlen]
  simp only [ggDepANH]
  rw [List.getElem_map]
  simp only [List.range_eq_range', List.getElem_range'_1, Nat.zero_add]
  rw [ggDepAh]
  by_cases hjN : j.val + 1 = N
  · simp [hjN]
  · rw [if_neg hjN, if_neg hjN]
    exact l05nNC_cast_hterm' p (j.val = i) (j.val = i + 1) (i + 2 = N)

lemma l05nNC_toZ_A {p N i : ℕ} [Fact p.Prime] (h : i + 1 < N) :
    ggDepANToZ p N (ggDepANA p N i) = ggDepAα p N ⟨i, by omega⟩ := by
  funext j
  have hj : j.val < N := j.isLt
  have hjlen : j.val < (ggDepANA p N i).length := by simp [ggDepANA, hj]
  simp only [ggDepANToZ]
  rw [List.getD_eq_getElem (l := ggDepANA p N i) (d := 0) (n := j.val) hjlen]
  simp only [ggDepANA]
  rw [List.getElem_map]
  simp only [List.range_eq_range', List.getElem_range'_1, Nat.zero_add]
  rw [ggDepAα]
  by_cases hjN : j.val + 1 = N
  · simp [hjN]
  · rw [if_neg hjN, if_neg hjN]
    exact l05nNC_cast_aterm' p (j.val = i) (j.val = i + 1)

lemma l05nNC_pair_i {p N : ℕ} (i : Fin (N - 1)) :
    ggDepAdot (ggDepAα p N i) (ggDepAh p N i) = 2 := by
  rw [ggDepAdot]
  have hi1 : ¬ (i.val + 1 = N) := by have := i.isLt; omega
  have hii : ¬ (i.val = i.val + 1) := by omega
  let iN : Fin N := ⟨i.val, by have := i.isLt; omega⟩
  let i1N : Fin N := ⟨i.val + 1, by have := i.isLt; omega⟩
  have hne : iN ≠ i1N := by
    intro h; have := congrArg Fin.val h; simp only [iN, i1N] at this; omega
  have hsupp : ∀ j : Fin N, j ≠ iN → j ≠ i1N →
      ggDepAα p N i j * ggDepAh p N i j = 0 := by
    intro j hj1 hj2
    have hjv1 : j.val ≠ i.val := fun h => hj1 (Fin.ext h)
    have hjv2 : j.val ≠ i.val + 1 := fun h => hj2 (Fin.ext h)
    simp only [ggDepAα, ggDepAh]
    by_cases hjN : j.val + 1 = N
    · simp [hjN]
    · simp [hjN, hjv1, hjv2]
  have hsum : (∑ j, ggDepAα p N i j * ggDepAh p N i j) =
      ggDepAα p N i iN * ggDepAh p N i iN +
        ggDepAα p N i i1N * ggDepAh p N i i1N := by
    have hsub : (∑ j ∈ ({iN, i1N} : Finset (Fin N)), ggDepAα p N i j * ggDepAh p N i j)
        = ∑ j, ggDepAα p N i j * ggDepAh p N i j :=
      Finset.sum_subset (by intro x _; simp) (fun x _ hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        exact hsupp x hx.1 hx.2)
    rw [← hsub, Finset.sum_pair hne]
  rw [hsum]
  have e1 : ggDepAα p N i iN = 1 := by
    simp only [ggDepAα, iN, Fin.val_mk]
    rw [if_neg hi1]
    simp [hii]
  have f1 : ggDepAh p N i iN = 1 + (if i.val + 2 = N then 1 else 0) := by
    simp only [ggDepAh, iN, Fin.val_mk]
    rw [if_neg hi1]
    simp [hii]
  by_cases h2 : i.val + 2 = N
  · have e2 : ggDepAα p N i i1N = 0 := by
      simp only [ggDepAα, i1N, Fin.val_mk]
      rw [if_pos (show i.val + 1 + 1 = N by omega)]
    have f2 : ggDepAh p N i i1N = 0 := by
      simp only [ggDepAh, i1N, Fin.val_mk]
      rw [if_pos (show i.val + 1 + 1 = N by omega)]
    rw [e1, f1, e2, f2, if_pos h2]
    ring
  · have hA : ¬ (i.val + 1 + 1 = N) := by omega
    have hB : ¬ (i.val + 1 = i.val) := by omega
    have e2 : ggDepAα p N i i1N = -1 := by
      simp only [ggDepAα, i1N, Fin.val_mk]
      rw [if_neg hA, if_neg hB]
      simp
    have f2 : ggDepAh p N i i1N = -1 := by
      simp only [ggDepAh, i1N, Fin.val_mk]
      rw [if_neg hA, if_neg hB, if_neg h2]
      simp
    rw [e1, f1, e2, f2, if_neg h2]
    ring

lemma l05nNC_H_length (p N i : ℕ) : (ggDepANH p N i).length = N := by
  simp [ggDepANH]

lemma l05nNC_A_length (p N i : ℕ) : (ggDepANA p N i).length = N := by
  simp [ggDepANA]

lemma l05nNC_sub_length {p N : ℕ} {a b : List ℕ} (ha : a.length = N) (hb : b.length = N) :
    (ggDepANSub p a b).length = N := by
  simp only [ggDepANSub, List.length_zipWith, ha, hb, min_self]

lemma l05nNC_smul_length {p N k : ℕ} {a : List ℕ} (ha : a.length = N) :
    (ggDepANSmul p k a).length = N := by
  simp only [ggDepANSmul, List.length_map, ha]

lemma l05nNC_gen_length1 {p N : ℕ} {ha aa : List ℕ} (hha : ha.length = N)
    (haa : aa.length = N) (i : ℕ) : (ggDepANGen p N ha aa i).1.length = N := by
  simp only [ggDepANGen]
  split
  · exact l05nNC_H_length p N i
  · exact hha

lemma l05nNC_gen_length2 {p N : ℕ} {ha aa : List ℕ} (hha : ha.length = N)
    (haa : aa.length = N) (i : ℕ) : (ggDepANGen p N ha aa i).2.length = N := by
  simp only [ggDepANGen]
  split
  · exact l05nNC_A_length p N i
  · exact haa

lemma l05nNC_conj_length {p N : ℕ} {q g : GGDepANPair} (hq1 : q.1.length = N)
    (hq2 : q.2.length = N) (hg1 : g.1.length = N) (hg2 : g.2.length = N) :
    (ggDepANConj p q g).1.length = N ∧ (ggDepANConj p q g).2.length = N := by
  constructor
  · simp only [ggDepANConj]
    exact l05nNC_sub_length hq1 (l05nNC_smul_length hg1)
  · simp only [ggDepANConj]
    exact l05nNC_sub_length hq2 (l05nNC_smul_length hg2)

lemma l05nNC_word_length {p N : ℕ} {ha aa : List ℕ} (hha : ha.length = N)
    (haa : aa.length = N) (w : List ℕ) (q : GGDepANPair) (hq1 : q.1.length = N)
    (hq2 : q.2.length = N) :
    (ggDepANWord p N q w ha aa).1.length = N ∧ (ggDepANWord p N q w ha aa).2.length = N := by
  induction w generalizing q with
  | nil => simpa [ggDepANWord] using ⟨hq1, hq2⟩
  | cons g w ih =>
      simp only [ggDepANWord, List.foldr_cons]
      exact l05nNC_conj_length (ih q hq1 hq2).1 (ih q hq1 hq2).2
        (l05nNC_gen_length1 hha haa g) (l05nNC_gen_length2 hha haa g)

lemma l05nNC_toZ_sub {p N : ℕ} [Fact p.Prime] {a b : List ℕ} (ha : a.length = N)
    (hb : b.length = N) :
    ggDepANToZ p N (ggDepANSub p a b) = ggDepANToZ p N a - ggDepANToZ p N b := by
  funext j
  have hj : j.val < N := j.isLt
  have hja : j.val < a.length := by rw [ha]; exact hj
  have hjb : j.val < b.length := by rw [hb]; exact hj
  have hjl : j.val < (a.zipWith (fun x y => (x + (p - y % p)) % p) b).length := by
    rw [List.length_zipWith, ha, hb, min_self]; exact hj
  simp only [ggDepANToZ, ggDepANSub, Pi.sub_apply]
  rw [List.getD_eq_getElem (l := a.zipWith _ b) (d := 0) (n := j.val) hjl,
    List.getD_eq_getElem (l := a) (d := 0) (n := j.val) hja,
    List.getD_eq_getElem (l := b) (d := 0) (n := j.val) hjb]
  rw [List.getElem_zipWith]
  exact l05nNC_cast_sub p _ _

lemma l05nNC_toZ_smul {p N : ℕ} [Fact p.Prime] {a : List ℕ} (ha : a.length = N) (k : ℕ) :
    ggDepANToZ p N (ggDepANSmul p k a) = (k : ZMod p) • ggDepANToZ p N a := by
  funext j
  have hj : j.val < N := j.isLt
  have hja : j.val < a.length := by rw [ha]; exact hj
  have hjl : j.val < (a.map (fun x => k * x % p)).length := by
    rw [List.length_map, ha]; exact hj
  simp only [ggDepANToZ, ggDepANSmul, Pi.smul_apply, smul_eq_mul]
  rw [List.getD_eq_getElem (l := a.map _) (d := 0) (n := j.val) hjl,
    List.getD_eq_getElem (l := a) (d := 0) (n := j.val) hja]
  rw [List.getElem_map, ZMod.natCast_mod, Nat.cast_mul]

lemma l05nNC_toZ_conj {p N : ℕ} [Fact p.Prime] {q g : GGDepANPair} (hq1 : q.1.length = N)
    (hq2 : q.2.length = N) (hg1 : g.1.length = N) (hg2 : g.2.length = N) :
    ggDepANToZ p N (ggDepANConj p q g).1 =
        ggDepANToZ p N q.1 - ggDepAdot (ggDepANToZ p N g.2) (ggDepANToZ p N q.1) •
          ggDepANToZ p N g.1 ∧
      ggDepANToZ p N (ggDepANConj p q g).2 =
        ggDepANToZ p N q.2 - ggDepAdot (ggDepANToZ p N q.2) (ggDepANToZ p N g.1) •
          ggDepANToZ p N g.2 := by
  constructor
  · simp only [ggDepANConj]
    rw [l05nNC_toZ_sub hq1 (l05nNC_smul_length hg1), l05nNC_toZ_smul hg1,
      ggDepANDot_cast g.2 q.1 hg2 hq1]
  · simp only [ggDepANConj]
    rw [l05nNC_toZ_sub hq2 (l05nNC_smul_length hg2), l05nNC_toZ_smul hg2,
      ggDepANDot_cast q.2 g.1 hq2 hg1]

private lemma l05nNC_form_apply {p N : ℕ} (f v : GGDepAE p N) :
    ggDepAform f v = ggDepAdot f v := by
  simp [ggDepAform, ggDepAdot]

lemma l05nNC_refl_apply {p N : ℕ} (c f v : GGDepAE p N) :
    ggDepARefl c f v = v - ggDepAdot f v • c := by
  simp [ggDepARefl, l05nNC_form_apply]

private lemma l05nNC_dot_sub {p N : ℕ} (a v w : GGDepAE p N) :
    ggDepAdot a (v - w) = ggDepAdot a v - ggDepAdot a w := by
  rw [← l05nNC_form_apply a (v - w), map_sub, l05nNC_form_apply a v, l05nNC_form_apply a w]

private lemma l05nNC_dot_smul {p N : ℕ} (a : GGDepAE p N) (k : ZMod p) (v : GGDepAE p N) :
    ggDepAdot a (k • v) = k * ggDepAdot a v := by
  rw [← l05nNC_form_apply a (k • v), map_smul, l05nNC_form_apply a v]
  simp

private lemma l05nNC_dot_sub_left {p N : ℕ} (a b v : GGDepAE p N) :
    ggDepAdot (a - b) v = ggDepAdot a v - ggDepAdot b v := by
  simp only [ggDepAdot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma l05nNC_dot_smul_left {p N : ℕ} (k : ZMod p) (a v : GGDepAE p N) :
    ggDepAdot (k • a) v = k * ggDepAdot a v := by
  simp only [ggDepAdot, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [← Finset.mul_sum]

lemma l05nNC_refl_conj {p N : ℕ} (c f gc gf : GGDepAE p N)
    (h : ggDepAdot gf gc = 2) :
    ggDepARefl gc gf * ggDepARefl c f * ggDepARefl gc gf =
      ggDepARefl (c - ggDepAdot gf c • gc) (f - ggDepAdot f gc • gf) := by
  apply LinearMap.ext; intro v
  ext j
  simp only [Module.End.mul_apply, l05nNC_refl_apply, Pi.sub_apply, Pi.smul_apply,
    l05nNC_dot_sub, l05nNC_dot_smul, l05nNC_dot_sub_left, l05nNC_dot_smul_left, h]
  ring

lemma l05nNC_conj_dot {p N : ℕ} (c f gc gf : GGDepAE p N)
    (h : ggDepAdot f c = 2) (hg : ggDepAdot gf gc = 2) :
    ggDepAdot (f - ggDepAdot f gc • gf) (c - ggDepAdot gf c • gc) = 2 := by
  rw [l05nNC_dot_sub, l05nNC_dot_sub_left, l05nNC_dot_smul_left, l05nNC_dot_smul,
    l05nNC_dot_sub_left, l05nNC_dot_smul_left, h, hg]
  ring

lemma l05nNC_gen_dot {p N : ℕ} [Fact p.Prime] {ha aa : List ℕ} (hha : ha.length = N)
    (haa : aa.length = N) (hdot : ggDepANDot p aa ha = 2 % p) (g : ℕ) :
    ggDepAdot (ggDepANToZ p N (ggDepANGen p N ha aa g).2)
      (ggDepANToZ p N (ggDepANGen p N ha aa g).1) = 2 := by
  by_cases h : g + 1 < N
  · simp only [ggDepANGen, if_pos h]
    rw [l05nNC_toZ_A h, l05nNC_toZ_H h]
    exact l05nNC_pair_i ⟨g, by omega⟩
  · simp only [ggDepANGen, if_neg h]
    rw [← ggDepANDot_cast aa ha haa hha, hdot, ZMod.natCast_mod]
    rfl

lemma l05nNC_gen_mem {p N : ℕ} [Fact p.Prime] {ha aa : List ℕ} (hha : ha.length = N)
    (haa : aa.length = N) (g : ℕ) :
    ggDepARefl (ggDepANToZ p N (ggDepANGen p N ha aa g).1)
      (ggDepANToZ p N (ggDepANGen p N ha aa g).2) ∈
      Submonoid.closure (Set.range (fun j : Fin (N - 1) =>
        ggDepARefl (ggDepAh p N j) (ggDepAα p N j)) ∪
        {ggDepARefl (ggDepANToZ p N ha) (ggDepANToZ p N aa)}) := by
  by_cases h : g + 1 < N
  · simp only [ggDepANGen, if_pos h]
    rw [l05nNC_toZ_H h, l05nNC_toZ_A h]
    exact Submonoid.subset_closure (Or.inl ⟨⟨g, by omega⟩, rfl⟩)
  · simp only [ggDepANGen, if_neg h]
    exact Submonoid.subset_closure (Or.inr rfl)

private lemma l05nNC_word_cons (p N : ℕ) (q : GGDepANPair) (g : ℕ) (w : List ℕ) (ha aa : List ℕ) :
    ggDepANWord p N q (g :: w) ha aa =
      ggDepANConj p (ggDepANWord p N q w ha aa) (ggDepANGen p N ha aa g) := by
  simp [ggDepANWord]

lemma l05nNC_word {p N : ℕ} [Fact p.Prime] (ha aa : List ℕ) (hha : ha.length = N)
    (haa : aa.length = N) (S : Submonoid (Module.End (ZMod p) (GGDepAE p N)))
    (hdg : ∀ g : ℕ, ggDepAdot (ggDepANToZ p N (ggDepANGen p N ha aa g).2)
      (ggDepANToZ p N (ggDepANGen p N ha aa g).1) = 2)
    (hmem : ∀ g : ℕ, ggDepARefl (ggDepANToZ p N (ggDepANGen p N ha aa g).1)
      (ggDepANToZ p N (ggDepANGen p N ha aa g).2) ∈ S)
    (w : List ℕ) (q : GGDepANPair) (hq1 : q.1.length = N) (hq2 : q.2.length = N)
    (hdq : ggDepAdot (ggDepANToZ p N q.2) (ggDepANToZ p N q.1) = 2)
    (hq : ggDepARefl (ggDepANToZ p N q.1) (ggDepANToZ p N q.2) ∈ S) :
    ggDepAdot (ggDepANToZ p N (ggDepANWord p N q w ha aa).2)
        (ggDepANToZ p N (ggDepANWord p N q w ha aa).1) = 2 ∧
      ggDepARefl (ggDepANToZ p N (ggDepANWord p N q w ha aa).1)
        (ggDepANToZ p N (ggDepANWord p N q w ha aa).2) ∈ S := by
  induction w generalizing q with
  | nil => exact ⟨by simpa [ggDepANWord] using hdq, by simpa [ggDepANWord] using hq⟩
  | cons g w ih =>
      rw [l05nNC_word_cons]
      have hQ1 : (ggDepANWord p N q w ha aa).1.length = N :=
        (l05nNC_word_length hha haa w q hq1 hq2).1
      have hQ2 : (ggDepANWord p N q w ha aa).2.length = N :=
        (l05nNC_word_length hha haa w q hq1 hq2).2
      have hG1 : (ggDepANGen p N ha aa g).1.length = N := l05nNC_gen_length1 hha haa g
      have hG2 : (ggDepANGen p N ha aa g).2.length = N := l05nNC_gen_length2 hha haa g
      obtain ⟨ihd, ihm⟩ := ih q hq1 hq2 hdq hq
      obtain ⟨hc1, hc2⟩ := l05nNC_toZ_conj (p := p) (N := N) (q := ggDepANWord p N q w ha aa)
        (g := ggDepANGen p N ha aa g) hQ1 hQ2 hG1 hG2
      rw [hc1, hc2]
      refine ⟨l05nNC_conj_dot _ _ _ _ ihd (hdg g), ?_⟩
      rw [← l05nNC_refl_conj (ggDepANToZ p N (ggDepANWord p N q w ha aa).1)
        (ggDepANToZ p N (ggDepANWord p N q w ha aa).2)
        (ggDepANToZ p N (ggDepANGen p N ha aa g).1)
        (ggDepANToZ p N (ggDepANGen p N ha aa g).2) (hdg g)]
      exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hmem g) ihm) (hmem g)

private theorem l05nNC_main {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hN : 5 ≤ N)
    (w : GGDepANWit) (hw : ggDepANWitValid N w = true) (ha aa : List ℕ) (hha : ha.length = N)
    (haa : aa.length = N) (hdot : ggDepANDot p aa ha = 2 % p)
    (ht : ggDepANWitTest p N w ha aa = true) :
    ∃ g ∈ Submonoid.closure (Set.range (fun i : Fin (N - 1) =>
        ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪
        {ggDepARefl (ggDepANToZ p N ha) (ggDepANToZ p N aa)}), GGDepAIsTv g := by
  set S : Submonoid (Module.End (ZMod p) (GGDepAE p N)) :=
    Submonoid.closure (Set.range (fun i : Fin (N - 1) =>
      ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪
      {ggDepARefl (ggDepANToZ p N ha) (ggDepANToZ p N aa)}) with hSdef
  have hdg : ∀ g : ℕ, ggDepAdot (ggDepANToZ p N (ggDepANGen p N ha aa g).2)
      (ggDepANToZ p N (ggDepANGen p N ha aa g).1) = 2 := fun g => l05nNC_gen_dot hha haa hdot g
  have hmem : ∀ g : ℕ, ggDepARefl (ggDepANToZ p N (ggDepANGen p N ha aa g).1)
      (ggDepANToZ p N (ggDepANGen p N ha aa g).2) ∈ S := by
    intro g; rw [hSdef]; exact l05nNC_gen_mem hha haa g
  set q1 : GGDepANPair := ggDepANWord p N (ggDepANGen p N ha aa w.g1) w.w1 ha aa with hq1def
  set q2 : GGDepANPair := ggDepANWord p N (ggDepANGen p N ha aa w.g2) w.w2 ha aa with hq2def
  have hL1 : q1.1.length = N :=
    (l05nNC_word_length hha haa w.w1 (ggDepANGen p N ha aa w.g1)
      (l05nNC_gen_length1 hha haa w.g1) (l05nNC_gen_length2 hha haa w.g1)).1
  have hL2 : q1.2.length = N :=
    (l05nNC_word_length hha haa w.w1 (ggDepANGen p N ha aa w.g1)
      (l05nNC_gen_length1 hha haa w.g1) (l05nNC_gen_length2 hha haa w.g1)).2
  have hL3 : q2.1.length = N :=
    (l05nNC_word_length hha haa w.w2 (ggDepANGen p N ha aa w.g2)
      (l05nNC_gen_length1 hha haa w.g2) (l05nNC_gen_length2 hha haa w.g2)).1
  have hL4 : q2.2.length = N :=
    (l05nNC_word_length hha haa w.w2 (ggDepANGen p N ha aa w.g2)
      (l05nNC_gen_length1 hha haa w.g2) (l05nNC_gen_length2 hha haa w.g2)).2
  have hword1 : ggDepAdot (ggDepANToZ p N q1.2) (ggDepANToZ p N q1.1) = 2 ∧
      ggDepARefl (ggDepANToZ p N q1.1) (ggDepANToZ p N q1.2) ∈ S := by
    rw [hq1def]
    exact l05nNC_word ha aa hha haa S hdg hmem w.w1 (ggDepANGen p N ha aa w.g1)
      (l05nNC_gen_length1 hha haa w.g1) (l05nNC_gen_length2 hha haa w.g1) (hdg w.g1) (hmem w.g1)
  have hword2 : ggDepAdot (ggDepANToZ p N q2.2) (ggDepANToZ p N q2.1) = 2 ∧
      ggDepARefl (ggDepANToZ p N q2.1) (ggDepANToZ p N q2.2) ∈ S := by
    rw [hq2def]
    exact l05nNC_word ha aa hha haa S hdg hmem w.w2 (ggDepANGen p N ha aa w.g2)
      (l05nNC_gen_length1 hha haa w.g2) (l05nNC_gen_length2 hha haa w.g2) (hdg w.g2) (hmem w.g2)
  have hdot1 : ggDepANDot p q1.2 q1.1 = 2 % p := by
    have h := ggDepANDot_cast (p := p) (N := N) q1.2 q1.1 hL2 hL1
    rw [hword1.1] at h
    have h2 : ((ggDepANDot p q1.2 q1.1 : ℕ) : ZMod p) = ((2 % p : ℕ) : ZMod p) := by
      rw [ZMod.natCast_mod]; exact h
    rw [ZMod.natCast_eq_natCast_iff'] at h2
    simpa [ggDepANDot, Nat.mod_mod] using h2
  have hdot2 : ggDepANDot p q2.2 q2.1 = 2 % p := by
    have h := ggDepANDot_cast (p := p) (N := N) q2.2 q2.1 hL4 hL3
    rw [hword2.1] at h
    have h2 : ((ggDepANDot p q2.2 q2.1 : ℕ) : ZMod p) = ((2 % p : ℕ) : ZMod p) := by
      rw [ZMod.natCast_mod]; exact h
    rw [ZMod.natCast_eq_natCast_iff'] at h2
    simpa [ggDepANDot, Nat.mod_mod] using h2
  have ht' : ggDepANTestPair p q1 q2 = true := by
    rw [hq1def, hq2def]
    simpa only [ggDepANWitTest] using ht
  have htv := ggDepANTestPair_sound (p := p) (N := N) hp2 q1 q2 hL1 hL2 hL3 hL4 hdot1 hdot2 ht'
  have hfin : ggDepARefl (ggDepANToZ p N q1.1) (ggDepANToZ p N q1.2) *
      ggDepARefl (ggDepANToZ p N q2.1) (ggDepANToZ p N q2.2) ∈ S :=
    Submonoid.mul_mem _ hword1.2 hword2.2
  rw [hSdef] at hfin
  exact ⟨_, hfin, htv.2.2⟩

theorem ggDepANWitTest_sound {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hN : 5 ≤ N)
    (w : GGDepANWit) (hw : ggDepANWitValid N w = true) (ha aa : List ℕ) (hha : ha.length = N)
    (haa : aa.length = N) (hdot : ggDepANDot p aa ha = 2 % p)
    (ht : ggDepANWitTest p N w ha aa = true) :
    ∃ g ∈ Submonoid.closure (Set.range (fun i : Fin (N - 1) =>
        ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪
        {ggDepARefl (ggDepANToZ p N ha) (ggDepANToZ p N aa)}), GGDepAIsTv g := by
  exact l05nNC_main hp2 hN w hw ha aa hha haa hdot ht

theorem ggDepANPatB_iff {N : ℕ} (b c0 : Fin (N - 1)) (mi ni : ℕ) (hmi : mi = 1 ∨ mi = 2)
    (hni : ni = 1 ∨ ni = 2) :
    ggDepANPatB N b.val c0.val mi ni = true ↔ GGDepAPat N b c0 (-(mi : ℤ)) (-(ni : ℤ)) := by
  rcases hmi with rfl | rfl <;> rcases hni with rfl | rfl <;>
  · unfold ggDepANPatB GGDepAPat
    rw [decide_eq_true b.isLt, decide_eq_true c0.isLt]
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.true_and, Bool.true_or, Bool.false_and,
      Bool.false_or, Bool.and_false, Bool.or_false, Bool.and_true, Bool.or_true,
      decide_eq_true_iff, beq_iff_eq]
    simp [Fin.ext_iff]
    try tauto

private lemma l05nND_pat_wit {N : ℕ} (b c0 : Fin (N - 1)) {m n : ℤ}
    (h : GGDepAPat N b c0 m n) :
    ∃ mi ni : ℕ, (mi = 1 ∨ mi = 2) ∧ (ni = 1 ∨ ni = 2) ∧
      m = -(mi : ℤ) ∧ n = -(ni : ℤ) ∧ ggDepANPatB N b.val c0.val mi ni = true := by
  unfold GGDepAPat at h
  obtain ⟨hb, hbc, h⟩ := h
  rcases h with ⟨hA, (⟨hm, hn⟩ | ⟨hm, hn⟩ | ⟨hm, hn⟩)⟩ | ⟨hB, hC, hm, hn⟩ | ⟨hE, hF, hm, hn⟩
  · exact ⟨1, 1, Or.inl rfl, Or.inl rfl, by omega, by omega, by
      rw [ggDepANPatB_iff b c0 1 1 (Or.inl rfl) (Or.inl rfl)]
      exact ⟨hb, hbc, Or.inl ⟨hA, Or.inl ⟨rfl, rfl⟩⟩⟩⟩
  · exact ⟨1, 2, Or.inl rfl, Or.inr rfl, by omega, by omega, by
      rw [ggDepANPatB_iff b c0 1 2 (Or.inl rfl) (Or.inr rfl)]
      exact ⟨hb, hbc, Or.inl ⟨hA, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩⟩⟩
  · exact ⟨2, 1, Or.inr rfl, Or.inl rfl, by omega, by omega, by
      rw [ggDepANPatB_iff b c0 2 1 (Or.inr rfl) (Or.inl rfl)]
      exact ⟨hb, hbc, Or.inl ⟨hA, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩⟩⟩
  · exact ⟨1, 1, Or.inl rfl, Or.inl rfl, by omega, by omega, by
      rw [ggDepANPatB_iff b c0 1 1 (Or.inl rfl) (Or.inl rfl)]
      exact ⟨hb, hbc, Or.inr (Or.inl ⟨hB, hC, rfl, rfl⟩)⟩⟩
  · exact ⟨1, 1, Or.inl rfl, Or.inl rfl, by omega, by omega, by
      rw [ggDepANPatB_iff b c0 1 1 (Or.inl rfl) (Or.inl rfl)]
      exact ⟨hb, hbc, Or.inr (Or.inr ⟨hE, hF, rfl, rfl⟩)⟩⟩

lemma l05nND_HaParam_length (p N b c0 n s t : ℕ) :
    (ggDepANHaParam p N b c0 n s t).length = N := by
  simp [ggDepANHaParam]

lemma l05nND_AaParam_length (p N b c0 m u v : ℕ) :
    (ggDepANAaParam p N b c0 m u v).length = N := by
  simp [ggDepANAaParam]

lemma l05nND_HaParam_mod (p N b c0 n s t : ℕ) :
    ggDepANHaParam p N b c0 n (s % p) (t % p) = ggDepANHaParam p N b c0 n s t := by
  rw [ggDepANHaParam, ggDepANHaParam, List.map_eq_map_iff]
  intro j hj
  simp only [List.mem_range] at hj
  split_ifs <;> simp_all [Nat.mod_mod, Nat.add_mod]

lemma l05nND_AaParam_mod (p N b c0 m u v : ℕ) :
    ggDepANAaParam p N b c0 m (u % p) (v % p) = ggDepANAaParam p N b c0 m u v := by
  rw [ggDepANAaParam, ggDepANAaParam, List.map_eq_map_iff]
  intro j hj
  simp only [List.mem_range] at hj
  split_ifs <;> simp_all [Nat.mod_mod, Nat.add_mod]

lemma l05nND_cast_neg (p mi : ℕ) (hmi : mi ≤ p) :
    (((p - mi) % p : ℕ) : ZMod p) = -((mi : ℕ) : ZMod p) := by
  rw [ZMod.natCast_mod, Nat.cast_sub hmi, ZMod.natCast_self, zero_sub]

private lemma l05nND_dot_single {p N : ℕ} (f : GGDepAE p N) (j : Fin N) :
    ggDepAdot f (Pi.single j 1) = f j := by
  rw [ggDepAdot, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro hj; exact absurd (Finset.mem_univ j) hj

lemma l05nND_dot_ax {p N : ℕ} (f : GGDepAE p N) (hN : 1 ≤ N) :
    ggDepAdot f (ggDepAx p N) = f ⟨N - 1, by omega⟩ := by
  have hax : ggDepAx p N = Pi.single ⟨N - 1, by omega⟩ (1 : ZMod p) := by
    funext j
    rw [ggDepAx]
    by_cases hj : j.val + 1 = N
    · have hji : j = ⟨N - 1, by omega⟩ := by
        apply Fin.ext
        show j.val = N - 1
        omega
      rw [if_pos hj, hji, Pi.single_eq_same]
    · have hji : j ≠ ⟨N - 1, by omega⟩ := by
        intro hh
        rw [hh] at hj
        exact hj (Nat.sub_add_cancel hN)
      rw [if_neg hj, Pi.single_eq_of_ne hji]
  rw [hax, l05nND_dot_single]

lemma l05nND_AaParam_getD (p N b c0 m u v : ℕ) (hN : 1 ≤ N) :
    (ggDepANAaParam p N b c0 m u v).getD (N - 1) 0 = v % p := by
  rw [ggDepANAaParam, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (show N - 1 < N by omega)]
  simp [Nat.sub_add_cancel hN]

private lemma l05nND_dot_eq_two {p : ℕ} (hp : 5 ≤ p) {x : ℕ} (hx : x < p)
    (h : (x : ZMod p) = 2) : x = 2 % p := by
  have h2 : x % p = 2 % p := by
    have h' : (x : ZMod p).val = ((2 : ℕ) : ZMod p).val := congrArg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_natCast] at h'
  rw [Nat.mod_eq_of_lt (by omega : 2 < p)]
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by omega : 2 < p)] at h2
  exact h2

theorem ggDepANCheck_sound {p N : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hpN : p ∣ N) (hN : 5 ≤ N)
    (data : GGDepANData) (h : ggDepANCheck p N data = true) : GGDepASmallCells p N := by
  intro b c0 m n hpat ha αa hpairs hdot2 hx
  have hpat' := hpat
  unfold GGDepAPat at hpat'
  obtain ⟨hb, hbc, -⟩ := hpat'
  obtain ⟨mi, ni, hmi, hni, hm, hn, hpatB⟩ := l05nND_pat_wit b c0 hpat
  rw [ggDepANCheck, Bool.and_eq_true] at h
  obtain ⟨hvalid, hcheck⟩ := h
  have hb_mem : b.val ∈ List.range (N - 1) := List.mem_range.mpr b.isLt
  have hc0_mem : c0.val ∈ List.range (N - 1) := List.mem_range.mpr c0.isLt
  have hmi_mem : mi ∈ [1, 2] := by rcases hmi with rfl | rfl <;> simp
  have hni_mem : ni ∈ [1, 2] := by rcases hni with rfl | rfl <;> simp
  have h1 := List.all_eq_true.mp hcheck b.val hb_mem
  have h2 := List.all_eq_true.mp h1 c0.val hc0_mem
  have h3 := List.all_eq_true.mp h2 mi hmi_mem
  have h4 := List.all_eq_true.mp h3 ni hni_mem
  rw [if_pos hpatB] at h4
  cases hlook : data.lookup (b.val, c0.val, mi, ni) with
  | none => rw [hlook] at h4; simp at h4
  | some wits =>
    rw [hlook] at h4
    obtain ⟨l₁, l₂, hdata, -⟩ := List.lookup_eq_some_iff.mp hlook
    subst hdata
    have hentry : (((b.val, c0.val, mi, ni) : ℕ × ℕ × ℕ × ℕ), wits) ∈
        l₁ ++ (((b.val, c0.val, mi, ni) : ℕ × ℕ × ℕ × ℕ), wits) :: l₂ := by simp
    simp only [ggDepANCases] at h4
    have hm_cast : (m : ZMod p) = (((p - mi) % p : ℕ) : ZMod p) := by
      rw [hm, Int.cast_neg, Int.cast_natCast]
      exact (l05nND_cast_neg p mi (by omega)).symm
    have hn_cast : (n : ZMod p) = (((p - ni) % p : ℕ) : ZMod p) := by
      rw [hn, Int.cast_neg, Int.cast_natCast]
      exact (l05nND_cast_neg p ni (by omega)).symm
    have hpairA : ∀ c : Fin (N - 1), c ≠ b →
        ggDepAdot αa (ggDepAh p N c) = if c = c0 then (((p - mi) % p : ℕ) : ZMod p) else 0 := by
      intro c hc
      rw [(hpairs c hc).1, hm_cast]
    obtain ⟨u, v, huv⟩ :=
      ggDepANAa_complete hpN hN b c0 hb hbc ((p - mi) % p) αa hpairA
    have hpairH : ∀ c : Fin (N - 1), c ≠ b →
        ggDepAdot (ggDepAα p N c) ha = if c = c0 then (((p - ni) % p : ℕ) : ZMod p) else 0 := by
      intro c hc
      rw [(hpairs c hc).2, hn_cast]
    obtain ⟨s, t, hst⟩ :=
      ggDepANHa_complete hN b c0 hb hbc ((p - ni) % p) ha hpairH
    have hs : s % p ∈ List.range p := List.mem_range.mpr (Nat.mod_lt s (by omega))
    have ht : t % p ∈ List.range p := List.mem_range.mpr (Nat.mod_lt t (by omega))
    have hu : u % p ∈ List.range p := List.mem_range.mpr (Nat.mod_lt u (by omega))
    have hv : v % p ∈ List.range p := List.mem_range.mpr (Nat.mod_lt v (by omega))
    have hcase := List.all_eq_true.mp h4 (s % p) hs
    have hcase := List.all_eq_true.mp hcase (t % p) ht
    have hcase := List.all_eq_true.mp hcase (u % p) hu
    have hcase := List.all_eq_true.mp hcase (v % p) hv
    have hxval : ggDepAdot (ggDepANToZ p N
        (ggDepANAaParam p N b.val c0.val ((p - mi) % p) u v)) (ggDepAx p N) =
        ((v % p : ℕ) : ZMod p) := by
      rw [l05nND_dot_ax _ (by omega)]
      show ((ggDepANAaParam p N b.val c0.val ((p - mi) % p) u v).getD (N - 1) 0 : ZMod p) =
        ((v % p : ℕ) : ZMod p)
      rw [l05nND_AaParam_getD p N b.val c0.val ((p - mi) % p) u v (by omega)]
    have hv0 : v % p ≠ 0 := by
      intro hvz
      apply hx
      rw [huv, hxval, hvz]
      simp
    have hdotN : ggDepANDot p (ggDepANAaParam p N b.val c0.val ((p - mi) % p) (u % p) (v % p))
        (ggDepANHaParam p N b.val c0.val ((p - ni) % p) (s % p) (t % p)) = 2 % p := by
      rw [l05nND_AaParam_mod, l05nND_HaParam_mod]
      refine l05nND_dot_eq_two hp (by rw [ggDepANDot]; exact Nat.mod_lt _ (by omega)) ?_
      rw [ggDepANDot_cast _ _ (l05nND_AaParam_length ..) (l05nND_HaParam_length ..),
        ← huv, ← hst]
      exact hdot2
    have hvv : (v % p) % p ≠ 0 := by
      rwa [Nat.mod_eq_of_lt (Nat.mod_lt v (by omega))]
    have hcond : (ggDepANDot p (ggDepANAaParam p N b.val c0.val ((p - mi) % p) (u % p) (v % p))
        (ggDepANHaParam p N b.val c0.val ((p - ni) % p) (s % p) (t % p)) == 2 % p &&
        (v % p) % p != 0) = true := by
      rw [Bool.and_eq_true]
      exact ⟨beq_iff_eq.mpr hdotN, bne_iff_ne.mpr hvv⟩
    rw [if_pos hcond] at hcase
    obtain ⟨w, hwmem, hwtest⟩ := List.any_eq_true.mp hcase
    have hwvalid : ggDepANWitValid N w = true :=
      List.all_eq_true.mp
        (List.all_eq_true.mp hvalid (((b.val, c0.val, mi, ni) : ℕ × ℕ × ℕ × ℕ), wits) hentry)
        w hwmem
    have hlenH : (ggDepANHaParam p N b.val c0.val ((p - ni) % p) (s % p) (t % p)).length = N :=
      l05nND_HaParam_length ..
    have hlenA : (ggDepANAaParam p N b.val c0.val ((p - mi) % p) (u % p) (v % p)).length = N :=
      l05nND_AaParam_length ..
    obtain ⟨g, hgmem, hgtv⟩ :=
      ggDepANWitTest_sound (by omega : p ≠ 2) hN w hwvalid
        (ggDepANHaParam p N b.val c0.val ((p - ni) % p) (s % p) (t % p))
        (ggDepANAaParam p N b.val c0.val ((p - mi) % p) (u % p) (v % p))
        hlenH hlenA hdotN hwtest
    refine ⟨g, ?_, hgtv⟩
    have hHa : ggDepANToZ p N (ggDepANHaParam p N b.val c0.val ((p - ni) % p) (s % p) (t % p)) =
        ha := by
      rw [l05nND_HaParam_mod]
      exact hst.symm
    have hAa : ggDepANToZ p N (ggDepANAaParam p N b.val c0.val ((p - mi) % p) (u % p) (v % p)) =
        αa := by
      rw [l05nND_AaParam_mod]
      exact huv.symm
    rw [hHa, hAa] at hgmem
    exact hgmem

end CFSG.StandardType
