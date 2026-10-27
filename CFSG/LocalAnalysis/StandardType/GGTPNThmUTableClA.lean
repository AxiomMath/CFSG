module

public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableClDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggTUClA_odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨2 ^ k - 1, ?_⟩
  have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [pow_succ']
  omega

private theorem ggTUClA_odd_two_pow_add_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨2 ^ k, ?_⟩
  rw [pow_succ']

private theorem ggTUClA_odd {p n : ℕ} (hn : 1 ≤ n) (hd : ggMultOrd p n ≠ 0) : Odd p := by
  unfold ggMultOrd at hd
  split_ifs at hd with h1 h2
  · exact Odd.of_dvd_nat (ggTUClA_odd_two_pow_sub_one hn) h1
  · exact Odd.of_dvd_nat (ggTUClA_odd_two_pow_add_one hn) h2
  · omega

private theorem ggTUClA_two_mul_half_add_one {p : ℕ} (hodd : Odd p) :
    2 * ((p - 1) / 2) + 1 = p := by
  have hp : 2 * (p / 2) + 1 = p := Nat.two_mul_div_two_add_one_of_odd hodd
  have h1 : (p - 1) / 2 = p / 2 := by
    have h2 : p - 1 = 2 * (p / 2) := by omega
    rw [h2, Nat.mul_comm 2 (p / 2)]
    exact Nat.mul_div_left _ (by norm_num : 0 < 2)
  omega

private theorem ggTUClA_dvd_of_ord_eq_one {p n : ℕ} (h : ggMultOrd p n = 1) :
    p ∣ 2 ^ n - 1 := by
  unfold ggMultOrd at h
  by_cases h1 : p ∣ 2 ^ n - 1
  · exact h1
  · rw [if_neg h1] at h
    split_ifs at h <;> omega

private theorem ggTUClA_dvd_of_ord_eq_two {p n : ℕ} (h : ggMultOrd p n = 2) :
    p ∣ 2 ^ n + 1 := by
  unfold ggMultOrd at h
  by_cases h1 : p ∣ 2 ^ n - 1
  · rw [if_pos h1] at h
    omega
  · rw [if_neg h1] at h
    by_cases h2 : p ∣ 2 ^ n + 1
    · exact h2
    · rw [if_neg h2] at h
      omega

private theorem ggTUClA_ord_eq_one_or_two {p n : ℕ} (hd : ggMultOrd p n ≠ 0) :
    ggMultOrd p n = 1 ∨ ggMultOrd p n = 2 := by
  by_cases h1 : p ∣ 2 ^ n - 1
  · unfold ggMultOrd
    rw [if_pos h1]
    exact Or.inl rfl
  · by_cases h2 : p ∣ 2 ^ n + 1
    · unfold ggMultOrd
      rw [if_neg h1, if_pos h2]
      exact Or.inr rfl
    · exfalso
      unfold ggMultOrd at hd
      rw [if_neg h1, if_neg h2] at hd
      exact hd rfl

private theorem ggTUClA_sum_eq_finset (m : List ℕ) :
    m.sum = ∑ j ∈ Finset.range m.length, m.getD j 0 := by
  induction m with
  | nil => simp
  | cons x xs ih =>
      rw [List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      omega

private theorem ggTUClA_sum_range_eq_finset : ∀ (H : ℕ) (g : ℕ → ℕ),
    ((List.range H).map g).sum = ∑ j ∈ Finset.range H, g j
  | 0, g => by simp
  | H + 1, g => by
      rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ,
        ggTUClA_sum_range_eq_finset H g]
      simp

private theorem ggTUClA_sum_symm {p H : ℕ} (hp : p = 2 * H + 1) {m : List ℕ}
    (hlen : m.length = p) (hsymm : ∀ j < p, m.getD ((p - j) % p) 0 = m.getD j 0) :
    m.sum = m.getD 0 0 + 2 * ∑ j ∈ Finset.range H, m.getD (j + 1) 0 := by
  rw [ggTUClA_sum_eq_finset m, hlen, hp]
  rw [Finset.sum_range_succ' (fun j => m.getD j 0) (2 * H)]
  have hsplit : ∑ k ∈ Finset.range (2 * H), m.getD (k + 1) 0 =
      ∑ k ∈ Finset.range H, m.getD (k + 1) 0 +
        ∑ k ∈ Finset.range H, m.getD (k + H + 1) 0 := by
    rw [show 2 * H = H + H by omega, Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    omega
  rw [hsplit]
  have hreflect : ∑ k ∈ Finset.range H, m.getD (k + H + 1) 0 =
      ∑ k ∈ Finset.range H, m.getD (k + 1) 0 := by
    have hr := Finset.sum_range_reflect (fun j => m.getD (2 * H - j) 0) H
    have hleft : ∑ j ∈ Finset.range H, (fun j => m.getD (2 * H - j) 0) (H - 1 - j) =
        ∑ j ∈ Finset.range H, m.getD (j + H + 1) 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjH : j < H := Finset.mem_range.mp hj
      simp only
      rw [show 2 * H - (H - 1 - j) = j + H + 1 by omega]
    rw [hleft] at hr
    rw [hr]
    apply Finset.sum_congr rfl
    intro j hj
    have hjH : j < H := Finset.mem_range.mp hj
    have hj1 : j + 1 < p := by omega
    have hmod : (p - (j + 1)) % p = 2 * H - j := by
      rw [hp, show 2 * H + 1 - (j + 1) = 2 * H - j by omega,
        Nat.mod_eq_of_lt (by omega)]
    rw [← hmod]
    exact hsymm (j + 1) hj1
  rw [hreflect]
  omega

private theorem ggTUClA_sum_eq_length_filter_pos {m : List ℕ} (h : ∀ x ∈ m, x ≤ 1) :
    m.sum = (m.filter (fun x => decide (0 < x))).length := by
  induction m with
  | nil => simp
  | cons x xs ih =>
      have hx : x ≤ 1 := h x (by simp)
      have hxs : ∀ y ∈ xs, y ≤ 1 := fun y hy => h y (by simp [hy])
      rw [List.sum_cons, ih hxs]
      have hx01 : x = 0 ∨ x = 1 := by omega
      rcases hx01 with rfl | rfl
      · simp
      · simp [Nat.add_comm]

private theorem ggTUClA_length_filter_ge_two_le {l : List ℕ} :
    (l.filter (fun x => decide (2 ≤ x))).length ≤
      (l.filter (fun x => decide (0 < x))).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      by_cases hx2 : 2 ≤ x
      · have hx0 : 0 < x := by omega
        simp [hx2, hx0]
        omega
      · by_cases hx0 : 0 < x
        · simp [hx2, hx0]
          omega
        · simp [hx2, hx0]
          omega

private theorem ggTUClA_sum_eq_ge_two_add {m : List ℕ}
    (h2 : (m.filter (fun x => decide (2 ≤ x))).length = 1) :
    m.sum = (m.filter (fun x => decide (2 ≤ x))).sum +
      ((m.filter (fun x => decide (0 < x))).length - 1) := by
  induction m with
  | nil => simp at h2
  | cons x xs ih =>
      by_cases hx2 : 2 ≤ x
      · have hx0 : 0 < x := by omega
        have h2xs : (xs.filter (fun y => decide (2 ≤ y))).length = 0 := by
          simpa [hx2, hx0] using h2
        have hnil : xs.filter (fun y => decide (2 ≤ y)) = [] :=
          List.length_eq_zero_iff.mp h2xs
        have hle : ∀ y ∈ xs, y ≤ 1 := by
          intro y hy
          by_contra hy1
          have hy2 : 2 ≤ y := by omega
          have hyin : y ∈ xs.filter (fun y => decide (2 ≤ y)) := by simp [hy2, hy]
          rw [hnil] at hyin
          exact List.not_mem_nil hyin
        have hsum := ggTUClA_sum_eq_length_filter_pos hle
        simp [hx2, hx0, hsum, hnil, List.sum_cons]
      · have h2xs : (xs.filter (fun y => decide (2 ≤ y))).length = 1 := by
          simpa [hx2] using h2
        have ih' := ih h2xs
        have hpos : 1 ≤ (xs.filter (fun y => decide (0 < y))).length := by
          have := ggTUClA_length_filter_ge_two_le (l := xs)
          omega
        have hx01 : x = 0 ∨ x = 1 := by omega
        rcases hx01 with rfl | rfl
        · simpa using ih'
        · have hP1 : ((1 : ℕ) :: xs).filter (fun y => decide (0 < y)) =
              (1 : ℕ) :: xs.filter (fun y => decide (0 < y)) := by simp
          have hP2 : ((1 : ℕ) :: xs).filter (fun y => decide (2 ≤ y)) =
              xs.filter (fun y => decide (2 ≤ y)) := by simp
          rw [List.sum_cons, hP1, hP2, List.length_cons, ih']
          omega

private theorem ggTUClA_filter_map_range {p : ℕ} {m : List ℕ} (hlen : m.length = p)
    (P : ℕ → Prop) [DecidablePred P] :
    ((List.range p).filter (fun j => decide (P (m.getD j 0)))).map (fun j => m.getD j 0) =
      m.filter (fun x => decide (P x)) := by
  have hm : m = (List.range p).map (fun j => m.getD j 0) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2
      rw [List.getElem_map, List.getElem_range]
      exact (List.getD_eq_getElem (l := m) (d := 0) (n := i) h1).symm
  conv_rhs => rw [hm]
  rw [List.filter_map]
  rfl

private theorem ggTUClA_sum_range_succ_eq_filter : ∀ (H : ℕ) (f : ℕ → ℕ),
    ((List.range H).map (fun i => f (i + 1))).sum =
      (((List.range (H + 1)).filter (fun j => decide (1 ≤ j ∧ 0 < f j))).map f).sum
  | 0, f => by simp
  | H + 1, f => by
      have h1 : ((List.range (H + 1)).map (fun i => f (i + 1))).sum =
          ((List.range H).map (fun i => f (i + 1))).sum + f (H + 1) := by
        rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
          List.sum_singleton]
      have h2 : (((List.range (H + 1 + 1)).filter
            (fun j => decide (1 ≤ j ∧ 0 < f j))).map f).sum =
          ((((List.range (H + 1)).filter (fun j => decide (1 ≤ j ∧ 0 < f j))).map f).sum) +
            f (H + 1) := by
        rw [show H + 1 + 1 = (H + 1) + 1 by omega, List.range_succ, List.filter_append,
          List.map_append, List.sum_append]
        rw [show (List.filter (fun j => decide (1 ≤ j ∧ 0 < f j)) [H + 1]) =
            if 0 < f (H + 1) then [H + 1] else [] by
          rw [List.filter_singleton]
          simp [show 1 ≤ H + 1 by omega]]
        split_ifs with hf
        · simp
        · have hf0 : f (H + 1) = 0 := by omega
          simp [hf0]
      rw [h1, h2, ggTUClA_sum_range_succ_eq_filter H f]

private theorem ggTUClA_length_filter_le_of_imp {l : List ℕ} {P Q : ℕ → Prop}
    [DecidablePred P] [DecidablePred Q] (h : ∀ x, P x → Q x) :
    (l.filter (fun x => decide (P x))).length ≤
      (l.filter (fun x => decide (Q x))).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      by_cases hpx : P x
      · have hqx : Q x := h x hpx
        simp [hpx, hqx]
        omega
      · by_cases hqx : Q x <;> simp [hpx, hqx] <;> omega

private theorem ggTUClA_dvd_two_pow_two_mul_sub_one_of_add {p n : ℕ}
    (h : p ∣ 2 ^ n + 1) : p ∣ 2 ^ (2 * n) - 1 := by
  have hpow : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by
    rw [show 2 * n = n * 2 by omega, pow_mul]
  have hfac : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    rw [hpow]
    simpa using Nat.sq_sub_sq (2 ^ n) 1
  rw [hfac]
  exact dvd_mul_of_dvd_left h _

private theorem ggTUClA_row_A_succ {p n k r : ℕ} (hp : p ∣ 2 ^ n - 1) (hk : 2 ≤ k)
    (hr : r = k + 1) : GGTablePRow p ⟨.A, k, n⟩ ⟨.A, r, n⟩ := by
  subst hr
  refine Or.inl ⟨rfl, hp, hk, Or.inl rfl⟩

private theorem ggTUClA_row_A_add_two {p n k r : ℕ} (hp : p ∣ 2 ^ n + 1) (hk : 3 ≤ k)
    (hr : r = k + 2) : GGTablePRow p ⟨.A, k, n⟩ ⟨.A, r, n⟩ := by
  subst hr
  refine Or.inr (Or.inl ⟨rfl, hp, hk, Or.inl rfl⟩)

private theorem ggTUClA_row_twA_succ {p n k r : ℕ} (hp : p ∣ 2 ^ n + 1) (hk : 2 ≤ k)
    (hr : r = k + 1) : GGTablePRow p ⟨.twA, k, n⟩ ⟨.twA, r, n⟩ := by
  subst hr
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨rfl, hp, hk, Or.inl rfl⟩)))))))

private theorem ggTUClA_row_twA_add_two {p n k r : ℕ} (hp : p ∣ 2 ^ n - 1) (hk : 3 ≤ k)
    (hr : r = k + 2) : GGTablePRow p ⟨.twA, k, n⟩ ⟨.twA, r, n⟩ := by
  subst hr
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨rfl, hp, hk, Or.inl rfl⟩))))))

private theorem ggTUClA_row_A_double {p n k r : ℕ} (hp : p ∣ 2 ^ (2 * n) - 1) (hk : 2 ≤ k)
    (hr : r = 2 * k + 1 ∨ r = 2 * k + 2) (hpq : p ∣ 2 ^ n + 1) :
    GGTablePRow p ⟨.A, k, 2 * n⟩ ⟨.A, r, n⟩ := by
  refine Or.inl ⟨rfl, hp, hk, ?_⟩
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨rfl, hr, rfl, hpq⟩)))))))))

private theorem ggTUClA_row_A_two_field {p n : ℕ} (hp : p ∣ 2 ^ (2 * n) - 1)
    (hp' : p ∣ 2 ^ n - 1) : GGTablePRow p ⟨.A, 2, 2 * n⟩ ⟨.twA, 5, n⟩ := by
  refine Or.inl ⟨rfl, hp, by norm_num, ?_⟩
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨rfl, rfl, rfl, rfl, hp'⟩)))))))))

private theorem ggTUClA_lambda2_A {k n : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hk1 : k = 1 → 2 ≤ n) : LargeEvenInLambda2 ⟨.A, k, n⟩ := by
  unfold LargeEvenInLambda2
  exact ⟨hn, hk, hk1⟩

private theorem ggTUClA_lambda2_twA {k n : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hk2 : k = 2 → 2 ≤ n) : LargeEvenInLambda2 ⟨.twA, k, n⟩ := by
  unfold LargeEvenInLambda2
  exact ⟨hn, hk, hk2⟩

private theorem ggTUClA_dvd_two_pow_two_mul_sub_one {p n : ℕ} (h : p ∣ 2 ^ n - 1) :
    p ∣ 2 ^ (2 * n) - 1 := by
  have h1 : 2 ^ n - 1 ∣ 2 ^ (2 * n) - 1 := by
    simpa using Nat.pow_sub_pow_dvd_pow_sub_pow (x := 2) (y := 1) (m := n) (k := 2 * n)
      ⟨2, by omega⟩
  exact dvd_trans h h1

private theorem ggTUClA_blockA_lab_one {k n : ℕ} :
    (ggMultBlockA k n 1).lab = ⟨.A, k, n⟩ := by
  simp [ggMultBlockA]

private theorem ggTUClA_blockA_lab_two {k n : ℕ} (hk : 2 ≤ k) :
    (ggMultBlockA k n 2).lab = ⟨.twA, k, n⟩ := by
  simp [ggMultBlockA, hk]

private theorem ggTUClA_blockA_lab_two_small {k n : ℕ} (hk : ¬ 2 ≤ k) :
    (ggMultBlockA k n 2).lab = ⟨.A, 1, n⟩ := by
  simp [ggMultBlockA, hk]

private theorem ggTUClA_qs_two {k n : ℕ} (h : (ggMultBlockA k n 2).qs = true) (hk : k = 2) :
    n ≠ 1 := by
  rintro rfl
  simp [ggMultBlockA, hk] at h

private theorem ggTUClA_trivial_setup {r p n : ℕ} {tw : Bool} {D : GGKacDatum}
    (hD : D ∈ ggMultTableCl (.A r) tw p n) (hrZ : D.rZ ≤ 1) {o : GGKacOrbit}
    (hDo : D.orbits = [o]) (hqs : o.qs = true)
    (htriv : (tw = false ∧ ggMultOrd p n = 1) ∨ (tw = true ∧ ggMultOrd p n = 2)) :
    ∃ a b : ℕ, 2 ≤ a ∧ b ≤ 1 ∧ r + 1 = a + b ∧
      o = ggMultBlockA (a - 1) n (ggMultOrd p n) ∧
      (ggMultBlockA (a - 1) n (ggMultOrd p n)).qs = true := by
  have hd := ggMultOrd_ne_zero_of_mem_ggMultTableCl hD
  obtain ⟨m, hmlen, hmsum, hQ, hDeq⟩ := (mem_ggMultTableCl_A hd).mp hD
  subst hDeq
  simp only [ggMultDatumA] at hDo hrZ ⊢
  rw [if_pos htriv] at hDo hrZ
  dsimp only at hDo hrZ
  obtain ⟨j₀, hS, ho⟩ := List.map_eq_singleton_iff.mp hDo
  have hj₀mem : j₀ ∈ (List.range p).filter (fun j => decide (2 ≤ m.getD j 0)) := by
    rw [hS]
    exact List.mem_singleton_self j₀
  have hj₀2 : 2 ≤ m.getD j₀ 0 := by
    have := (List.mem_filter.mp hj₀mem).2
    simpa using this
  have hfilter2 : m.filter (fun x => decide (2 ≤ x)) = [m.getD j₀ 0] := by
    rw [← ggTUClA_filter_map_range (P := fun x => 2 ≤ x) hmlen, hS]
    simp
  have hfilterlen : (m.filter (fun x => decide (2 ≤ x))).length = 1 := by
    rw [hfilter2]
    simp
  have hsum1 : m.sum = m.getD j₀ 0 +
      ((m.filter (fun x => decide (0 < x))).length - 1) := by
    have := ggTUClA_sum_eq_ge_two_add hfilterlen
    rwa [hfilter2] at this
  have hposmap := ggTUClA_filter_map_range (m := m) (p := p) hmlen (P := fun x => 0 < x)
  have hposlen : (m.filter (fun x => decide (0 < x))).length ≤ 2 := by
    have hlen := congrArg List.length hposmap
    simp only [List.length_map] at hlen
    omega
  have hoa : o = ggMultBlockA (m.getD j₀ 0 - 1) n (ggMultOrd p n) := ho.symm
  have hqs' : (ggMultBlockA (m.getD j₀ 0 - 1) n (ggMultOrd p n)).qs = true := by
    rw [hoa] at hqs
    exact hqs
  exact ⟨m.getD j₀ 0, (m.filter (fun x => decide (0 < x))).length - 1, hj₀2,
    by omega, by omega, hoa, hqs'⟩

private theorem ggTUClA_trivial_single_A {r p n a b : ℕ} {o : GGKacOrbit}
    (hb : b = 0) (hsum : r + 1 = a + b) (ho : o = ggMultBlockA (a - 1) n 1)
    (hX : o.lab ≠ ⟨.A, r, n⟩) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨.A, r, n⟩ := by
  have ha : a = r + 1 := by omega
  have ho_lab : o.lab = ⟨.A, r, n⟩ := by
    rw [ho, ggTUClA_blockA_lab_one, ha]
    simp only [Nat.add_sub_cancel]
  exact (hX ho_lab).elim

private theorem ggTUClA_trivial_single_twA {r p n a b : ℕ} {o : GGKacOrbit}
    (h2a : 2 ≤ a) (hb : b = 0) (hsum : r + 1 = a + b)
    (ho : o = ggMultBlockA (a - 1) n 2)
    (hX : o.lab ≠ ⟨.twA, r, n⟩) (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨.twA, r, n⟩ := by
  have ha : a = r + 1 := by omega
  by_cases hr2 : 2 ≤ r
  · have ho_lab : o.lab = ⟨.twA, r, n⟩ := by
      rw [ho, show a - 1 = r by omega]
      exact ggTUClA_blockA_lab_two hr2
    exact (hX ho_lab).elim
  · have hr1 : r = 1 := by omega
    exfalso
    apply hrk
    rw [ho, show a - 1 = 1 by omega]
    exact Or.inl (by simp [ggMultBlockA])

private theorem ggTUClA_trivial_double_A {r p n a b : ℕ} {o : GGKacOrbit} (hn : 1 ≤ n)
    (hd1 : ggMultOrd p n = 1) (h2a : 2 ≤ a) (hb : b = 1) (hsum : r + 1 = a + b)
    (ho : o = ggMultBlockA (a - 1) n 1) (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨.A, r, n⟩ := by
  have ha : a = r := by omega
  have hr2 : 2 ≤ r := by omega
  by_cases hk2 : 2 ≤ r - 1
  · have ho_lab : o.lab = ⟨.A, r - 1, n⟩ := by
      rw [ho, ggTUClA_blockA_lab_one, ha]
    rw [ho_lab]
    exact ⟨ggTUClA_lambda2_A hn (by omega) (by omega),
      ggTUClA_row_A_succ (ggTUClA_dvd_of_ord_eq_one hd1) hk2 (by omega)⟩
  · exfalso
    apply hrk
    rw [ho, show a - 1 = 1 by omega]
    exact Or.inl (by simp [ggMultBlockA])

private theorem ggTUClA_trivial_double_twA {r p n a b : ℕ} {o : GGKacOrbit} (hn : 1 ≤ n)
    (hd2 : ggMultOrd p n = 2) (h2a : 2 ≤ a) (hb : b = 1) (hsum : r + 1 = a + b)
    (ho : o = ggMultBlockA (a - 1) n 2)
    (hqs : (ggMultBlockA (a - 1) n 2).qs = true) (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨.twA, r, n⟩ := by
  have ha : a = r := by omega
  have hr2 : 2 ≤ r := by omega
  by_cases hk2 : 2 ≤ r - 1
  · have ho_lab : o.lab = ⟨.twA, r - 1, n⟩ := by
      rw [ho, show a - 1 = r - 1 by omega]
      exact ggTUClA_blockA_lab_two hk2
    rw [ho_lab]
    refine ⟨ggTUClA_lambda2_twA hn hk2 ?_, ?_⟩
    · intro hk
      have ha2 : a - 1 = 2 := by omega
      have hqs2 : (ggMultBlockA 2 n 2).qs = true := by
        have h' : (ggMultBlockA (a - 1) n 2).qs = true := hqs
        rwa [ha2] at h'
      have hne := ggTUClA_qs_two hqs2 rfl
      omega
    · exact ggTUClA_row_twA_succ (ggTUClA_dvd_of_ord_eq_two hd2) hk2 (by omega)
  · exfalso
    apply hrk
    rw [ho, show a - 1 = 1 by omega]
    exact Or.inl (by simp [ggMultBlockA])

private theorem ggTUClA_trivial {r p n : ℕ} {tw : Bool} {D : GGKacDatum} (hn : 1 ≤ n)
    (hD : D ∈ ggMultTableCl (.A r) tw p n) (hrZ : D.rZ ≤ 1) {o : GGKacOrbit}
    (hDo : D.orbits = [o]) (hqs : o.qs = true)
    (hX : o.lab ≠ ⟨if tw then .twA else .A, r, n⟩)
    (hrk : ¬ GGTPNPRankOne p o.lab)
    (htriv : (tw = false ∧ ggMultOrd p n = 1) ∨ (tw = true ∧ ggMultOrd p n = 2)) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨if tw then .twA else .A, r, n⟩ := by
  obtain ⟨a, b, h2a, hb, hsum, ho, hqsb⟩ := ggTUClA_trivial_setup hD hrZ hDo hqs htriv
  have hb01 : b = 0 ∨ b = 1 := by omega
  rcases htriv with ⟨htw, hd1⟩ | ⟨htw, hd2⟩
  · subst htw
    rw [hd1] at ho hqsb
    rcases hb01 with hb0 | hb1
    · exact ggTUClA_trivial_single_A hb0 hsum ho hX
    · exact ggTUClA_trivial_double_A hn hd1 h2a hb1 hsum ho hrk
  · subst htw
    rw [hd2] at ho hqsb
    rcases hb01 with hb0 | hb1
    · exact ggTUClA_trivial_single_twA h2a hb0 hsum ho hX hrk
    · exact ggTUClA_trivial_double_twA hn hd2 h2a hb1 hsum ho hqsb hrk
private theorem ggTUClA_sum_symm_list {p H : ℕ} (hp : p = 2 * H + 1) {m : List ℕ}
    (hlen : m.length = p) (hsymm : ∀ j < p, m.getD ((p - j) % p) 0 = m.getD j 0) :
    m.sum = m.headD 0 + 2 * ((List.range H).map (fun i => m.getD (i + 1) 0)).sum := by
  rw [ggTUClA_sum_symm hp hlen hsymm, ← List.headD_eq_getD,
    ← ggTUClA_sum_range_eq_finset H (fun j => m.getD (j + 1) 0)]

private def ggTUClAOrb0 (n : ℕ) (tw : Bool) (m0 : ℕ) : List GGKacOrbit :=
  if 2 ≤ m0 then
    (if tw = false then
      [⟨⟨.A, m0 - 1, n⟩, decide (¬(m0 - 1 = 1 ∧ n = 1))⟩]
    else [ggMultBlockA (m0 - 1) n 2])
  else []

private def ggTUClAReflData (r p n : ℕ) (tw : Bool) (m : List ℕ) (H : ℕ) (T U : List ℕ)
    (o : GGKacOrbit) : Prop :=
  T.length ≤ 1 ∧ m.length = p ∧ m.sum = r + 1 ∧
    (∀ j < p, m.getD ((p - j) % p) 0 = m.getD j 0) ∧ ggMultOrd p n ≠ 0 ∧
    p = 2 * H + 1 ∧
    T = (List.range (H + 1)).filter (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0)) ∧
    U = (List.range (H + 1)).filter (fun j => decide (1 ≤ j ∧ 2 ≤ m.getD j 0)) ∧
    m.sum = m.headD 0 + 2 * (T.map (fun j => m.getD j 0)).sum ∧
    ggTUClAOrb0 n tw (m.headD 0) ++
      (U.map (fun j => (⟨⟨.A, m.getD j 0 - 1, 2 * n⟩, true⟩ : GGKacOrbit))) = [o]

private theorem ggTUClA_reflection_setup {r p n : ℕ} {tw : Bool} {D : GGKacDatum}
    (hn : 1 ≤ n) (hD : D ∈ ggMultTableCl (.A r) tw p n) (hrZ : D.rZ ≤ 1)
    {o : GGKacOrbit} (hDo : D.orbits = [o])
    (htriv : ¬ ((tw = false ∧ ggMultOrd p n = 1) ∨ (tw = true ∧ ggMultOrd p n = 2))) :
    ∃ (m : List ℕ) (H : ℕ) (T U : List ℕ), ggTUClAReflData r p n tw m H T U o := by
  have hd := ggMultOrd_ne_zero_of_mem_ggMultTableCl hD
  obtain ⟨m, hmlen, hmsum, hQ, hDeq⟩ := (mem_ggMultTableCl_A hd).mp hD
  subst hDeq
  simp only [ggMultDatumA] at hDo hrZ ⊢
  have hodd : Odd p := ggTUClA_odd hn hd
  have hsymm : ∀ j < p, m.getD ((p - j) % p) 0 = m.getD j 0 := by
    rcases hQ with h | h | h
    · exact absurd (Or.inl h) htriv
    · exact absurd (Or.inr h) htriv
    · exact h
  set H := (p - 1) / 2 with hH
  have hp_eq : p = 2 * H + 1 := by
    rw [hH]
    exact (ggTUClA_two_mul_half_add_one hodd).symm
  rw [if_neg htriv] at hDo hrZ
  dsimp only at hDo hrZ
  set T := (List.range (H + 1)).filter (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0)) with hT
  set U := (List.range (H + 1)).filter (fun j => decide (1 ≤ j ∧ 2 ≤ m.getD j 0)) with hU
  have hsum : m.sum = m.headD 0 + 2 * (T.map (fun j => m.getD j 0)).sum := by
    rw [ggTUClA_sum_symm_list hp_eq hmlen hsymm,
      ggTUClA_sum_range_succ_eq_filter H (fun j => m.getD j 0), ← hT]
  exact ⟨m, H, T, U, hrZ, hmlen, hmsum, hsymm, hd, hp_eq, hT, hU, hsum, hDo⟩

private def ggTUClAEmptyData (r n : ℕ) (tw : Bool) (m : List ℕ) (o : GGKacOrbit) : Prop :=
  ggTUClAOrb0 n tw (m.headD 0) = [o] ∧ 2 ≤ m.headD 0 ∧ m.headD 0 = r + 1

private theorem ggTUClA_empty_data {r p n : ℕ} {tw : Bool} {m : List ℕ} {H : ℕ}
    {T U : List ℕ} {o : GGKacOrbit} (hdata : ggTUClAReflData r p n tw m H T U o)
    (hTnil : T = []) : ggTUClAEmptyData r n tw m o := by
  obtain ⟨hTle, hmlen, hmsum, hsymm, hd, hp_eq, hT, hU, hsum, hDoT⟩ := hdata
  have hUnil : U = [] := by
    apply List.length_eq_zero_iff.mp
    have h := ggTUClA_length_filter_le_of_imp (l := List.range (H + 1))
      (P := fun j => 1 ≤ j ∧ 2 ≤ m.getD j 0) (Q := fun j => 1 ≤ j ∧ 0 < m.getD j 0)
      (fun x hx => by omega)
    rw [← hU, ← hT, hTnil] at h
    simpa using h
  have horb0 : ggTUClAOrb0 n tw (m.headD 0) = [o] := by
    rw [hUnil] at hDoT
    simpa using hDoT
  have hm0ge : 2 ≤ m.headD 0 := by
    by_contra hlt
    have hnil : ggTUClAOrb0 n tw (m.headD 0) = [] := by
      unfold ggTUClAOrb0
      rw [if_neg hlt]
    rw [hnil] at horb0
    simp at horb0
  have hm0eq : m.headD 0 = r + 1 := by
    have h0 : (T.map (fun j => m.getD j 0)).sum = 0 := by rw [hTnil]; simp
    have h1 : m.sum = m.headD 0 := by rw [hsum, h0]; omega
    omega
  exact ⟨horb0, hm0ge, hm0eq⟩

private theorem ggTUClA_reflection_empty_A {r p n : ℕ} {tw : Bool} {m : List ℕ}
    {o : GGKacOrbit} (h : ggTUClAEmptyData r n tw m o) (htw : tw = false)
    (hX : o.lab ≠ ⟨.A, r, n⟩) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨.A, r, n⟩ := by
  obtain ⟨horb0, hm0ge, hm0eq⟩ := h
  subst htw
  have hoA : o = ⟨⟨.A, m.headD 0 - 1, n⟩,
      decide (¬(m.headD 0 - 1 = 1 ∧ n = 1))⟩ := by
    have h' := horb0
    unfold ggTUClAOrb0 at h'
    rw [if_pos hm0ge, if_pos rfl] at h'
    exact (List.singleton_inj.mp h').symm
  have holab : o.lab = ⟨.A, r, n⟩ := by
    rw [hoA, show m.headD 0 - 1 = r by omega]
  exact (hX holab).elim

private theorem ggTUClA_reflection_empty_twA {r p n : ℕ} {tw : Bool} {m : List ℕ}
    {o : GGKacOrbit} (h : ggTUClAEmptyData r n tw m o) (htw : tw = true)
    (hX : o.lab ≠ ⟨.twA, r, n⟩)
    (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨.twA, r, n⟩ := by
  obtain ⟨horb0, hm0ge, hm0eq⟩ := h
  subst htw
  have hoA : o = ggMultBlockA (m.headD 0 - 1) n 2 := by
    have h' := horb0
    unfold ggTUClAOrb0 at h'
    rw [if_pos hm0ge, if_neg (by simp)] at h'
    exact (List.singleton_inj.mp h').symm
  by_cases hr1 : r = 1
  · exfalso
    apply hrk
    rw [hoA, show m.headD 0 - 1 = 1 by omega]
    exact Or.inl (by
      rw [ggTUClA_blockA_lab_two_small (by norm_num : ¬ 2 ≤ 1)]
      exact ⟨rfl, rfl⟩)
  · have hr2 : 2 ≤ r := by omega
    have holab : o.lab = ⟨.twA, r, n⟩ := by
      rw [hoA, show m.headD 0 - 1 = r by omega]
      exact ggTUClA_blockA_lab_two hr2
    exact (hX holab).elim

private theorem ggTUClA_reflection_empty {r p n : ℕ} {tw : Bool} {m : List ℕ} {H : ℕ}
    {T U : List ℕ} {o : GGKacOrbit}
    (htriv : ¬ ((tw = false ∧ ggMultOrd p n = 1) ∨ (tw = true ∧ ggMultOrd p n = 2)))
    (hdata : ggTUClAReflData r p n tw m H T U o) (hTnil : T = [])
    (hX : o.lab ≠ ⟨if tw then .twA else .A, r, n⟩)
    (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨if tw then .twA else .A, r, n⟩ := by
  have h := ggTUClA_empty_data hdata hTnil
  obtain ⟨hTle, hmlen, hmsum, hsymm, hd, hp_eq, hT, hU, hsum, hDoT⟩ := hdata
  by_cases htw : tw = false
  · subst htw
    exact ggTUClA_reflection_empty_A h rfl hX
  · have htw' : tw = true := Bool.of_not_eq_false htw
    subst htw'
    exact ggTUClA_reflection_empty_twA h rfl hX hrk

private def ggTUClAOneData (r n : ℕ) (tw : Bool) (m : List ℕ) (o : GGKacOrbit) : Prop :=
  2 ≤ m.headD 0 ∧ m.headD 0 = r - 1 ∧ ggTUClAOrb0 n tw (m.headD 0) = [o]

private def ggTUClATwoData (r n : ℕ) (m : List ℕ) (j₀ : ℕ) (o : GGKacOrbit) : Prop :=
  2 ≤ m.getD j₀ 0 ∧ m.headD 0 ≤ 1 ∧
    r + 1 = m.headD 0 + 2 * m.getD j₀ 0 ∧
    o = ⟨⟨.A, m.getD j₀ 0 - 1, 2 * n⟩, true⟩

private theorem ggTUClA_reflection_one_A {r p n : ℕ} {m : List ℕ} {o : GGKacOrbit}
    (hn : 1 ≤ n) (hd2 : ggMultOrd p n = 2)
    (ho : o = ⟨⟨.A, m.headD 0 - 1, n⟩, decide (¬(m.headD 0 - 1 = 1 ∧ n = 1))⟩)
    (hm0 : m.headD 0 = r - 1) (h2m0 : 2 ≤ m.headD 0) (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨.A, r, n⟩ := by
  have hlab : o.lab = ⟨.A, r - 2, n⟩ := by
    rw [ho, show m.headD 0 - 1 = r - 2 by omega]
  have hpq := ggTUClA_dvd_of_ord_eq_two hd2
  rcases lt_or_ge r 4 with hr4 | hr4
  · have hk : r - 2 = 1 := by omega
    exact (hrk (by rw [hlab, hk]; exact Or.inl ⟨rfl, rfl⟩)).elim
  rcases lt_or_ge r 5 with hr5 | hr5
  · have hk : r - 2 = 2 := by omega
    exact (hrk (by
      rw [hlab, hk]
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hpq⟩)))).elim
  · have hk3 : 3 ≤ r - 2 := by omega
    rw [hlab]
    exact ⟨ggTUClA_lambda2_A hn (by omega) (by omega),
      ggTUClA_row_A_add_two hpq hk3 (by omega)⟩

private theorem ggTUClA_reflection_one_twA {r p n : ℕ} {m : List ℕ} {o : GGKacOrbit}
    (hn : 1 ≤ n) (hd1 : ggMultOrd p n = 1)
    (ho : o = ggMultBlockA (m.headD 0 - 1) n 2)
    (hm0 : m.headD 0 = r - 1) (h2m0 : 2 ≤ m.headD 0) (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨.twA, r, n⟩ := by
  have hpq := ggTUClA_dvd_of_ord_eq_one hd1
  rcases lt_or_ge r 4 with hr4 | hr4
  · exact (hrk (by
      rw [ho, show m.headD 0 - 1 = 1 by omega]
      exact Or.inl (by
        rw [ggTUClA_blockA_lab_two_small (by norm_num : ¬ 2 ≤ 1)]
        exact ⟨rfl, rfl⟩))).elim
  rcases lt_or_ge r 5 with hr5 | hr5
  · have hk : m.headD 0 - 1 = 2 := by omega
    have hlab : o.lab = ⟨.twA, 2, n⟩ := by
      rw [ho, hk]
      exact ggTUClA_blockA_lab_two (by norm_num)
    exact (hrk (by
      rw [hlab]
      exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hpq⟩)))).elim
  · have hk3 : 3 ≤ r - 2 := by omega
    have hlab : o.lab = ⟨.twA, r - 2, n⟩ := by
      rw [ho, show m.headD 0 - 1 = r - 2 by omega]
      exact ggTUClA_blockA_lab_two (by omega)
    rw [hlab]
    exact ⟨ggTUClA_lambda2_twA hn (by omega) (by omega),
      ggTUClA_row_twA_add_two hpq hk3 (by omega)⟩

private theorem ggTUClA_reflection_two_A {r p n : ℕ} {m : List ℕ} {j₀ : ℕ} {o : GGKacOrbit}
    (hn : 1 ≤ n) (hd2 : ggMultOrd p n = 2) (htwo : ggTUClATwoData r n m j₀ o)
    (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨.A, r, n⟩ := by
  obtain ⟨ha2, hm0le, hsum, ho⟩ := htwo
  have hlab : o.lab = ⟨.A, m.getD j₀ 0 - 1, 2 * n⟩ := by rw [ho]
  rcases lt_or_ge (m.getD j₀ 0) 3 with ha3 | ha3
  · have haeq : m.getD j₀ 0 = 2 := by omega
    exact (hrk (by rw [ho, haeq]; exact Or.inl ⟨rfl, rfl⟩)).elim
  · have hpq := ggTUClA_dvd_of_ord_eq_two hd2
    have hpd := ggTUClA_dvd_two_pow_two_mul_sub_one_of_add hpq
    rw [hlab]
    exact ⟨ggTUClA_lambda2_A (by omega) (by omega) (by omega),
      ggTUClA_row_A_double hpd (by omega) (by omega) hpq⟩

private theorem ggTUClA_reflection_two_twA {r p n : ℕ} {m : List ℕ} {j₀ : ℕ}
    {o : GGKacOrbit} (hn : 1 ≤ n)
    (hT5 : p ∣ 2 ^ n - 1 → ¬ p ∣ 2 ^ n + 1 → r = 3 ∨ r = 5)
    (hd1 : ggMultOrd p n = 1) (h3p : 3 ≤ p) (htwo : ggTUClATwoData r n m j₀ o)
    (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨.twA, r, n⟩ := by
  obtain ⟨ha2, hm0le, hsum, ho⟩ := htwo
  have hpq := ggTUClA_dvd_of_ord_eq_one hd1
  have hnot : ¬ p ∣ 2 ^ n + 1 := by
    intro hboth
    have h2 : p ∣ 2 := by
      have hsub : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hboth hpq
      have heq : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
        have := Nat.one_le_two_pow (n := n)
        omega
      rwa [heq] at hsub
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  rcases lt_or_ge (m.getD j₀ 0) 3 with ha3 | ha3
  · have haeq : m.getD j₀ 0 = 2 := by omega
    exact (hrk (by rw [ho, haeq]; exact Or.inl ⟨rfl, rfl⟩)).elim
  · rcases hT5 hpq hnot with hr3 | hr5
    · omega
    · have haeq : m.getD j₀ 0 = 3 := by omega
      have hlab : o.lab = ⟨.A, 2, 2 * n⟩ := by rw [ho, haeq]
      have hpd := ggTUClA_dvd_two_pow_two_mul_sub_one hpq
      rw [hlab]
      exact ⟨ggTUClA_lambda2_A (by omega) (by norm_num) (by omega),
        by simpa [hr5] using ggTUClA_row_A_two_field hpd hpq⟩

private theorem ggTUClA_reflection_one {r p n : ℕ} {tw : Bool} {m : List ℕ} {o : GGKacOrbit}
    (hn : 1 ≤ n) (hone : ggTUClAOneData r n tw m o) (hd : ggMultOrd p n ≠ 0)
    (htriv : ¬ ((tw = false ∧ ggMultOrd p n = 1) ∨ (tw = true ∧ ggMultOrd p n = 2)))
    (hX : o.lab ≠ ⟨if tw then .twA else .A, r, n⟩)
    (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨if tw then .twA else .A, r, n⟩ := by
  obtain ⟨h2m0, hm0eq, horb0⟩ := hone
  by_cases htw : tw = false
  · subst htw
    have hd2 : ggMultOrd p n = 2 := by
      rcases ggTUClA_ord_eq_one_or_two hd with h | h
      · exact absurd (Or.inl ⟨rfl, h⟩) htriv
      · exact h
    have hoA : o = ⟨⟨.A, m.headD 0 - 1, n⟩,
        decide (¬(m.headD 0 - 1 = 1 ∧ n = 1))⟩ := by
      have h' := horb0
      unfold ggTUClAOrb0 at h'
      rw [if_pos h2m0, if_pos rfl] at h'
      exact (List.singleton_inj.mp h').symm
    exact ggTUClA_reflection_one_A hn hd2 hoA hm0eq h2m0 hrk
  · have htw' : tw = true := Bool.of_not_eq_false htw
    have hd1 : ggMultOrd p n = 1 := by
      rcases ggTUClA_ord_eq_one_or_two hd with h | h
      · exact h
      · exact absurd (Or.inr ⟨htw', h⟩) htriv
    have hoA : o = ggMultBlockA (m.headD 0 - 1) n 2 := by
      have h' := horb0
      unfold ggTUClAOrb0 at h'
      rw [if_pos h2m0, if_neg (by simp [htw'])] at h'
      exact (List.singleton_inj.mp h').symm
    subst htw'
    exact ggTUClA_reflection_one_twA hn hd1 hoA hm0eq h2m0 hrk

private theorem ggTUClA_reflection_two {r p n : ℕ} {tw : Bool} {m : List ℕ} {j₀ : ℕ}
    {o : GGKacOrbit} (hn : 1 ≤ n)
    (hT5 : tw = true → p ∣ 2 ^ n - 1 → ¬ p ∣ 2 ^ n + 1 → r = 3 ∨ r = 5)
    (htwo : ggTUClATwoData r n m j₀ o) (hd : ggMultOrd p n ≠ 0) (h3p : 3 ≤ p)
    (htriv : ¬ ((tw = false ∧ ggMultOrd p n = 1) ∨ (tw = true ∧ ggMultOrd p n = 2)))
    (hX : o.lab ≠ ⟨if tw then .twA else .A, r, n⟩)
    (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨if tw then .twA else .A, r, n⟩ := by
  by_cases htw : tw = false
  · subst htw
    have hd2 : ggMultOrd p n = 2 := by
      rcases ggTUClA_ord_eq_one_or_two hd with h | h
      · exact absurd (Or.inl ⟨rfl, h⟩) htriv
      · exact h
    exact ggTUClA_reflection_two_A hn hd2 htwo hrk
  · have htw' : tw = true := Bool.of_not_eq_false htw
    have hd1 : ggMultOrd p n = 1 := by
      rcases ggTUClA_ord_eq_one_or_two hd with h | h
      · exact h
      · exact absurd (Or.inr ⟨htw', h⟩) htriv
    subst htw'
    exact ggTUClA_reflection_two_twA hn (hT5 rfl) hd1 h3p htwo hrk

private theorem ggTUClA_reflection_pos_one {r p n : ℕ} {tw : Bool} {m : List ℕ} {H : ℕ}
    {T U : List ℕ} {o : GGKacOrbit} (hn : 1 ≤ n)
    (htriv : ¬ ((tw = false ∧ ggMultOrd p n = 1) ∨ (tw = true ∧ ggMultOrd p n = 2)))
    (hdata : ggTUClAReflData r p n tw m H T U o) (j₀ : ℕ) (hTj : T = [j₀]) (hUnil : U = [])
    (hX : o.lab ≠ ⟨if tw then .twA else .A, r, n⟩)
    (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨if tw then .twA else .A, r, n⟩ := by
  obtain ⟨hTle, hmlen, hmsum, hsymm, hd, hp_eq, hT, hU, hsum, hDoT⟩ := hdata
  have hj₀mem : j₀ ∈ T := by rw [hTj]; exact List.mem_singleton_self j₀
  have hj₀le : j₀ ≤ H := by
    have h := List.mem_range.mp (List.mem_of_mem_filter (by rwa [hT] at hj₀mem))
    omega
  have hj₀cond : 1 ≤ j₀ ∧ 0 < m.getD j₀ 0 := by
    rw [hT] at hj₀mem
    have := (List.mem_filter.mp hj₀mem).2
    simpa using this
  have hTmap : (T.map (fun j => m.getD j 0)).sum = m.getD j₀ 0 := by rw [hTj]; simp
  have hsumj : m.sum = m.headD 0 + 2 * m.getD j₀ 0 := by rw [hsum, hTmap]
  have ha1 : m.getD j₀ 0 = 1 := by
    by_contra hne
    have h2 : 2 ≤ m.getD j₀ 0 := by omega
    have hmemU : j₀ ∈ U := by
      rw [hU]
      exact List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), by
        simp only [decide_eq_true_eq]
        exact ⟨hj₀cond.1, h2⟩⟩
    rw [hUnil] at hmemU
    exact List.not_mem_nil hmemU
  have hm0eq : m.headD 0 = r - 1 := by omega
  have horb0 : ggTUClAOrb0 n tw (m.headD 0) = [o] := by
    rw [hUnil] at hDoT
    simpa using hDoT
  have hm0ge : 2 ≤ m.headD 0 := by
    by_contra hlt
    have hnil : ggTUClAOrb0 n tw (m.headD 0) = [] := by
      unfold ggTUClAOrb0
      rw [if_neg hlt]
    rw [hnil] at horb0
    simp at horb0
  exact ggTUClA_reflection_one hn ⟨hm0ge, hm0eq, horb0⟩ hd htriv hX hrk

private theorem ggTUClA_reflection_pos_two {r p n : ℕ} {tw : Bool} {m : List ℕ} {H : ℕ}
    {T U : List ℕ} {o : GGKacOrbit} (hn : 1 ≤ n)
    (hT5 : tw = true → p ∣ 2 ^ n - 1 → ¬ p ∣ 2 ^ n + 1 → r = 3 ∨ r = 5)
    (htriv : ¬ ((tw = false ∧ ggMultOrd p n = 1) ∨ (tw = true ∧ ggMultOrd p n = 2)))
    (hdata : ggTUClAReflData r p n tw m H T U o) (j₀ : ℕ) (hTj : T = [j₀])
    (hUj : U = [j₀]) (hX : o.lab ≠ ⟨if tw then .twA else .A, r, n⟩)
    (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨if tw then .twA else .A, r, n⟩ := by
  obtain ⟨hTle, hmlen, hmsum, hsymm, hd, hp_eq, hT, hU, hsum, hDoT⟩ := hdata
  have hj₀mem : j₀ ∈ T := by rw [hTj]; exact List.mem_singleton_self j₀
  have hj₀le : j₀ ≤ H := by
    have h := List.mem_range.mp (List.mem_of_mem_filter (by rwa [hT] at hj₀mem))
    omega
  have hmapU : (U.map (fun j => (⟨⟨.A, m.getD j 0 - 1, 2 * n⟩, true⟩ : GGKacOrbit))) =
      [⟨⟨.A, m.getD j₀ 0 - 1, 2 * n⟩, true⟩] := by rw [hUj]; simp
  rw [hmapU] at hDoT
  rcases List.append_eq_singleton_iff.mp hDoT with ⟨horb0nil, hoJ⟩ | ⟨_, hnil⟩
  · have hm0le : m.headD 0 ≤ 1 := by
      by_contra hlt
      have h2 : 2 ≤ m.headD 0 := by omega
      have hne : ggTUClAOrb0 n tw (m.headD 0) ≠ [] := by
        unfold ggTUClAOrb0
        rw [if_pos h2]
        by_cases htw : tw = false
        · rw [if_pos htw]; simp
        · rw [if_neg htw]; simp
      exact hne horb0nil
    have ha2 : 2 ≤ m.getD j₀ 0 := by
      have hmemU : j₀ ∈ U := by rw [hUj]; exact List.mem_singleton_self j₀
      have hm := List.mem_filter.mp (by rwa [hU] at hmemU)
      have hc : 1 ≤ j₀ ∧ 2 ≤ m.getD j₀ 0 := by simpa using hm.2
      exact hc.2
    have ho : o = ⟨⟨.A, m.getD j₀ 0 - 1, 2 * n⟩, true⟩ := by
      simpa using hoJ.symm
    have hTmap : (T.map (fun j => m.getD j 0)).sum = m.getD j₀ 0 := by rw [hTj]; simp
    have hsumj : m.sum = m.headD 0 + 2 * m.getD j₀ 0 := by rw [hsum, hTmap]
    have hsumja : r + 1 = m.headD 0 + 2 * m.getD j₀ 0 := by omega
    have h3p : 3 ≤ p := by
      have hj₀1 : 1 ≤ j₀ := by
        rw [hT] at hj₀mem
        have hc : 1 ≤ j₀ ∧ 0 < m.getD j₀ 0 := by
          have := (List.mem_filter.mp hj₀mem).2
          simpa using this
        exact hc.1
      omega
    exact ggTUClA_reflection_two hn hT5 ⟨ha2, hm0le, hsumja, ho⟩ hd h3p htriv hX hrk
  · exact absurd hnil (by simp)

private theorem ggTUClA_reflection_pos {r p n : ℕ} {tw : Bool} {m : List ℕ} {H : ℕ}
    {T U : List ℕ} {o : GGKacOrbit} (hn : 1 ≤ n)
    (hT5 : tw = true → p ∣ 2 ^ n - 1 → ¬ p ∣ 2 ^ n + 1 → r = 3 ∨ r = 5)
    (htriv : ¬ ((tw = false ∧ ggMultOrd p n = 1) ∨ (tw = true ∧ ggMultOrd p n = 2)))
    (hdata : ggTUClAReflData r p n tw m H T U o) (j₀ : ℕ) (hTj : T = [j₀])
    (hX : o.lab ≠ ⟨if tw then .twA else .A, r, n⟩)
    (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨if tw then .twA else .A, r, n⟩ := by
  have hdata' := hdata
  obtain ⟨hTle, hmlen, hmsum, hsymm, hd, hp_eq, hT, hU, hsum, hDoT⟩ := hdata
  have hUle : U.length ≤ 1 := by
    have h := ggTUClA_length_filter_le_of_imp (l := List.range (H + 1))
      (P := fun j => 1 ≤ j ∧ 2 ≤ m.getD j 0) (Q := fun j => 1 ≤ j ∧ 0 < m.getD j 0)
      (fun x hx => by omega)
    rw [← hU, ← hT, hTj] at h
    simpa using h
  have hUcases : U = [] ∨ U = [j₀] := by
    rcases Nat.eq_zero_or_pos U.length with h0 | hpos
    · exact Or.inl (List.length_eq_zero_iff.mp h0)
    · right
      obtain ⟨j₁, hUj⟩ := (List.length_eq_one_iff (l := U)).mp (by omega)
      have hj₁mem : j₁ ∈ U := by rw [hUj]; exact List.mem_singleton_self j₁
      have hj₁T : j₁ ∈ T := by
        have hUmem : j₁ ∈ U := hj₁mem
        rw [hU] at hUmem
        rw [hT]
        refine List.mem_filter.mpr ⟨List.mem_of_mem_filter hUmem, ?_⟩
        have := (List.mem_filter.mp hUmem).2
        simp only [decide_eq_true_eq] at this ⊢
        omega
      have hjj : j₁ = j₀ := by simpa [hTj] using hj₁T
      rw [hUj, hjj]
  rcases hUcases with hUnil | hUj
  · exact ggTUClA_reflection_pos_one hn htriv hdata' j₀ hTj hUnil hX hrk
  · exact ggTUClA_reflection_pos_two hn hT5 htriv hdata' j₀ hTj hUj hX hrk

private theorem ggTUClA_reflection {r p n : ℕ} {tw : Bool} {D : GGKacDatum} (hn : 1 ≤ n)
    (hT5 : tw = true → p ∣ 2 ^ n - 1 → ¬ p ∣ 2 ^ n + 1 → r = 3 ∨ r = 5)
    (hD : D ∈ ggMultTableCl (.A r) tw p n) (hrZ : D.rZ ≤ 1) {o : GGKacOrbit}
    (hDo : D.orbits = [o])
    (hX : o.lab ≠ ⟨if tw then .twA else .A, r, n⟩)
    (hrk : ¬ GGTPNPRankOne p o.lab)
    (htriv : ¬ ((tw = false ∧ ggMultOrd p n = 1) ∨ (tw = true ∧ ggMultOrd p n = 2))) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨if tw then .twA else .A, r, n⟩ := by
  obtain ⟨m, H, T, U, hdata⟩ := ggTUClA_reflection_setup hn hD hrZ hDo htriv
  have hTle : T.length ≤ 1 := hdata.1
  rcases Nat.eq_zero_or_pos T.length with h0 | hpos
  · exact ggTUClA_reflection_empty htriv hdata (List.length_eq_zero_iff.mp h0) hX hrk
  · have hT1 : T.length = 1 := by omega
    obtain ⟨j₀, hTj⟩ := List.length_eq_one_iff.mp hT1
    exact ggTUClA_reflection_pos hn hT5 htriv hdata j₀ hTj hX hrk
theorem ggTablePRow_of_mem_ggMultTableCl_A {r p n : ℕ} {tw : Bool} {D : GGKacDatum} (hn : 1 ≤ n)
    (hT5 : tw = true → p ∣ 2 ^ n - 1 → ¬ p ∣ 2 ^ n + 1 → r = 3 ∨ r = 5)
    (hD : D ∈ ggMultTableCl (.A r) tw p n) (hrZ : D.rZ ≤ 1) {o : GGKacOrbit}
    (hDo : D.orbits = [o]) (hqs : o.qs = true) (hX : o.lab ≠ ⟨if tw then .twA else .A, r, n⟩)
    (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨if tw then .twA else .A, r, n⟩ := by
  by_cases htriv : (tw = false ∧ ggMultOrd p n = 1) ∨ (tw = true ∧ ggMultOrd p n = 2)
  · exact ggTUClA_trivial hn hD hrZ hDo hqs hX hrk htriv
  · exact ggTUClA_reflection hn hT5 hD hrZ hDo hX hrk htriv

end CFSG.StandardType

end
