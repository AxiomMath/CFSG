module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.StandardType.GGSimplyLacedTits

public section

namespace CFSG.StandardType

@[expose] def ggDeps (n : ℕ) (v : ℕ → ℤ) (k : ℕ) : ℤ :=
  if k = 0 then v 0
  else if k + 3 ≤ n then v k - v (k - 1)
  else if k + 2 = n then v (n - 2) + v (n - 1) - v (n - 3)
  else if k + 1 = n then v (n - 1) - v (n - 2)
  else 0

@[expose] def GGDRoot (n : ℕ) (u : ℕ → ℤ) : Prop :=
  ∃ a b : ℕ, a < n ∧ b < n ∧ a ≠ b ∧ ∃ s t : ℤ, (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧
    ∀ k, ggDeps n u k = (if k = a then s else 0) + (if k = b then t else 0)

@[expose] def ggDinv (n : ℕ) (x : ℕ → ℤ) (i : ℕ) : ℤ :=
  if i + 3 ≤ n then ∑ k ∈ Finset.range (i + 1), x k
  else if i + 2 = n then ((∑ k ∈ Finset.range (n - 1), x k) - x (n - 1)) / 2
  else if i + 1 = n then ((∑ k ∈ Finset.range (n - 1), x k) + x (n - 1)) / 2
  else 0

@[expose] def ggDRootList (n : ℕ) : List (List ℤ) :=
  (List.range n).flatMap fun a => (List.range n).flatMap fun b =>
    if a < b then
      [(1, 1), (1, -1), (-1, 1), (-1, -1)].map fun st : ℤ × ℤ =>
        (List.range n).map
          (ggDinv n fun k => (if k = a then st.1 else 0) + (if k = b then st.2 else 0))
    else []

private theorem drm_deps_zero (n : ℕ) (u : ℕ → ℤ) : ggDeps n u 0 = u 0 := by
  unfold ggDeps
  rw [if_pos rfl]

private theorem drm_deps_chain (n : ℕ) (u : ℕ → ℤ) (k : ℕ) (hk : 0 < k) (hkn : k + 3 ≤ n) :
    ggDeps n u k = u k - u (k - 1) := by
  unfold ggDeps
  rw [if_neg (by omega : ¬ k = 0), if_pos hkn]

private theorem drm_sum_chain (n : ℕ) (u : ℕ → ℤ) :
    ∀ i, i + 3 ≤ n → (∑ k ∈ Finset.range (i + 1), ggDeps n u k) = u i := by
  intro i
  induction i with
  | zero =>
      intro _
      simp [drm_deps_zero]
  | succ i ih =>
      intro hi
      rw [Finset.sum_range_succ, ih (by omega)]
      rw [drm_deps_chain n u (i + 1) (by omega) (by omega)]
      have hidx : (i + 1) - 1 = i := by omega
      rw [hidx]
      ring

private theorem drm_deps_spin2 (n : ℕ) (hn : 3 ≤ n) (v : ℕ → ℤ) :
    ggDeps n v (n - 2) = v (n - 2) + v (n - 1) - v (n - 3) := by
  unfold ggDeps
  rw [if_neg (by omega : ¬ (n - 2) = 0), if_neg (by omega : ¬ (n - 2) + 3 ≤ n),
      if_pos (by omega : (n - 2) + 2 = n)]

private theorem drm_deps_spin (n : ℕ) (hn : 4 ≤ n) (v : ℕ → ℤ) :
    ggDeps n v (n - 1) = v (n - 1) - v (n - 2) := by
  unfold ggDeps
  rw [if_neg (by omega : ¬ (n - 1) = 0), if_neg (by omega : ¬ (n - 1) + 3 ≤ n),
      if_neg (by omega : ¬ (n - 1) + 2 = n), if_pos (by omega : (n - 1) + 1 = n)]

private theorem drm_sum_spin (n : ℕ) (hn : 4 ≤ n) (u : ℕ → ℤ) :
    (∑ k ∈ Finset.range (n - 1), ggDeps n u k) = u (n - 2) + u (n - 1) := by
  have hchain : (∑ k ∈ Finset.range (n - 2), ggDeps n u k) = u (n - 3) := by
    have h := drm_sum_chain n u (n - 3) (by omega)
    simpa only [show n - 3 + 1 = n - 2 by omega] using h
  have hstep : (∑ k ∈ Finset.range (n - 1), ggDeps n u k) =
      (∑ k ∈ Finset.range (n - 2), ggDeps n u k) + ggDeps n u (n - 2) := by
    rw [show n - 1 = n - 2 + 1 by omega, Finset.sum_range_succ]
  have hd : ggDeps n u (n - 2) = u (n - 2) + u (n - 1) - u (n - 3) :=
    drm_deps_spin2 n (by omega) u
  rw [hstep, hchain, hd]
  ring

private theorem drm_abs_pair (a b m : ℕ) (s t : ℤ)
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    |(if a < m then s else 0) + (if b < m then t else 0)| ≤ 2 := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  all_goals
    split_ifs <;> norm_num

private theorem drm_abs_one (a b k : ℕ) (s t : ℤ) (hab : a ≠ b)
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    |(if k = a then s else 0) + (if k = b then t else 0)| ≤ 1 := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  all_goals
    split_ifs <;> first | (exfalso; omega) | norm_num

theorem ggDRoot_abs_le {n : ℕ} (hn : 5 ≤ n) {u : ℕ → ℤ} (hu : GGDRoot n u) {i : ℕ} (hi : i < n) :
    |u i| ≤ 2 := by
  obtain ⟨a, b, _, _, hab, s, t, hs, ht, hx⟩ := hu
  by_cases hchain : i + 3 ≤ n
  · have hsum := drm_sum_chain n u i hchain
    have hpair : (∑ k ∈ Finset.range (i + 1),
        ((if k = a then s else 0) + (if k = b then t else 0))) = u i := by
      rw [← hsum]
      exact Finset.sum_congr rfl (fun k _ => (hx k).symm)
    rw [← hpair, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_range]
    exact drm_abs_pair a b (i + 1) s t hs ht
  · have hsp : i = n - 2 ∨ i = n - 1 := by omega
    have hS : (∑ k ∈ Finset.range (n - 1), ggDeps n u k) = u (n - 2) + u (n - 1) :=
      drm_sum_spin n (by omega) u
    have hB : ggDeps n u (n - 1) = u (n - 1) - u (n - 2) := drm_deps_spin n (by omega) u
    have hSp : (∑ k ∈ Finset.range (n - 1), ggDeps n u k) =
        (if a < n - 1 then s else 0) + (if b < n - 1 then t else 0) := by
      calc
        (∑ k ∈ Finset.range (n - 1), ggDeps n u k)
            = ∑ k ∈ Finset.range (n - 1),
                ((if k = a then s else 0) + (if k = b then t else 0)) :=
              Finset.sum_congr rfl (fun k _ => hx k)
        _ = (∑ k ∈ Finset.range (n - 1), (if k = a then s else 0))
              + (∑ k ∈ Finset.range (n - 1), (if k = b then t else 0)) :=
              Finset.sum_add_distrib
        _ = _ := by
              rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
              simp only [Finset.mem_range]
    have hA2 := drm_abs_pair a b (n - 1) s t hs ht
    have hB2 := drm_abs_one a b (n - 1) s t hab hs ht
    have hAb := abs_le.mp hA2
    have hBb := abs_le.mp hB2
    rw [hSp] at hS
    rw [hx (n - 1)] at hB
    rcases hsp with hsp | hsp
    · rw [hsp]
      have heq : 2 * u (n - 2) =
          ((if a < n - 1 then s else 0) + (if b < n - 1 then t else 0))
            - ((if (n - 1) = a then s else 0) + (if (n - 1) = b then t else 0)) := by
        omega
      have hle : u (n - 2) ≤ 2 := by omega
      have hge : -2 ≤ u (n - 2) := by omega
      exact abs_le.mpr ⟨hge, hle⟩
    · rw [hsp]
      have heq : 2 * u (n - 1) =
          ((if a < n - 1 then s else 0) + (if b < n - 1 then t else 0))
            + ((if (n - 1) = a then s else 0) + (if (n - 1) = b then t else 0)) := by
        omega
      have hle : u (n - 1) ≤ 2 := by omega
      have hge : -2 ≤ u (n - 1) := by omega
      exact abs_le.mpr ⟨hge, hle⟩

private theorem drm_deps_zero_of_lt (n m : ℕ) (u : ℕ → ℤ) (hz : ∀ i < m, u i = 0)
    (hmn : m + 5 ≤ n) {k : ℕ} (hk : k < m) : ggDeps n u k = 0 := by
  unfold ggDeps
  by_cases h0 : k = 0
  · subst h0
    rw [if_pos rfl, hz 0 (by omega)]
  · have hc : k + 3 ≤ n := by omega
    rw [if_neg h0, if_pos hc, hz k hk]
    have hk1 : k - 1 < m := by omega
    rw [hz (k - 1) hk1]
    ring

private theorem drm_deps_shift (n m : ℕ) (u : ℕ → ℤ) (hz : ∀ i < m, u i = 0)
    (hm : 1 ≤ m) (hmn : m + 5 ≤ n) (k : ℕ) :
    ggDeps (n - m) (fun i => u (m + i)) k = ggDeps n u (m + k) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp only [Nat.add_zero]
    have hL : ggDeps (n - m) (fun i => u (m + i)) 0 = u m := by
      unfold ggDeps
      rw [if_pos rfl]
      simp only [Nat.add_zero]
    have hR : ggDeps n u m = u m := by
      unfold ggDeps
      rw [if_neg (by omega : ¬ m = 0), if_pos (by omega : m + 3 ≤ n)]
      rw [hz (m - 1) (by omega)]
      ring
    rw [hL, hR]
  · by_cases hc : k + 3 ≤ n - m
    · have hL : ggDeps (n - m) (fun i => u (m + i)) k =
          (fun i => u (m + i)) k - (fun i => u (m + i)) (k - 1) :=
        drm_deps_chain (n - m) (fun i => u (m + i)) k hkpos hc
      have hR : ggDeps n u (m + k) = u (m + k) - u (m + (k - 1)) := by
        have h1 : 0 < m + k := by omega
        have h2 : (m + k) + 3 ≤ n := by omega
        have h3 : (m + k) - 1 = m + (k - 1) := by omega
        rw [drm_deps_chain n u (m + k) h1 h2, h3]
      rw [hL, hR]
    · by_cases hs2 : k + 2 = n - m
      · have hL : ggDeps (n - m) (fun i => u (m + i)) k =
            (fun i => u (m + i)) (n - m - 2) + (fun i => u (m + i)) (n - m - 1)
              - (fun i => u (m + i)) (n - m - 3) := by
          unfold ggDeps
          rw [if_neg (by omega : ¬ k = 0), if_neg hc, if_pos hs2]
        have hmk : m + k = n - 2 := by omega
        have hR : ggDeps n u (m + k) = u (n - 2) + u (n - 1) - u (n - 3) := by
          rw [hmk]
          exact drm_deps_spin2 n (by omega) u
        rw [hL, hR]
        simp only [show m + (n - m - 2) = n - 2 by omega,
          show m + (n - m - 1) = n - 1 by omega,
          show m + (n - m - 3) = n - 3 by omega]
      · by_cases hs1 : k + 1 = n - m
        · have hL : ggDeps (n - m) (fun i => u (m + i)) k =
              (fun i => u (m + i)) (n - m - 1) - (fun i => u (m + i)) (n - m - 2) := by
            unfold ggDeps
            rw [if_neg (by omega : ¬ k = 0), if_neg hc, if_neg hs2, if_pos hs1]
          have hmk : m + k = n - 1 := by omega
          have hR : ggDeps n u (m + k) = u (n - 1) - u (n - 2) := by
            rw [hmk]
            exact drm_deps_spin n (by omega) u
          rw [hL, hR]
          simp only [show m + (n - m - 1) = n - 1 by omega,
            show m + (n - m - 2) = n - 2 by omega]
        · have hL : ggDeps (n - m) (fun i => u (m + i)) k = 0 := by
            unfold ggDeps
            rw [if_neg (by omega : ¬ k = 0), if_neg hc, if_neg hs2, if_neg hs1]
          have hR : ggDeps n u (m + k) = 0 := by
            unfold ggDeps
            rw [if_neg (by omega : ¬ m + k = 0), if_neg (by omega : ¬ (m + k) + 3 ≤ n),
                if_neg (by omega : ¬ (m + k) + 2 = n),
                if_neg (by omega : ¬ (m + k) + 1 = n)]
          rw [hL, hR]

theorem ggDRoot_tail {n m : ℕ} (hnm : m + 5 ≤ n) {u : ℕ → ℤ} (hu : GGDRoot n u)
    (hz : ∀ i < m, u i = 0) : GGDRoot (n - m) (fun i => u (m + i)) := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    simpa only [Nat.sub_zero, Nat.zero_add] using hu
  · obtain ⟨a, b, _, _, hab, s, t, hs, ht, hx⟩ := hu
    have hge_a : m ≤ a := by
      by_contra h
      have hlt : a < m := by omega
      have hz0 : ggDeps n u a = 0 := drm_deps_zero_of_lt n m u hz hnm hlt
      have hp := hx a
      rw [hz0, if_pos rfl, if_neg hab] at hp
      rcases hs with h | h <;> omega
    have hge_b : m ≤ b := by
      by_contra h
      have hlt : b < m := by omega
      have hz0 : ggDeps n u b = 0 := drm_deps_zero_of_lt n m u hz hnm hlt
      have hp := hx b
      rw [hz0, if_neg (Ne.symm hab), if_pos rfl] at hp
      rcases ht with h | h <;> omega
    refine ⟨a - m, b - m, by omega, by omega, by omega, s, t, hs, ht, ?_⟩
    intro k
    rw [drm_deps_shift n m u hz hmpos hnm k, hx (m + k)]
    have h1 : (if m + k = a then s else 0) = (if k = a - m then s else 0) := by
      by_cases h : m + k = a
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    have h2 : (if m + k = b then t else 0) = (if k = b - m then t else 0) := by
      by_cases h : m + k = b
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    rw [h1, h2]

private theorem drm_dinv_chain (n : ℕ) (u : ℕ → ℤ) (i : ℕ) (hi : i + 3 ≤ n) :
    ggDinv n (ggDeps n u) i = u i := by
  unfold ggDinv
  rw [if_pos hi]
  exact drm_sum_chain n u i hi

private theorem drm_dinv_spin2 (n : ℕ) (hn : 4 ≤ n) (u : ℕ → ℤ) :
    ggDinv n (ggDeps n u) (n - 2) = u (n - 2) := by
  unfold ggDinv
  rw [if_neg (by omega : ¬ (n - 2) + 3 ≤ n),
      if_pos (by omega : (n - 2) + 2 = n)]
  rw [drm_sum_spin n hn u, drm_deps_spin n hn u]
  have h : u (n - 2) + u (n - 1) - (u (n - 1) - u (n - 2)) = 2 * u (n - 2) := by
    ring
  rw [h]
  exact Int.mul_ediv_cancel_left (u (n - 2)) (by norm_num)

private theorem drm_dinv_spin1 (n : ℕ) (hn : 4 ≤ n) (u : ℕ → ℤ) :
    ggDinv n (ggDeps n u) (n - 1) = u (n - 1) := by
  unfold ggDinv
  rw [if_neg (by omega : ¬ (n - 1) + 3 ≤ n),
      if_neg (by omega : ¬ (n - 1) + 2 = n),
      if_pos (by omega : (n - 1) + 1 = n)]
  rw [drm_sum_spin n hn u, drm_deps_spin n hn u]
  have h : u (n - 2) + u (n - 1) + (u (n - 1) - u (n - 2)) = 2 * u (n - 1) := by
    ring
  rw [h]
  exact Int.mul_ediv_cancel_left (u (n - 1)) (by norm_num)

private theorem drm_left_inv (n : ℕ) (hn : 4 ≤ n) (u : ℕ → ℤ) (i : ℕ) (hi : i < n) :
    ggDinv n (ggDeps n u) i = u i := by
  by_cases h1 : i + 3 ≤ n
  · exact drm_dinv_chain n u i h1
  · by_cases h2 : i + 2 = n
    · have hi2 : i = n - 2 := by omega
      rw [hi2]
      exact drm_dinv_spin2 n hn u
    · by_cases h3 : i + 1 = n
      · have hi1 : i = n - 1 := by omega
        rw [hi1]
        exact drm_dinv_spin1 n hn u
      · exfalso
        omega

private theorem drm_pair_mem (s t : ℤ) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    (s, t) ∈ [(1, 1), (1, -1), (-1, 1), (-1, -1)] := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp

private theorem drm_mem_ggDRootList_of_pair (n a b : ℕ) (s t : ℤ) (ha : a < n) (hb : b < n)
    (hab : a < b) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    (List.range n).map (ggDinv n fun k =>
        (if k = a then s else 0) + (if k = b then t else 0)) ∈ ggDRootList n := by
  rw [ggDRootList, List.mem_flatMap]
  refine ⟨a, List.mem_range.mpr ha, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨b, List.mem_range.mpr hb, ?_⟩
  rw [if_pos hab, List.mem_map]
  exact ⟨(s, t), drm_pair_mem s t hs ht, rfl⟩

theorem ggDRoot_mem_ggDRootList {n : ℕ} (hn : 4 ≤ n) {u : ℕ → ℤ} (hu : GGDRoot n u) :
    (List.range n).map u ∈ ggDRootList n := by
  obtain ⟨a, b, ha, hb, hab, s, t, hs, ht, hx⟩ := hu
  have hinv : ∀ i < n, u i = ggDinv n (ggDeps n u) i := by
    intro i hi
    rw [drm_left_inv n hn u i hi]
  have hfun_a : ggDeps n u =
      (fun k => (if k = a then s else 0) + (if k = b then t else 0)) := funext hx
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have hmem : (List.range n).map (ggDinv n fun k =>
        (if k = a then s else 0) + (if k = b then t else 0)) ∈ ggDRootList n :=
      drm_mem_ggDRootList_of_pair n a b s t ha hb hlt hs ht
    have hvec : (List.range n).map u = (List.range n).map (ggDinv n fun k =>
        (if k = a then s else 0) + (if k = b then t else 0)) := by
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      rw [hinv i hi, hfun_a]
    rw [hvec]
    exact hmem
  · have hfun_b : ggDeps n u =
        (fun k => (if k = b then t else 0) + (if k = a then s else 0)) :=
      funext fun k => by rw [hx k]; ring
    have hmem : (List.range n).map (ggDinv n fun k =>
        (if k = b then t else 0) + (if k = a then s else 0)) ∈ ggDRootList n :=
      drm_mem_ggDRootList_of_pair n b a t s hb ha hgt ht hs
    have hvec : (List.range n).map u = (List.range n).map (ggDinv n fun k =>
        (if k = b then t else 0) + (if k = a then s else 0)) := by
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      rw [hinv i hi, hfun_b]
    rw [hvec]
    exact hmem

end CFSG.StandardType
