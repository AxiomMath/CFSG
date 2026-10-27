module

public import CFSG.LocalAnalysis.StandardType.GGK0MarkedKacIface1587
import CFSG.LocalAnalysis.StandardType.GGKacCompsSpec

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG.Assembly

private theorem k0lst_getD_set_ne {l : List ℕ} {i j : ℕ} (h : i ≠ j) (a d : ℕ) :
    (l.set i a).getD j d = l.getD j d := by
  by_cases hj : j < l.length
  · rw [List.getD_eq_getElem (hn := by simpa [List.length_set] using hj),
      List.getElem_set_ne h (by simpa [List.length_set] using hj),
      List.getD_eq_getElem (hn := hj)]
  · have hj' : (l.set i a).length ≤ j := by simpa [List.length_set] using Nat.le_of_not_lt hj
    rw [List.getD_eq_default _ _ hj', List.getD_eq_default _ _ (Nat.le_of_not_lt hj)]

private theorem k0lst_getD_set_self {l : List ℕ} {i : ℕ} (h : i < l.length) (a d : ℕ) :
    (l.set i a).getD i d = a := by
  rw [List.getD_eq_getElem (hn := by simpa [List.length_set] using h)]
  exact List.getElem_set_self (by simpa [List.length_set] using h)

private theorem k0lstAct_go_length (s : List ℕ) :
    ∀ (l : List ℕ) (i : ℕ) (acc : List ℕ), (k0pAct.go s i l acc).length = acc.length := by
  intro l
  induction l with
  | nil => intro i acc; rw [k0pAct.go.eq_1]
  | cons x xs ih =>
      intro i acc
      rw [k0pAct.go.eq_2]
      exact (ih (i + 1) (acc.set x (s.getD i 0))).trans List.length_set

private theorem k0lstInv_go_length :
    ∀ (l : List ℕ) (i : ℕ) (acc : List ℕ), (k0pInv.go i l acc).length = acc.length := by
  intro l
  induction l with
  | nil => intro i acc; rw [k0pInv.go.eq_1]
  | cons x xs ih =>
      intro i acc
      rw [k0pInv.go.eq_2]
      exact (ih (i + 1) (acc.set x i)).trans List.length_set

private theorem k0lstAct_go_getD_not_mem (s : List ℕ) :
    ∀ (l : List ℕ) (i : ℕ) (acc : List ℕ) (j : ℕ), j ∉ l →
      (k0pAct.go s i l acc).getD j 0 = acc.getD j 0 := by
  intro l
  induction l with
  | nil => intro i acc j _; rw [k0pAct.go.eq_1]
  | cons x xs ih =>
      intro i acc j hj
      rw [k0pAct.go.eq_2]
      rw [ih (i + 1) (acc.set x (s.getD i 0)) j (by simp at hj ⊢; tauto)]
      exact k0lst_getD_set_ne (by simp at hj; tauto) _ _

private theorem k0lstInv_go_getD_not_mem :
    ∀ (l : List ℕ) (i : ℕ) (acc : List ℕ) (j : ℕ), j ∉ l →
      (k0pInv.go i l acc).getD j 0 = acc.getD j 0 := by
  intro l
  induction l with
  | nil => intro i acc j _; rw [k0pInv.go.eq_1]
  | cons x xs ih =>
      intro i acc j hj
      rw [k0pInv.go.eq_2]
      rw [ih (i + 1) (acc.set x i) j (by simp at hj ⊢; tauto)]
      exact k0lst_getD_set_ne (by simp at hj; tauto) _ _

private theorem k0lstAct_go_getD_mem (s : List ℕ) :
    ∀ (l : List ℕ) (i : ℕ) (acc : List ℕ), l.Nodup → (∀ x ∈ l, x < acc.length) →
      ∀ k < l.length, (k0pAct.go s i l acc).getD (l.getD k 0) 0 = s.getD (i + k) 0 := by
  intro l
  induction l with
  | nil => intro i acc _ _ k hk; simp at hk
  | cons x xs ih =>
      intro i acc hnd hlt k hk
      have hxacc : x < acc.length := hlt x (by simp)
      have hxnx : x ∉ xs := (List.nodup_cons.mp hnd).1
      have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
      have hlt' : ∀ y ∈ xs, y < (acc.set x (s.getD i 0)).length := by
        intro y hy
        rw [List.length_set]
        exact hlt y (by simp [hy])
      rw [k0pAct.go.eq_2]
      cases k with
      | zero =>
          rw [List.getD_cons_zero, k0lstAct_go_getD_not_mem s xs (i + 1) _ x hxnx,
            k0lst_getD_set_self hxacc, Nat.add_zero]
      | succ k =>
          rw [List.getD_cons_succ,
            ih (i + 1) (acc.set x (s.getD i 0)) hnd' hlt' k (by simpa using hk)]
          congr 1
          omega

private theorem k0lstInv_go_getD_mem :
    ∀ (l : List ℕ) (i : ℕ) (acc : List ℕ), l.Nodup → (∀ x ∈ l, x < acc.length) →
      ∀ k < l.length, (k0pInv.go i l acc).getD (l.getD k 0) 0 = i + k := by
  intro l
  induction l with
  | nil => intro i acc _ _ k hk; simp at hk
  | cons x xs ih =>
      intro i acc hnd hlt k hk
      have hxacc : x < acc.length := hlt x (by simp)
      have hxnx : x ∉ xs := (List.nodup_cons.mp hnd).1
      have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
      have hlt' : ∀ y ∈ xs, y < (acc.set x i).length := by
        intro y hy
        rw [List.length_set]
        exact hlt y (by simp [hy])
      rw [k0pInv.go.eq_2]
      cases k with
      | zero =>
          rw [List.getD_cons_zero, k0lstInv_go_getD_not_mem xs (i + 1) _ x hxnx,
            k0lst_getD_set_self hxacc, Nat.add_zero]
      | succ k =>
          rw [List.getD_cons_succ,
            ih (i + 1) (acc.set x i) hnd' hlt' k (by simpa using hk)]
          omega

private theorem k0lst_map_range_getD (a : List ℕ) :
    (List.range a.length).map (fun i => a.getD i 0) = a := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem (hn := hj')]

private theorem k0lst_exists_getD {n : ℕ} {a : List ℕ} (ha : a.Perm (List.range n)) {j : ℕ}
    (hj : j < n) : ∃ i, i < a.length ∧ a.getD i 0 = j := by
  have hmem : j ∈ a := ha.mem_iff.mpr (List.mem_range.mpr hj)
  obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp hmem
  exact ⟨i, hi, by rw [List.getD_eq_getElem (hn := hi)]; exact hia⟩


theorem k0pAct_length (a s : List ℕ) : (k0pAct a s).length = s.length := by
  rw [k0pAct, k0lstAct_go_length, List.length_replicate]

theorem k0pAct_getD_of_perm {n : ℕ} {a s : List ℕ} (ha : a.Perm (List.range n))
    (hs : s.length = n) {i : ℕ} (hi : i < n) :
    (k0pAct a s).getD (a.getD i 0) 0 = s.getD i 0 := by
  have hnd : a.Nodup := ha.nodup_iff.mpr List.nodup_range
  have hlen : a.length = n := ha.length_eq.trans List.length_range
  have hle : ∀ x ∈ a, x < (List.replicate s.length 0).length := by
    intro x hx
    rw [List.length_replicate]
    have := (ha.mem_iff.mp hx)
    rw [List.mem_range] at this
    omega
  have hi' : i < a.length := by omega
  have h := k0lstAct_go_getD_mem s a 0 (List.replicate s.length 0) hnd hle i hi'
  rw [k0pAct]
  simpa using h

theorem k0pMul_getD (a b : List ℕ) {i : ℕ} (hi : i < b.length) :
    (k0pMul a b).getD i 0 = a.getD (b.getD i 0) 0 := by
  induction b generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          have hi' : i < xs.length := by simpa using hi
          show (xs.map (fun j => a.getD j 0)).getD i 0 = a.getD (xs.getD i 0) 0
          exact ih hi'

theorem k0pMul_perm {n : ℕ} {a b : List ℕ} (ha : a.Perm (List.range n))
    (hb : b.Perm (List.range n)) : (k0pMul a b).Perm (List.range n) := by
  have h1 : (k0pMul a b).Perm ((List.range n).map (fun i => a.getD i 0)) := by
    rw [k0pMul]; exact hb.map _
  have h2 : (List.range n).map (fun i => a.getD i 0) = a := by
    have hlen : a.length = n := ha.length_eq.trans List.length_range
    simpa [hlen] using k0lst_map_range_getD a
  rw [h2] at h1
  exact h1.trans ha

theorem k0pInv_getD_of_perm {n : ℕ} {a : List ℕ} (ha : a.Perm (List.range n)) {i : ℕ}
    (hi : i < n) : (k0pInv a).getD (a.getD i 0) 0 = i := by
  have hnd : a.Nodup := ha.nodup_iff.mpr List.nodup_range
  have hlen : a.length = n := ha.length_eq.trans List.length_range
  have hle : ∀ x ∈ a, x < (List.replicate a.length 0).length := by
    intro x hx
    rw [List.length_replicate]
    have := List.mem_range.mp (ha.mem_iff.mp hx)
    omega
  have hi' : i < a.length := by omega
  have h := k0lstInv_go_getD_mem a 0 (List.replicate a.length 0) hnd hle i hi'
  rw [k0pInv]
  simpa using h

private theorem k0lst_apply_inv {n : ℕ} {a : List ℕ} (ha : a.Perm (List.range n)) {j : ℕ}
    (hj : j < n) : a.getD ((k0pInv a).getD j 0) 0 = j := by
  have hlen : a.length = n := ha.length_eq.trans List.length_range
  obtain ⟨i, hi, hia⟩ := k0lst_exists_getD ha hj
  have h := k0pInv_getD_of_perm ha (i := i) (by omega : i < n)
  rw [hia] at h
  rw [← hia] at h ⊢
  rw [h]

theorem k0pInv_perm {n : ℕ} {a : List ℕ} (ha : a.Perm (List.range n)) :
    (k0pInv a).Perm (List.range n) := by
  have hlen : a.length = n := ha.length_eq.trans List.length_range
  have hinvlen : (k0pInv a).length = n := by
    rw [k0pInv, k0lstInv_go_length, List.length_replicate, hlen]
  have hmap : (k0pInv a).map (fun j => a.getD j 0) = List.range n := by
    apply List.ext_getElem
    · rw [List.length_map, hinvlen, List.length_range]
    · intro j hj hj'
      have hj'' : j < n := by simpa using hj'
      rw [List.getElem_map, List.getElem_range, List.getElem_eq_getD (fallback := 0)]
      exact k0lst_apply_inv ha hj''
  have hnodup : (k0pInv a).Nodup := by
    apply List.Nodup.of_map (fun j => a.getD j 0)
    rw [hmap]
    exact List.nodup_range
  have hentry : ∀ x ∈ k0pInv a, x < n := by
    intro x hx
    obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.mp hx
    have hj' : j < n := by rw [← hinvlen]; exact hj
    have hxj : x = (k0pInv a).getD j 0 := by rw [← hjx, List.getElem_eq_getD]
    rw [hxj]
    obtain ⟨i, hi, hia⟩ := k0lst_exists_getD ha hj'
    have hformula := k0pInv_getD_of_perm ha (i := i) (by omega : i < n)
    rw [hia] at hformula
    rw [hformula]
    omega
  have hsub : (k0pInv a).toFinset ⊆ (List.range n).toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    rw [List.mem_range]
    exact hentry x hx
  have hcard : (List.range n).toFinset.card ≤ (k0pInv a).toFinset.card := by
    rw [List.toFinset_card_of_nodup hnodup, hinvlen, List.toFinset_range, Finset.card_range]
  have heq : (k0pInv a).toFinset = (List.range n).toFinset :=
    Finset.eq_of_subset_of_card_le hsub hcard
  exact List.perm_of_nodup_nodup_toFinset_eq hnodup List.nodup_range heq


private theorem k0pAct_mul {n : ℕ} {a b s : List ℕ} (ha : a.Perm (List.range n))
    (hb : b.Perm (List.range n)) (hs : s.length = n) :
    k0pAct b (k0pAct a s) = k0pAct (k0pMul b a) s := by
  have hlen' : (k0pAct a s).length = n := by rw [k0pAct_length, hs]
  have hal : a.length = n := ha.length_eq.trans List.length_range
  have hbl : b.length = n := hb.length_eq.trans List.length_range
  have hinvperm : (k0pInv a).Perm (List.range n) := k0pInv_perm ha
  have hinvlen : (k0pInv a).length = n := hinvperm.length_eq.trans List.length_range
  apply List.ext_getElem
  · simp [k0pAct_length, hs]
  · intro j hj hj'
    have hjlt : j < n := by rw [k0pAct_length, hlen'] at hj; exact hj
    obtain ⟨i, hi, hia⟩ := k0lst_exists_getD hb hjlt
    have hin : i < n := by rw [← hbl]; exact hi
    have hi'lt : (k0pInv a).getD i 0 < n := by
      have hmem : (k0pInv a).getD i 0 ∈ k0pInv a := by
        rw [List.getD_eq_getElem (hn := by rw [hinvlen]; exact hin)]
        exact List.getElem_mem _
      exact List.mem_range.mp (hinvperm.mem_iff.mp hmem)
    have hai : a.getD ((k0pInv a).getD i 0) 0 = i := k0lst_apply_inv ha hin
    have hL : (k0pAct b (k0pAct a s)).getD (b.getD i 0) 0 = (k0pAct a s).getD i 0 :=
      k0pAct_getD_of_perm hb hlen' hin
    have hL2 : (k0pAct a s).getD i 0 = s.getD ((k0pInv a).getD i 0) 0 := by
      have h := k0pAct_getD_of_perm ha hs hi'lt
      rwa [hai] at h
    have hc : (k0pMul b a).Perm (List.range n) := k0pMul_perm hb ha
    have hci : (k0pMul b a).getD ((k0pInv a).getD i 0) 0 = b.getD i 0 := by
      rw [k0pMul_getD b a (by rw [hal]; exact hi'lt), hai]
    have hR : (k0pAct (k0pMul b a) s).getD (b.getD i 0) 0
        = s.getD ((k0pInv a).getD i 0) 0 := by
      rw [← hci]
      exact k0pAct_getD_of_perm hc hs hi'lt
    rw [List.getElem_eq_getD (fallback := 0), List.getElem_eq_getD (fallback := 0), ← hia,
      hL, hL2]
    exact hR.symm

private theorem k0pAct_id {n : ℕ} {s : List ℕ} (hs : s.length = n) :
    k0pAct (k0pId n) s = s := by
  have hperm : (k0pId n).Perm (List.range n) := List.Perm.refl _
  apply List.ext_getElem
  · rw [k0pAct_length, hs]
  · intro j hj hj'
    have hjn : j < n := by rw [← hs]; exact hj'
    have h1 : (k0pAct (k0pId n) s)[j] = s[j] := by
      rw [List.getElem_eq_getD (fallback := 0), List.getElem_eq_getD (fallback := 0)]
      have hg : (k0pId n).getD j 0 = j := by
        rw [k0pId, List.getD_eq_getElem (hn := by simpa using hjn)]
        exact List.getElem_range _
      have h2 := k0pAct_getD_of_perm (a := k0pId n) (s := s) (n := n) hperm hs (i := j) hjn
      rw [hg] at h2
      exact h2
    rw [h1]

theorem omega_perm (T : GGKacType) {a : List ℕ} (ha : a ∈ (k0DiagOf T).omega) :
    a.Perm (List.range (k0DiagOf T).marks.length) := by
  cases T
  · simp only [k0DiagOf, k0E6Diag, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    all_goals decide
  · simp only [k0DiagOf, k0E7Diag, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    all_goals decide
  · simp only [k0DiagOf, k0E8Diag, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    all_goals decide
  · simp only [k0DiagOf, k0F4Diag, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    all_goals decide

theorem one_mem_omega (T : GGKacType) :
    k0pId (k0DiagOf T).marks.length ∈ (k0DiagOf T).omega := by
  cases T <;> decide

theorem mul_mem_omega (T : GGKacType) {a b : List ℕ} (ha : a ∈ (k0DiagOf T).omega)
    (hb : b ∈ (k0DiagOf T).omega) : k0pMul a b ∈ (k0DiagOf T).omega := by
  cases T
  · simp only [k0DiagOf, k0E6Diag, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl | rfl
    all_goals rcases hb with rfl | rfl | rfl
    all_goals decide
  · simp only [k0DiagOf, k0E7Diag, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl
    all_goals rcases hb with rfl | rfl
    all_goals decide
  · simp only [k0DiagOf, k0E8Diag, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl
    all_goals rcases hb with rfl
    all_goals decide
  · simp only [k0DiagOf, k0F4Diag, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl
    all_goals rcases hb with rfl
    all_goals decide

theorem inv_mem_omega (T : GGKacType) {a : List ℕ} (ha : a ∈ (k0DiagOf T).omega) :
    k0pInv a ∈ (k0DiagOf T).omega := by
  cases T
  · simp only [k0DiagOf, k0E6Diag, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    all_goals decide
  · simp only [k0DiagOf, k0E7Diag, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    all_goals decide
  · simp only [k0DiagOf, k0E8Diag, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    all_goals decide
  · simp only [k0DiagOf, k0F4Diag, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    all_goals decide

theorem omega_marks (T : GGKacType) {a : List ℕ} (ha : a ∈ (k0DiagOf T).omega) {i : ℕ}
    (hi : i < (k0DiagOf T).marks.length) :
    (k0DiagOf T).marks.getD (a.getD i 0) 0 = (k0DiagOf T).marks.getD i 0 := by
  cases T
  · simp only [k0DiagOf, k0E6Diag, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
    simp only [k0DiagOf, k0E6Diag] at hi
    have hi7 : i < 7 := by simpa using hi
    rcases ha with rfl | rfl | rfl
    all_goals interval_cases i
    all_goals decide
  · simp only [k0DiagOf, k0E7Diag, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
    simp only [k0DiagOf, k0E7Diag] at hi
    have hi7 : i < 8 := by simpa using hi
    rcases ha with rfl | rfl
    all_goals interval_cases i
    all_goals decide
  · simp only [k0DiagOf, k0E8Diag, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
    simp only [k0DiagOf, k0E8Diag] at hi
    have hi7 : i < 9 := by simpa using hi
    rcases ha with rfl
    all_goals interval_cases i
    all_goals decide
  · simp only [k0DiagOf, k0F4Diag, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
    simp only [k0DiagOf, k0F4Diag] at hi
    have hi7 : i < 5 := by simpa using hi
    rcases ha with rfl
    all_goals interval_cases i
    all_goals decide

theorem tau0_perm (T : GGKacType) :
    (k0DiagOf T).tau0.Perm (List.range (k0DiagOf T).marks.length) := by
  cases T <;> decide

theorem tau0_mul_tau0 (T : GGKacType) :
    k0pMul (k0DiagOf T).tau0 (k0DiagOf T).tau0 = k0pId (k0DiagOf T).marks.length := by
  cases T <;> decide

theorem tau0_conj_mem_omega (T : GGKacType) {a : List ℕ} (ha : a ∈ (k0DiagOf T).omega) :
    k0pMul (k0DiagOf T).tau0 (k0pMul a (k0DiagOf T).tau0) ∈ (k0DiagOf T).omega := by
  cases T
  · simp only [k0DiagOf, k0E6Diag, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
    rcases ha with rfl | rfl | rfl
    all_goals decide
  · simp only [k0DiagOf, k0E7Diag, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
    rcases ha with rfl | rfl
    all_goals decide
  · simp only [k0DiagOf, k0E8Diag, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
    rcases ha with rfl
    all_goals decide
  · simp only [k0DiagOf, k0F4Diag, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
    rcases ha with rfl
    all_goals decide

theorem mem_k0VecsAux_of_sum {marks : List ℕ} (hm : ∀ m ∈ marks, 0 < m) {p : ℕ} {s : List ℕ}
    (hlen : s.length = marks.length)
    (hsum : (∑ i : Fin marks.length, marks.getD i 0 * s.getD i 0) = p) :
    s ∈ k0VecsAux marks p := by
  induction marks generalizing p s with
  | nil =>
      have hnil : s = [] := by
        cases s with
        | nil => rfl
        | cons _ _ => simp at hlen
      have hp : p = 0 := by simpa using hsum.symm
      subst hnil
      subst hp
      simp [k0VecsAux]
  | cons m ms ih =>
      have hm0 : 0 < m := hm m (by simp)
      have hslen : 0 < s.length := by rw [hlen]; simp
      obtain ⟨v, rest, hs⟩ : ∃ v rest, s = v :: rest := by
        cases s with
        | nil => simp at hslen
        | cons v rest => exact ⟨v, rest, rfl⟩
      subst hs
      have hrest_len : rest.length = ms.length := by simpa using hlen
      have hsum1 : m * v + (∑ i : Fin ms.length, ms.getD i 0 * rest.getD i 0) = p := by
        have h := hsum
        change (∑ i : Fin (ms.length + 1),
          (m :: ms).getD (i : ℕ) 0 * (v :: rest).getD (i : ℕ) 0) = p at h
        rw [Fin.sum_univ_succ] at h
        simpa [List.getD_cons_zero, List.getD_cons_succ, Fin.val_succ] using h
      have hsum2 : v * m + (∑ i : Fin ms.length, ms.getD i 0 * rest.getD i 0) = p := by
        rw [mul_comm]
        exact hsum1
      have hsum_rest : (∑ i : Fin ms.length, ms.getD i 0 * rest.getD i 0) = p - v * m := by
        omega
      have hvm : v * m ≤ p := by omega
      have hv_le : v ≤ p / m := (Nat.le_div_iff_mul_le hm0).mpr hvm
      have hv_mem : v ∈ List.range (p / m + 1) := by
        rw [List.mem_range]
        omega
      have hrest_mem : rest ∈ k0VecsAux ms (p - v * m) := by
        refine ih (fun x hx => hm x (by simp [hx])) hrest_len ?_
        rw [hsum_rest]
      unfold k0VecsAux
      rw [k0shape_mem_foldr_append]
      exact ⟨v, hv_mem, List.mem_map.mpr ⟨rest, hrest_mem, rfl⟩⟩


private theorem k0lstLex_irrefl : ∀ l : List ℕ, k0LexLtNat l l = false
  | [] => rfl
  | x :: xs => by
      simp only [k0LexLtNat, Nat.lt_irrefl, if_false]
      exact k0lstLex_irrefl xs

private theorem k0lstLex_asymm {x y : List ℕ} (h : k0LexLtNat x y = true) :
    k0LexLtNat y x = false := by
  induction x generalizing y with
  | nil => cases y <;> simp [k0LexLtNat] at h ⊢
  | cons a xs ih =>
      cases y with
      | nil => simp [k0LexLtNat] at h
      | cons b ys =>
          simp only [k0LexLtNat] at h ⊢
          by_cases hab : a < b
          · rw [if_pos hab] at h
            rw [if_neg (Nat.not_lt.mpr (Nat.le_of_lt hab)), if_pos hab]
          · rw [if_neg hab] at h
            by_cases hba : b < a
            · rw [if_pos hba] at h
              exact absurd h (by simp)
            · rw [if_neg hba] at h
              rw [if_neg hba, if_neg hab]
              exact ih h

private theorem k0lstLex_trich {x y : List ℕ} (h : k0LexLtNat x y = false) :
    x = y ∨ k0LexLtNat y x = true := by
  induction x generalizing y with
  | nil => cases y with
    | nil => exact Or.inl rfl
    | cons b ys => simp [k0LexLtNat] at h
  | cons a xs ih =>
      cases y with
      | nil => exact Or.inr (by simp [k0LexLtNat])
      | cons b ys =>
          simp only [k0LexLtNat] at h
          by_cases hab : a < b
          · rw [if_pos hab] at h
            exact absurd h (by simp)
          · rw [if_neg hab] at h
            by_cases hba : b < a
            · rw [if_pos hba] at h
              exact Or.inr (by simp only [k0LexLtNat, if_pos hba])
            · rw [if_neg hba] at h
              have hab' : a = b := by omega
              subst hab'
              rcases ih h with h' | h'
              · exact Or.inl (by rw [h'])
              · exact Or.inr (by simp only [k0LexLtNat, Nat.lt_irrefl, if_false, h'])

private theorem k0lstLex_trans {x y z : List ℕ} (h1 : k0LexLtNat x y = true)
    (h2 : k0LexLtNat y z = true) : k0LexLtNat x z = true := by
  induction x generalizing y z with
  | nil =>
      cases y <;> cases z <;> simp_all [k0LexLtNat]
  | cons a xs ih =>
      cases y with
      | nil => simp [k0LexLtNat] at h1
      | cons b ys =>
          cases z with
          | nil => simp [k0LexLtNat] at h2
          | cons c zs =>
              simp only [k0LexLtNat] at h1 h2 ⊢
              by_cases hab : a < b
              · rw [if_pos hab] at h1
                by_cases hbc : b < c
                · rw [if_pos hbc] at h2
                  simp only [if_pos (Nat.lt_trans hab hbc)]
                · rw [if_neg hbc] at h2
                  by_cases hcb : c < b
                  · rw [if_pos hcb] at h2
                    exact absurd h2 (by simp)
                  · rw [if_neg hcb] at h2
                    simp only [if_pos (by omega : a < c)]
              · rw [if_neg hab] at h1
                by_cases hba : b < a
                · rw [if_pos hba] at h1
                  exact absurd h1 (by simp)
                · rw [if_neg hba] at h1
                  have hab' : a = b := by omega
                  subst hab'
                  by_cases hbc : a < c
                  · rw [if_pos hbc] at h2
                    simp only [if_pos hbc]
                  · rw [if_neg hbc] at h2
                    by_cases hcb : c < a
                    · rw [if_pos hcb] at h2
                      exact absurd h2 (by simp)
                    · rw [if_neg hcb] at h2
                      simp only [if_neg hbc, if_neg hcb]
                      exact ih h1 h2

private theorem k0lstSortBy_perm (l : List (List ℕ)) :
    (k0SortBy k0LexLtNat l).Perm l := by
  rw [k0SortBy_eq_insertionSort]
  exact List.perm_insertionSort _ l

private theorem k0lstInsertBy_head_min (a : List ℕ) (l : List (List ℕ))
    (hmin : ∀ x ∈ l, k0LexLtNat x ((l.headD [])) = false) :
    (∀ x ∈ a :: l, k0LexLtNat x ((k0InsertBy k0LexLtNat a l).headD []) = false) ∧
      (k0InsertBy k0LexLtNat a l).headD [] ∈ a :: l := by
  induction l with
  | nil =>
      refine ⟨?_, by simp [k0InsertBy]⟩
      intro x hx
      rw [List.mem_singleton] at hx
      rw [hx]
      exact k0lstLex_irrefl _
  | cons b bs ih =>
      by_cases hab : k0LexLtNat a b = true
      · rw [k0InsertBy, if_pos hab]
        refine ⟨?_, by simp⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact k0lstLex_irrefl _
        · have hxb : k0LexLtNat x b = false := hmin x (by simp [hx])
          rcases k0lstLex_trich hxb with rfl | hb
          · exact k0lstLex_asymm hab
          · exact k0lstLex_asymm (k0lstLex_trans hab hb)
      · have hab' : k0LexLtNat a b = false := by simpa using hab
        rw [k0InsertBy, if_neg hab]
        refine ⟨?_, by simp⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hab'
        · exact hmin x (by simp [hx])

private theorem k0lstSortBy_head_min (l : List (List ℕ)) (hne : l ≠ []) :
    (k0SortBy k0LexLtNat l).headD [] ∈ l ∧
      ∀ x ∈ l, k0LexLtNat x ((k0SortBy k0LexLtNat l).headD []) = false := by
  induction l with
  | nil => exact absurd rfl hne
  | cons a as ih =>
      by_cases has : as = []
      · subst has
        have hstep : (k0SortBy k0LexLtNat [a]).headD [] = a := rfl
        rw [hstep]
        refine ⟨by simp, ?_⟩
        intro x hx
        rw [List.mem_singleton] at hx
        rw [hx]
        exact k0lstLex_irrefl _
      · have hih := ih has
        have hperm : (k0SortBy k0LexLtNat as).Perm as := k0lstSortBy_perm as
        have hmin' : ∀ x ∈ (k0SortBy k0LexLtNat as),
            k0LexLtNat x ((k0SortBy k0LexLtNat as).headD []) = false := by
          intro x hx
          exact hih.2 x (hperm.mem_iff.mp hx)
        have hins := k0lstInsertBy_head_min a (k0SortBy k0LexLtNat as) hmin'
        have hstep : (k0SortBy k0LexLtNat (a :: as)).headD []
            = (k0InsertBy k0LexLtNat a (k0SortBy k0LexLtNat as)).headD [] := rfl
        rw [hstep]
        refine ⟨?_, ?_⟩
        · rcases List.mem_cons.mp hins.2 with h | h
          · exact List.mem_cons.mpr (Or.inl h)
          · exact List.mem_cons.mpr (Or.inr (hperm.mem_iff.mp h))
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hins.1 x (List.mem_cons.mpr (Or.inl rfl))
          · exact hins.1 x (List.mem_cons.mpr (Or.inr (hperm.mem_iff.mpr hx)))

theorem exists_omega_k0OrbMin (T : GGKacType) {s : List ℕ}
    (hs : s.length = (k0DiagOf T).marks.length) :
    ∃ a ∈ (k0DiagOf T).omega, k0OrbMin (k0DiagOf T) s = k0pAct a s ∧
      k0OrbMin (k0DiagOf T) (k0OrbMin (k0DiagOf T) s) = k0OrbMin (k0DiagOf T) s := by
  set D := k0DiagOf T with hD
  set m := k0OrbMin D s with hm
  set L := D.omega.map (fun a => k0pAct a s) with hL
  have hmdef : m = (k0SortBy k0LexLtNat L).headD [] := by rw [hm]; rfl
  have hLne : L ≠ [] := by
    intro h
    have hmem : k0pAct (k0pId D.marks.length) s ∈ L :=
      List.mem_map.mpr ⟨k0pId D.marks.length, one_mem_omega T, rfl⟩
    rw [h] at hmem
    exact List.not_mem_nil hmem
  have hmin := k0lstSortBy_head_min L hLne
  obtain ⟨a, ha, ham⟩ := List.mem_map.mp hmin.1
  have ham' : m = k0pAct a s := by rw [hmdef, ham]
  refine ⟨a, ha, ham', ?_⟩
  set L' := D.omega.map (fun b => k0pAct b m) with hL'
  have hL'ne : L' ≠ [] := by
    intro h
    have hmem : k0pAct (k0pId D.marks.length) m ∈ L' :=
      List.mem_map.mpr ⟨k0pId D.marks.length, one_mem_omega T, rfl⟩
    rw [h] at hmem
    exact List.not_mem_nil hmem
  have hmin' := k0lstSortBy_head_min L' hL'ne
  have hsub : ∀ x ∈ L', x ∈ L := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    rw [ham']
    rw [k0pAct_mul (omega_perm T ha) (omega_perm T hb) hs]
    exact List.mem_map.mpr ⟨k0pMul b a, mul_mem_omega T hb ha, rfl⟩
  have hm'lt : k0LexLtNat ((k0SortBy k0LexLtNat L').headD []) m = false :=
    hmin.2 _ (hsub _ hmin'.1)
  have hmL' : m ∈ L' := by
    have hlenm : m.length = D.marks.length := by rw [ham', k0pAct_length]; exact hs
    have h : k0pAct (k0pId D.marks.length) m ∈ L' :=
      List.mem_map.mpr ⟨k0pId D.marks.length, one_mem_omega T, rfl⟩
    rwa [k0pAct_id hlenm] at h
  have hltm' : k0LexLtNat m ((k0SortBy k0LexLtNat L').headD []) = false :=
    hmin'.2 m hmL'
  have hgoal : (k0SortBy k0LexLtNat L').headD [] = m := by
    rcases k0lstLex_trich hm'lt with h | h
    · exact h
    · rw [h] at hltm'
      exact absurd hltm' (by simp)
  unfold k0OrbMin
  exact hgoal


private theorem k0lstBaseAux_exists {rho0 s : List ℕ} :
    ∀ {l : List (List ℕ)} {a : List ℕ}, a ∈ l → k0pAct (k0pMul a rho0) s = s →
      ∃ base, k0BaseAux rho0 s l = some base ∧ (∃ a0 ∈ l, base = k0pMul a0 rho0) ∧
        k0pAct base s = s := by
  intro l
  induction l with
  | nil => intro a ha; simp at ha
  | cons a0 rest ih =>
      intro a ha has
      simp only [k0BaseAux]
      split
      · rename_i hact
        exact ⟨k0pMul a0 rho0, rfl, ⟨a0, by simp, rfl⟩, hact⟩
      · rename_i hnact
        rcases List.mem_cons.mp ha with rfl | ha
        · exact absurd has hnact
        · obtain ⟨base, hbase, ⟨a1, ha1, heq⟩, hact⟩ := ih ha has
          exact ⟨base, hbase, ⟨a1, by simp [ha1], heq⟩, hact⟩

theorem exists_k0KacBase {D : K0Diag} {rho0 s a : List ℕ} (ha : a ∈ D.omega)
    (has : k0pAct (k0pMul a rho0) s = s) :
    ∃ base, k0KacBase D rho0 s = some base ∧ (∃ a0 ∈ D.omega, base = k0pMul a0 rho0) ∧
      k0pAct base s = s := by
  obtain ⟨base, hbase, hex, hact⟩ := k0lstBaseAux_exists ha has
  exact ⟨base, hbase, hex, hact⟩


private theorem k0lstRepsAux_spec (stab : List (List ℕ)) (base : List ℕ) :
    ∀ (as : List (List ℕ)) (fuel : ℕ) (seenF acc pre : List (List ℕ)),
      stab = pre ++ as → as.length < fuel →
      (∀ f ∈ seenF, ∃ r ∈ acc, ∃ b ∈ stab, f = k0pMul b (k0pMul r (k0pInv b))) →
      (∀ x ∈ pre, k0pMul x base ∈ acc ∨ ∃ r ∈ acc, ∃ b ∈ stab,
        k0pMul x base = k0pMul b (k0pMul r (k0pInv b))) →
      (∀ y ∈ acc, y ∈ k0RepsAux stab base fuel as seenF acc) ∧
      (∀ f ∈ seenF, ∃ r ∈ k0RepsAux stab base fuel as seenF acc, ∃ b ∈ stab,
        f = k0pMul b (k0pMul r (k0pInv b))) ∧
      (∀ x ∈ pre ++ as, k0pMul x base ∈ k0RepsAux stab base fuel as seenF acc ∨
        ∃ r ∈ k0RepsAux stab base fuel as seenF acc, ∃ b ∈ stab,
          k0pMul x base = k0pMul b (k0pMul r (k0pInv b))) := by
  intro as
  induction as with
  | nil =>
      intro fuel seenF acc pre _ _ hseen hpre
      have hout : k0RepsAux stab base fuel [] seenF acc = acc := by cases fuel <;> rfl
      rw [hout]
      exact ⟨fun y hy => hy, hseen, by simpa using hpre⟩
  | cons a as ih =>
      intro fuel seenF acc pre hstab hlen hseen hpre
      cases fuel with
      | zero => simp at hlen
      | succ fuel =>
          by_cases hmem : k0pMul a base ∈ seenF
          · have hstab' : stab = (pre ++ [a]) ++ as := by rw [hstab]; simp [List.append_assoc]
            have hlen' : as.length < fuel := by simpa using hlen
            have hpre' : ∀ x ∈ pre ++ [a], k0pMul x base ∈ acc ∨ ∃ r ∈ acc, ∃ b ∈ stab,
                k0pMul x base = k0pMul b (k0pMul r (k0pInv b)) := by
              intro x hx
              rcases List.mem_append.mp hx with hx | hx
              · exact hpre x hx
              · rw [List.mem_singleton] at hx
                rw [hx]
                exact Or.inr (hseen _ hmem)
            have hrec := ih fuel seenF acc (pre ++ [a]) hstab' hlen' hseen hpre'
            have hout : k0RepsAux stab base (fuel + 1) (a :: as) seenF acc
                = k0RepsAux stab base fuel as seenF acc := by
              rw [k0RepsAux, if_pos hmem]
            rw [hout]
            exact ⟨hrec.1, hrec.2.1, by simpa [List.append_assoc] using hrec.2.2⟩
          · have hstab' : stab = (pre ++ [a]) ++ as := by rw [hstab]; simp [List.append_assoc]
            have hlen' : as.length < fuel := by simpa using hlen
            have hseen' : ∀ f ∈ seenF ++ stab.map
                  (fun b => k0pMul b (k0pMul (k0pMul a base) (k0pInv b))),
                ∃ r ∈ acc ++ [k0pMul a base], ∃ b ∈ stab,
                  f = k0pMul b (k0pMul r (k0pInv b)) := by
              intro f hf
              rcases List.mem_append.mp hf with hf | hf
              · obtain ⟨r, hr, b, hb, heq⟩ := hseen f hf
                exact ⟨r, List.mem_append.mpr (Or.inl hr), b, hb, heq⟩
              · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hf
                exact ⟨k0pMul a base, List.mem_append.mpr (Or.inr (by simp)), b, hb, rfl⟩
            have hpre' : ∀ x ∈ pre ++ [a], k0pMul x base ∈ acc ++ [k0pMul a base] ∨
                ∃ r ∈ acc ++ [k0pMul a base], ∃ b ∈ stab,
                  k0pMul x base = k0pMul b (k0pMul r (k0pInv b)) := by
              intro x hx
              rcases List.mem_append.mp hx with hx | hx
              · rcases hpre x hx with h | ⟨r, hr, b, hb, heq⟩
                · exact Or.inl (List.mem_append.mpr (Or.inl h))
                · exact Or.inr ⟨r, List.mem_append.mpr (Or.inl hr), b, hb, heq⟩
              · rw [List.mem_singleton] at hx
                rw [hx]
                exact Or.inl (List.mem_append.mpr (Or.inr (by simp)))
            have hrec := ih fuel _ _ (pre ++ [a]) hstab' hlen' hseen' hpre'
            have hout : k0RepsAux stab base (fuel + 1) (a :: as) seenF acc
                = k0RepsAux stab base fuel as
                    (seenF ++ stab.map (fun b => k0pMul b (k0pMul (k0pMul a base) (k0pInv b))))
                    (acc ++ [k0pMul a base]) := by
              rw [k0RepsAux, if_neg hmem]
            rw [hout]
            refine ⟨?_, ?_, by simpa [List.append_assoc] using hrec.2.2⟩
            · intro y hy
              exact hrec.1 y (List.mem_append.mpr (Or.inl hy))
            · intro f hf
              exact hrec.2.1 f (List.mem_append.mpr (Or.inl hf))

theorem mem_or_conj_k0Reps {stab : List (List ℕ)} {base x : List ℕ} (hx : x ∈ stab) :
    k0pMul x base ∈ k0Reps stab base ∨ ∃ r ∈ k0Reps stab base, ∃ b ∈ stab,
      k0pMul x base = k0pMul b (k0pMul r (k0pInv b)) := by
  have h := k0lstRepsAux_spec stab base stab (stab.length + 1) [] [] []
    (by simp) (by simp) (by simp) (by simp)
  exact h.2.2 x (by simpa using hx)

theorem ggKacValid_k0Datum {lab : LargeEvenLabel} {p : ℕ} {T : GGKacType} {tw : Bool}
    (hT : ggKacTypeOfLabel lab = some (T, tw)) (hp : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)
    {s base rho : List ℕ} (hs : s ∈ k0VecsAux (k0DiagOf T).marks p)
    (hmin : k0OrbMin (k0DiagOf T) s = s)
    (hbase : k0KacBase (k0DiagOf T)
      (k0Rho0 (k0DiagOf T) tw (if p ∣ 2 ^ lab.n - 1 then 1 else 2)) s = some base)
    (hrho : rho ∈ k0Reps (((k0DiagOf T).omega).filter (fun w => decide (k0pAct w s = s))) base) :
    GGKacValid lab p (k0Datum (k0DiagOf T) s rho (if p ∣ 2 ^ lab.n - 1 then 1 else 2) lab.n
      (((k0DiagOf T).omega.filter (fun w => decide (k0pAct w s = s))).length)) := by
  set d := (if p ∣ 2 ^ lab.n - 1 then 1 else 2) with hd
  have hraw : k0Datum (k0DiagOf T) s rho d lab.n
        (((k0DiagOf T).omega.filter (fun w => decide (k0pAct w s = s))).length) ∈
      k0RawDatums (k0DiagOf T) tw p lab.n d := by
    unfold k0RawDatums
    rw [k0shape_mem_foldr_append]
    refine ⟨s, ?_, ?_⟩
    · rw [List.mem_filter]
      exact ⟨hs, by rw [decide_eq_true_eq]; exact hmin⟩
    · have hb : k0KacBase (k0DiagOf T) (k0Rho0 (k0DiagOf T) tw d) s = some base := hbase
      unfold k0DatumsOf
      rw [hb]
      rw [List.mem_map]
      exact ⟨rho, hrho, rfl⟩
  refine ⟨T, tw, hT, ?_⟩
  by_cases h1 : p ∣ 2 ^ lab.n - 1
  · have hd1 : d = 1 := by rw [hd]; simp [h1]
    rw [k0shape_table_branch1 T tw p lab.n h1, hd1]
    rw [hd1] at hraw
    exact (k0shape_sortDatums_perm _).mem_iff.mpr hraw
  · by_cases h2 : p ∣ 2 ^ lab.n + 1
    · have hd2 : d = 2 := by rw [hd]; simp [h1]
      rw [k0shape_table_branch2 T tw p lab.n h1 h2, hd2]
      rw [hd2] at hraw
      exact (k0shape_sortDatums_perm _).mem_iff.mpr hraw
    · exact absurd (hp.resolve_left h1) h2

end CFSG.StandardType.GGK0MarkedKacIface1587

end
