module

public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableClDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggTUCl_eq_of_length_filter_le_one {N : ℕ} {P : ℕ → Prop} [DecidablePred P]
    (h : ((List.range N).filter (fun j => decide (P j))).length ≤ 1) {i j : ℕ} (hi : i < N)
    (hj : j < N) (hPi : P i) (hPj : P j) : i = j := by
  by_contra hne
  have hmem_i : i ∈ (List.range N).filter (fun j => decide (P j)) := by
    simp [hi, hPi]
  have hmem_j : j ∈ (List.range N).filter (fun j => decide (P j)) := by
    simp [hj, hPj]
  obtain ⟨a, ha, hia⟩ := List.mem_iff_getElem.mp hmem_i
  obtain ⟨b, hb, hjb⟩ := List.mem_iff_getElem.mp hmem_j
  have hab : a ≠ b := by
    rintro rfl
    exact hne (hia.symm.trans hjb)
  omega

private lemma ggTUClC_ord_eq_one_or_two {p n : ℕ} (h : ggMultOrd p n ≠ 0) :
    ggMultOrd p n = 1 ∨ ggMultOrd p n = 2 := by
  unfold ggMultOrd at h ⊢
  by_cases h1 : p ∣ 2 ^ n - 1
  · simp [h1]
  · by_cases h2 : p ∣ 2 ^ n + 1
    · simp [h1, h2]
    · simp [h1, h2] at h

private lemma ggTUClC_dvd_of_ord_eq_one {p n : ℕ} (h : ggMultOrd p n = 1) :
    p ∣ 2 ^ n - 1 := by
  unfold ggMultOrd at h
  by_cases h1 : p ∣ 2 ^ n - 1
  · exact h1
  · by_cases h2 : p ∣ 2 ^ n + 1 <;> simp_all

private lemma ggTUClC_dvd_of_ord_eq_two {p n : ℕ} (h : ggMultOrd p n = 2) :
    p ∣ 2 ^ n + 1 := by
  unfold ggMultOrd at h
  by_cases h1 : p ∣ 2 ^ n - 1
  · simp [h1] at h
  · by_cases h2 : p ∣ 2 ^ n + 1
    · exact h2
    · simp [h1, h2] at h

private lemma ggTUClC_mem_of_eq_singleton {α : Type*} {l : List α} {o : α} (h : l = [o]) :
    o ∈ l := by
  rw [h]
  exact List.mem_singleton.mpr rfl

private lemma ggTUClC_getD_mem {l : List ℕ} {k : ℕ} (hk : k < l.length) : l.getD k 0 ∈ l := by
  have h : l.getD k 0 = l[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    rfl
  rw [h]
  exact List.getElem_mem hk

private lemma ggTUClC_sum_eq_of_unique_pos {l : List ℕ}
    (h : ∀ i j, i < l.length → j < l.length → 0 < l.getD i 0 → 0 < l.getD j 0 → i = j) :
    l.sum = 0 ∨ ∃ k, k < l.length ∧ 0 < l.getD k 0 ∧ l.sum = l.getD k 0 := by
  induction l with
  | nil => exact Or.inl rfl
  | cons a t ih =>
      by_cases ha : 0 < a
      · have ht : ∀ i, i < t.length → t.getD i 0 = 0 := by
          intro i hi
          by_contra hne
          have hpi : 0 < t.getD i 0 := Nat.pos_of_ne_zero hne
          have h0 := h (i + 1) 0 (by simp [hi]) (by simp)
            (by simpa [List.getD_cons_succ] using hpi) (by simpa using ha)
          omega
        have hsum0 : t.sum = 0 := by
          rw [List.sum_eq_zero_iff_forall_eq_nat]
          intro x hx
          obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
          have hget : t.getD i 0 = t[i] := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
            rfl
          rw [← hix, ← hget]
          exact ht i hi
        exact Or.inr ⟨0, by simp, by simpa using ha, by simp [hsum0]⟩
      · have ha0 : a = 0 := by omega
        have h' : ∀ i j, i < t.length → j < t.length → 0 < t.getD i 0 →
            0 < t.getD j 0 → i = j := by
          intro i j hi hj hpi hpj
          have h0 := h (i + 1) (j + 1) (by simp [hi]) (by simp [hj])
            (by simpa [List.getD_cons_succ] using hpi)
            (by simpa [List.getD_cons_succ] using hpj)
          omega
        rcases ih h' with h0 | ⟨k, hk, hpk, hsum⟩
        · exact Or.inl (by simp [ha0, h0])
        · exact Or.inr ⟨k + 1, by simp [hk], by simpa [List.getD_cons_succ] using hpk,
            by simp [ha0, hsum, List.getD_cons_succ]⟩

private lemma ggTUClC_sum_eq_getD_of_unique_pos {l : List ℕ} {k : ℕ} (hk : k < l.length)
    (hpos : 0 < l.getD k 0)
    (huniq : ∀ i j, i < l.length → j < l.length → 0 < l.getD i 0 → 0 < l.getD j 0 → i = j) :
    l.sum = l.getD k 0 := by
  rcases ggTUClC_sum_eq_of_unique_pos huniq with h0 | ⟨k', hk', hpk', hsum⟩
  · have hle : l.getD k 0 ≤ l.sum :=
      List.single_le_sum (fun x _ => Nat.zero_le x) (l.getD k 0) (ggTUClC_getD_mem hk)
    omega
  · have hkk : k' = k := huniq k' k hk' hk hpk' hpos
    rw [hkk] at hsum
    omega

private lemma ggTUClC_sum_le_one {l : List ℕ}
    (huniq : ∀ i j, i < l.length → j < l.length → 0 < l.getD i 0 → 0 < l.getD j 0 → i = j)
    (hno : ∀ k, k < l.length → l.getD k 0 < 2) : l.sum ≤ 1 := by
  rcases ggTUClC_sum_eq_of_unique_pos huniq with h0 | ⟨k, hk, hpos, hsum⟩
  · omega
  · have := hno k hk
    omega

private lemma ggTUClC_row_A {p n m : ℕ} (hm : 2 ≤ m) (hdvd : p ∣ 2 ^ n - 1) :
    GGTablePRow p ⟨.A, m, n⟩ ⟨.C, m + 1, n⟩ := by
  unfold GGTablePRow
  simp [hdvd, hm]

private lemma ggTUClC_row_twA {p n m : ℕ} (hm : 2 ≤ m) (hdvd : p ∣ 2 ^ n + 1) :
    GGTablePRow p ⟨.twA, m, n⟩ ⟨.C, m + 1, n⟩ := by
  unfold GGTablePRow
  simp [hdvd, hm]

private lemma ggTUClC_row_C {p n m : ℕ} (hm : 2 ≤ m) (hdvd : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) :
    GGTablePRow p ⟨.C, m, n⟩ ⟨.C, m + 1, n⟩ := by
  unfold GGTablePRow
  simp [hdvd, hm]

private lemma ggTUClC_row_B2der : GGTablePRow 3 ⟨.B2der, 0, 1⟩ ⟨.C, 3, 1⟩ := by
  unfold GGTablePRow
  simp

private lemma ggTUClC_lambda2_A {m n : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m) :
    LargeEvenInLambda2 ⟨.A, m, n⟩ := by
  show 1 ≤ n ∧ (1 ≤ m ∧ (m = 1 → 2 ≤ n))
  exact ⟨hn, by omega, by omega⟩

private lemma ggTUClC_lambda2_C {m n : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m) (hmn : m = 2 → 2 ≤ n) :
    LargeEvenInLambda2 ⟨.C, m, n⟩ := by
  show 1 ≤ n ∧ (2 ≤ m ∧ (m = 2 → 2 ≤ n))
  exact ⟨hn, hm, hmn⟩

private lemma ggTUClC_lambda2_twA {m n : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m) (hmn : m = 2 → 2 ≤ n) :
    LargeEvenInLambda2 ⟨.twA, m, n⟩ := by
  show 1 ≤ n ∧ (2 ≤ m ∧ (m = 2 → 2 ≤ n))
  exact ⟨hn, hm, hmn⟩

private lemma ggTUClC_lambda2_B2der : LargeEvenInLambda2 ⟨.B2der, 0, 1⟩ := by
  show 1 ≤ 1 ∧ (0 = 0 ∧ 1 = 1)
  norm_num

private lemma ggTUClC_blockA_one {r n : ℕ} :
    ggMultBlockA r n 1 = ⟨⟨.A, r, n⟩, decide (¬ (r = 1 ∧ n = 1))⟩ := by
  simp [ggMultBlockA]

private lemma ggTUClC_blockA_two {r n : ℕ} (hr : 2 ≤ r) :
    ggMultBlockA r n 2 = ⟨⟨.twA, r, n⟩, decide (¬ (r = 2 ∧ n = 1))⟩ := by
  simp [ggMultBlockA, hr]

private lemma ggTUClC_blockA_two' {r n : ℕ} (hr : ¬ 2 ≤ r) :
    ggMultBlockA r n 2 = ⟨⟨.A, 1, n⟩, decide (¬ (n = 1))⟩ := by
  simp [ggMultBlockA, hr]

private lemma ggTUClC_huniqR {p n d m0 : ℕ} {rest : List ℕ}
    (hlenR : rest.length = (p - 1) / 2)
    (hrZ : (ggMultDatumC p n d (m0 :: rest)).rZ ≤ 1) :
    ∀ i j, i < rest.length → j < rest.length → 0 < rest.getD i 0 → 0 < rest.getD j 0 → i = j := by
  simp only [ggMultDatumC] at hrZ
  have huniq : ∀ i j, i < (p - 1) / 2 + 1 → j < (p - 1) / 2 + 1 → 1 ≤ i → 1 ≤ j →
      0 < (m0 :: rest).getD i 0 → 0 < (m0 :: rest).getD j 0 → i = j := by
    intro i j hi hj hi1 hj1 hpi hpj
    exact ggTUCl_eq_of_length_filter_le_one hrZ hi hj ⟨hi1, hpi⟩ ⟨hj1, hpj⟩
  intro i j hi hj hpi hpj
  have h' := huniq (i + 1) (j + 1) (by omega) (by omega) (by omega) (by omega)
    (by simpa [List.getD_cons_succ] using hpi)
    (by simpa [List.getD_cons_succ] using hpj)
  omega

private lemma ggTUClC_zero_orbit {r p n d : ℕ} {m : List ℕ} {o : GGKacOrbit}
    (hlen : m.length = (p - 1) / 2 + 1) (hsum : m.sum = r)
    (hDo : (ggMultDatumC p n d m).orbits = [o])
    (hrZ : (ggMultDatumC p n d m).rZ ≤ 1) (hm0 : m.headD 0 = 0) :
    ∃ a, r = a ∧ 2 ≤ a ∧ o = ggMultBlockA (a - 1) n d := by
  cases m with
  | nil => simp at hlen
  | cons m0 rest =>
    have hlenR : rest.length = (p - 1) / 2 := by simpa using hlen
    have hsumR : r = m0 + rest.sum := by simpa using hsum.symm
    have huniqR := ggTUClC_huniqR hlenR hrZ
    simp only [List.headD_cons] at hm0
    subst hm0
    simp only [ggMultDatumC] at hDo
    rcases List.append_eq_singleton_iff.mp hDo with ⟨-, horbJ⟩ | ⟨horb0, -⟩
    · obtain ⟨j, hj, hfj⟩ := List.mem_map.mp (ggTUClC_mem_of_eq_singleton horbJ)
      obtain ⟨hjrange, hpj⟩ := List.mem_filter.mp hj
      rw [List.mem_range] at hjrange
      have hpj' : 1 ≤ j ∧ 2 ≤ (0 :: rest).getD j 0 := by simpa using hpj
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have hk : k < rest.length := by omega
      have hpk : 2 ≤ rest.getD k 0 := by simpa [List.getD_cons_succ] using hpj'.2
      have hsumk : rest.sum = rest.getD k 0 :=
        ggTUClC_sum_eq_getD_of_unique_pos hk (by omega) huniqR
      simp only [List.getD_cons_succ] at hfj
      exact ⟨rest.getD k 0, by omega, hpk, hfj.symm⟩
    · exact absurd horb0 (by simp)

private lemma ggTUClC_zero_one {r p n : ℕ} {m : List ℕ} {o : GGKacOrbit}
    (hord : ggMultOrd p n = 1) (hlen : m.length = (p - 1) / 2 + 1) (hsum : m.sum = r)
    (hDo : (ggMultDatumC p n (ggMultOrd p n) m).orbits = [o])
    (hrZ : (ggMultDatumC p n (ggMultOrd p n) m).rZ ≤ 1) (hn : 1 ≤ n)
    (hm0 : m.headD 0 = 0) (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨.C, r, n⟩ := by
  have hdvd : p ∣ 2 ^ n - 1 := ggTUClC_dvd_of_ord_eq_one hord
  rw [hord] at hDo hrZ
  obtain ⟨a, hr, ha, ho⟩ := ggTUClC_zero_orbit hlen hsum hDo hrZ hm0
  rw [hr]
  have hlab : o.lab = ⟨.A, a - 1, n⟩ := by rw [ho, ggTUClC_blockA_one]
  rcases Nat.lt_or_ge (a - 1) 2 with hlt | hge
  · have ha1 : a - 1 = 1 := by omega
    rw [ha1] at hlab
    exact absurd (by rw [hlab]; exact Or.inl ⟨rfl, rfl⟩) hrk
  · refine ⟨?_, ?_⟩
    · rw [hlab]
      exact ggTUClC_lambda2_A hn hge
    · rw [hlab]
      have hmeq : a - 1 + 1 = a := by omega
      rw [← hmeq]
      exact ggTUClC_row_A hge hdvd

private lemma ggTUClC_zero_two {r p n : ℕ} {m : List ℕ} {o : GGKacOrbit}
    (hord : ggMultOrd p n = 2) (hlen : m.length = (p - 1) / 2 + 1) (hsum : m.sum = r)
    (hDo : (ggMultDatumC p n (ggMultOrd p n) m).orbits = [o])
    (hrZ : (ggMultDatumC p n (ggMultOrd p n) m).rZ ≤ 1) (hn : 1 ≤ n)
    (hm0 : m.headD 0 = 0) (hqs : o.qs = true) (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨.C, r, n⟩ := by
  have hdvd : p ∣ 2 ^ n + 1 := ggTUClC_dvd_of_ord_eq_two hord
  rw [hord] at hDo hrZ
  obtain ⟨a, hr, ha, ho⟩ := ggTUClC_zero_orbit hlen hsum hDo hrZ hm0
  rw [hr]
  by_cases hge : 2 ≤ a - 1
  · have ho' : o = ⟨⟨.twA, a - 1, n⟩, decide (¬ (a - 1 = 2 ∧ n = 1))⟩ := by
      rw [ho, ggTUClC_blockA_two hge]
    have hlab : o.lab = ⟨.twA, a - 1, n⟩ := by rw [ho']
    have hqs' : decide (¬ (a - 1 = 2 ∧ n = 1)) = true := by
      rw [ho'] at hqs
      exact hqs
    have hmn : a - 1 = 2 → 2 ≤ n := by
      intro h2
      have hnot : ¬ (a - 1 = 2 ∧ n = 1) := of_decide_eq_true hqs'
      omega
    refine ⟨?_, ?_⟩
    · rw [hlab]
      exact ggTUClC_lambda2_twA hn hge hmn
    · rw [hlab]
      have hmeq : a - 1 + 1 = a := by omega
      rw [← hmeq]
      exact ggTUClC_row_twA hge hdvd
  · have ho' : o = ⟨⟨.A, 1, n⟩, decide (¬ (n = 1))⟩ := by rw [ho, ggTUClC_blockA_two' hge]
    exact absurd (by rw [ho']; exact Or.inl ⟨rfl, rfl⟩) hrk

private lemma ggTUClC_one {r p n d : ℕ} {m : List ℕ} {o : GGKacOrbit}
    (hlen : m.length = (p - 1) / 2 + 1)
    (hDo : (ggMultDatumC p n d m).orbits = [o]) (hm0 : m.headD 0 = 1)
    (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨.C, r, n⟩ := by
  cases m with
  | nil => simp at hlen
  | cons m0 rest =>
    simp only [ggMultDatumC] at hDo
    simp only [List.headD_cons] at hm0
    subst hm0
    rcases List.append_eq_singleton_iff.mp hDo with ⟨horb0, -⟩ | ⟨horb0, -⟩
    · exact absurd horb0 (by simp)
    · have hmem : o ∈ [⟨⟨.A, 1, n⟩, decide (¬ (n = 1))⟩] :=
        ggTUClC_mem_of_eq_singleton horb0
      have hlab : o.lab = ⟨.A, 1, n⟩ := by
        have hxo : o = _ := List.mem_singleton.mp hmem
        rw [hxo]
      exact absurd (by rw [hlab]; exact Or.inl ⟨rfl, rfl⟩) hrk

private lemma ggTUClC_ne_one_of_hr2 {r p : ℕ} {rest : List ℕ} (hr2 : r = 2 → 2 ≤ 1)
    (hlenR : rest.length = (p - 1) / 2) (hsumR : r = 2 + rest.sum) : p ≠ 1 := by
  intro hp
  have hlen0 : rest.length = 0 := by rw [hp] at hlenR; omega
  have hsum0 : rest.sum = 0 := by
    rw [List.sum_eq_zero_iff_forall_eq_nat]
    intro x hx
    rw [List.length_eq_zero_iff.mp hlen0] at hx
    simpa using hx
  have hr2' : r = 2 := by omega
  have := hr2 hr2'
  omega

private lemma ggTUClC_eq_three_of_dvd {p : ℕ} (hp1 : p ≠ 1) (hpdvd : p ∣ 3) : p = 3 := by
  have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hpdvd
  interval_cases p
  · norm_num at hpdvd
  · exact absurd rfl hp1
  · norm_num at hpdvd
  · rfl

private lemma ggTUClC_tail_sum_le_one {p n d m0 : ℕ} {rest : List ℕ}
    (hlenR : rest.length = (p - 1) / 2)
    (hrZ : (ggMultDatumC p n d (m0 :: rest)).rZ ≤ 1)
    (h : List.map (fun j => ggMultBlockA ((m0 :: rest).getD j 0 - 1) n d)
      (List.filter (fun j => decide (1 ≤ j ∧ 2 ≤ (m0 :: rest).getD j 0))
        (List.range ((p - 1) / 2 + 1))) = []) :
    rest.sum ≤ 1 := by
  have hmap := List.map_eq_nil_iff.mp h
  rw [List.filter_eq_nil_iff] at hmap
  have hno : ∀ k, k < rest.length → rest.getD k 0 < 2 := by
    intro k hk
    have h4 : ¬ (1 ≤ k + 1 ∧ 2 ≤ (m0 :: rest).getD (k + 1) 0) := by
      have := hmap (k + 1) (by rw [List.mem_range]; omega)
      simpa using this
    rw [List.getD_cons_succ] at h4
    omega
  exact ggTUClC_sum_le_one (ggTUClC_huniqR hlenR hrZ) hno

private lemma ggTUClC_two_one {r p n : ℕ} {m : List ℕ} {o : GGKacOrbit}
    (hd : ggMultOrd p n = 1 ∨ ggMultOrd p n = 2) (hlen : m.length = (p - 1) / 2 + 1)
    (hsum : m.sum = r)
    (hDo : (ggMultDatumC p n (ggMultOrd p n) m).orbits = [o])
    (hrZ : (ggMultDatumC p n (ggMultOrd p n) m).rZ ≤ 1)
    (hr2 : r = 2 → 2 ≤ n) (hn1 : n = 1) (hm0 : m.headD 0 = 2) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨.C, r, n⟩ := by
  cases m with
  | nil => simp at hlen
  | cons m0 rest =>
    have hlenR : rest.length = (p - 1) / 2 := by simpa using hlen
    have hsumR : r = m0 + rest.sum := by simpa using hsum.symm
    have huniqR := ggTUClC_huniqR hlenR hrZ
    simp only [ggMultDatumC] at hDo
    rw [List.headD_cons] at hm0
    subst hm0
    subst hn1
    rcases List.append_eq_singleton_iff.mp hDo with ⟨horb0, -⟩ | ⟨horb0, horbJ⟩
    · exact absurd horb0 (by simp)
    · have hmem : o ∈ [⟨⟨.B2der, 0, 1⟩, true⟩] := ggTUClC_mem_of_eq_singleton horb0
      have hlab : o.lab = ⟨.B2der, 0, 1⟩ := by
        have hxo : o = _ := List.mem_singleton.mp hmem
        rw [hxo]
      have hrest : rest.sum ≤ 1 := ggTUClC_tail_sum_le_one hlenR hrZ horbJ
      have hp1 : p ≠ 1 := ggTUClC_ne_one_of_hr2 hr2 hlenR hsumR
      have hpdvd : p ∣ 3 := by
        rcases hd with h1 | h2
        · have h1' : p ∣ 1 := by simpa using ggTUClC_dvd_of_ord_eq_one h1
          exact absurd (Nat.dvd_one.mp h1') hp1
        · simpa using ggTUClC_dvd_of_ord_eq_two h2
      have hp3 : p = 3 := ggTUClC_eq_three_of_dvd hp1 hpdvd
      have hr3 : r = 3 := by
        have hne : r ≠ 2 := by
          intro h
          have := hr2 h
          omega
        omega
      subst hp3
      refine ⟨?_, ?_⟩
      · rw [hlab]
        exact ggTUClC_lambda2_B2der
      · rw [hlab, hr3]
        exact ggTUClC_row_B2der

private lemma ggTUClC_c_row {r p n : ℕ} {m : List ℕ} {o : GGKacOrbit}
    (hd : ggMultOrd p n = 1 ∨ ggMultOrd p n = 2) (hlen : m.length = (p - 1) / 2 + 1)
    (hsum : m.sum = r)
    (hDo : (ggMultDatumC p n (ggMultOrd p n) m).orbits = [o])
    (hrZ : (ggMultDatumC p n (ggMultOrd p n) m).rZ ≤ 1) (hn : 1 ≤ n)
    (hm0 : 2 ≤ m.headD 0) (hne : ¬ (m.headD 0 = 2 ∧ n = 1))
    (hX : o.lab ≠ ⟨.C, r, n⟩) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨.C, r, n⟩ := by
  cases m with
  | nil => simp at hlen
  | cons m0 rest =>
    have hlenR : rest.length = (p - 1) / 2 := by simpa using hlen
    have hsumR : r = m0 + rest.sum := by simpa using hsum.symm
    have huniqR := ggTUClC_huniqR hlenR hrZ
    simp only [ggMultDatumC] at hDo
    rw [List.headD_cons] at hm0 hne
    have h1 : ¬ ((m0 :: rest).headD 0 = 1) := by rw [List.headD_cons]; omega
    have h2 : ¬ ((m0 :: rest).headD 0 = 2 ∧ n = 1) := by rw [List.headD_cons]; exact hne
    have h3 : 2 ≤ (m0 :: rest).headD 0 := by rw [List.headD_cons]; exact hm0
    rw [if_neg h1, if_neg h2, if_pos h3] at hDo
    rcases List.append_eq_singleton_iff.mp hDo with ⟨horb0, -⟩ | ⟨horb0, horbJ⟩
    · exact absurd horb0 (by simp)
    · have hmem : o ∈ [⟨⟨.C, m0, n⟩, true⟩] := ggTUClC_mem_of_eq_singleton horb0
      have hlab : o.lab = ⟨.C, m0, n⟩ := by
        have hxo : o = _ := List.mem_singleton.mp hmem
        rw [hxo]
      have hrest : rest.sum ≤ 1 := ggTUClC_tail_sum_le_one hlenR hrZ horbJ
      have hr : r = m0 + 1 := by
        have hne' : r ≠ m0 := by
          intro h
          exact hX (by rw [hlab, h])
        omega
      have hmn : m0 = 2 → 2 ≤ n := by
        intro hm2
        omega
      refine ⟨?_, ?_⟩
      · rw [hlab]
        exact ggTUClC_lambda2_C hn hm0 hmn
      · rw [hlab, hr]
        refine ggTUClC_row_C (by omega) ?_
        rcases hd with h1' | h2'
        · exact Or.inl (ggTUClC_dvd_of_ord_eq_one h1')
        · exact Or.inr (ggTUClC_dvd_of_ord_eq_two h2')

theorem ggTablePRow_of_mem_ggMultTableCl_C {r p n : ℕ} {D : GGKacDatum} (hn : 1 ≤ n)
    (hr2 : r = 2 → 2 ≤ n) (hD : D ∈ ggMultTableCl (.C r) false p n) (hrZ : D.rZ ≤ 1)
    {o : GGKacOrbit} (hDo : D.orbits = [o]) (hqs : o.qs = true) (hX : o.lab ≠ ⟨.C, r, n⟩)
    (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab ⟨.C, r, n⟩ := by
  have hd : ggMultOrd p n ≠ 0 := ggMultOrd_ne_zero_of_mem_ggMultTableCl hD
  obtain ⟨m, hlen, hsum, hDeq⟩ :=
    (mem_ggMultTableCl_C (r := r) (p := p) (n := n) hd).mp hD
  subst hDeq
  have hd12 : ggMultOrd p n = 1 ∨ ggMultOrd p n = 2 := ggTUClC_ord_eq_one_or_two hd
  by_cases h0 : m.headD 0 = 0
  · rcases hd12 with h1 | h2
    · exact ggTUClC_zero_one h1 hlen hsum hDo hrZ hn h0 hrk
    · exact ggTUClC_zero_two h2 hlen hsum hDo hrZ hn h0 hqs hrk
  · by_cases h1 : m.headD 0 = 1
    · exact ggTUClC_one hlen hDo h1 hrk
    · by_cases h2 : m.headD 0 = 2
      · by_cases hn1 : n = 1
        · exact ggTUClC_two_one hd12 hlen hsum hDo hrZ hr2 hn1 h2
        · exact ggTUClC_c_row hd12 hlen hsum hDo hrZ hn (by omega) (by omega) hX
      · exact ggTUClC_c_row hd12 hlen hsum hDo hrZ hn (by omega) (by omega) hX

end CFSG.StandardType

end
