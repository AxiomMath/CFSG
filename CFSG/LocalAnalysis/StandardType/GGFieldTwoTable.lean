module

public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableCl
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableClDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ftt_iso_n_eq_one {l l' : LargeEvenLabel} (h : GGLabelIso l l') (hl : l.n = 1) :
    l'.n = 1 ∨ l = ⟨.twD, 2, 1⟩ := by
  rcases h with h | ⟨h1, h2, h3, h4⟩ | h | h | h | h | h | h
  · exact Or.inl (by rw [← h, hl])
  · exact Or.inl (by rw [← h4, hl])
  · exact Or.inl (by rw [h.2, hl])
  · exact Or.inl (by rw [h.2, hl])
  · exact Or.inl (by rw [h.2, hl])
  · exact Or.inl (by rw [h.2, hl])
  · exact Or.inr (by rw [h.1, hl])
  · exfalso
    have h2 : 2 * l'.n = 1 := by rw [← hl, h.2]
    omega

private theorem ftt_n_one_false {l labJ : LargeEvenLabel} (hJ : GGLabelIso l labJ)
    (hJ2 : 2 ≤ labJ.n) (hl : l.n = 1) (hne : l ≠ ⟨.twD, 2, 1⟩) : False := by
  rcases ftt_iso_n_eq_one hJ hl with h | h
  · omega
  · exact hne h

private theorem ftt_blockA_n_one {k n : ℕ} (hn : n = 1) : (ggMultBlockA k n 2).lab.n = 1 := by
  subst hn
  unfold ggMultBlockA
  split_ifs <;> rfl

private theorem ftt_blockA_tag_ne_twD {k n d : ℕ} : (ggMultBlockA k n d).lab ≠ ⟨.twD, 2, 1⟩ := by
  unfold ggMultBlockA
  split_ifs <;> (intro hh; exact absurd (congrArg LargeEvenLabel.tag hh) (by intro h; cases h))

private theorem ftt_orbJ_blockA {H : ℕ} {m : List ℕ} {x : GGKacOrbit}
    (hx : x ∈ ((List.range (H + 1)).filter
      (fun j => decide (1 ≤ j ∧ 2 ≤ m.getD j 0))).map
      (fun j => ggMultBlockA (m.getD j 0 - 1) 1 2)) :
    x.lab.n = 1 ∧ x.lab ≠ ⟨.twD, 2, 1⟩ := by
  simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
  obtain ⟨j, -, hx⟩ := hx
  rw [← hx]
  exact ⟨ftt_blockA_n_one rfl, ftt_blockA_tag_ne_twD⟩

private theorem ftt_A_true_orbJ {m : List ℕ} {x : GGKacOrbit}
    (hx : x ∈ ((List.range 3).filter (fun j => decide (2 ≤ m.getD j 0))).map
      (fun j => ggMultBlockA (m.getD j 0 - 1) 1 2)) :
    x.lab.n = 1 ∧ x.lab ≠ ⟨.twD, 2, 1⟩ := by
  simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
  obtain ⟨j, -, hx⟩ := hx
  rw [← hx]
  exact ⟨ftt_blockA_n_one rfl, ftt_blockA_tag_ne_twD⟩

private theorem ftt_A_orbJ_class {m : List ℕ} {x : GGKacOrbit}
    (hx : x ∈ ((List.range 2).filter (fun j => decide (1 ≤ j ∧ 2 ≤ m.getD j 0))).map
      (fun j => ⟨⟨.A, m.getD j 0 - 1, 2⟩, true⟩)) :
    x.lab = ⟨.A, m.getD 1 0 - 1, 2⟩ ∧ 2 ≤ m.getD 1 0 := by
  simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
  obtain ⟨j, hj, hx⟩ := hx
  have hj1 : j = 1 := by omega
  subst hj1
  refine ⟨?_, hj.2.2⟩
  rw [← hx]

private theorem ftt_v0_class {m0 : ℕ} {e : Bool} {x : GGKacOrbit} (hx : x ∈ ggMultV0 m0 e 1) :
    x.lab = ⟨.A, 1, 2⟩ ∨ (x.lab.n = 1 ∧ x.lab ≠ ⟨.twD, 2, 1⟩) := by
  unfold ggMultV0 at hx
  by_cases h1 : m0 ≤ 1
  · rw [if_pos h1] at hx
    exact absurd hx (List.not_mem_nil)
  · rw [if_neg h1] at hx
    by_cases h2 : m0 = 2
    · rw [if_pos h2] at hx
      by_cases h3 : e = true
      · rw [if_pos h3] at hx
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl <;>
          exact Or.inr ⟨rfl, by
            intro hh
            exact absurd (congrArg LargeEvenLabel.tag hh) (by intro h; cases h)⟩
      · rw [if_neg h3] at hx
        simp only [List.mem_singleton] at hx
        rw [hx]
        exact Or.inl rfl
    · rw [if_neg h2] at hx
      by_cases h4 : m0 = 3
      · rw [if_pos h4] at hx
        by_cases h5 : e = true
        · rw [if_pos h5] at hx
          simp only [List.mem_singleton] at hx
          rw [hx]
          exact Or.inr ⟨rfl, by
            intro hh
            exact absurd (congrArg LargeEvenLabel.tag hh) (by intro h; cases h)⟩
        · rw [if_neg h5] at hx
          simp only [List.mem_singleton] at hx
          rw [hx]
          exact Or.inr ⟨rfl, by
            intro hh
            exact absurd (congrArg LargeEvenLabel.tag hh) (by intro h; cases h)⟩
      · rw [if_neg h4] at hx
        by_cases h6 : e = true
        · rw [if_pos h6] at hx
          simp only [List.mem_singleton] at hx
          rw [hx]
          exact Or.inr ⟨rfl, by
            intro hh
            exact absurd (congrArg LargeEvenLabel.tag hh) (by intro h; cases h)⟩
        · rw [if_neg h6] at hx
          simp only [List.mem_singleton] at hx
          rw [hx]
          refine Or.inr ⟨rfl, ?_⟩
          intro hh
          have hr : m0 = 2 := by simpa using congrArg LargeEvenLabel.rank hh
          exact h2 hr

private theorem ftt_A_false_orbit {r : ℕ} {D : GGKacDatum} {o : GGKacOrbit}
    (hD : D ∈ ggMultTableCl (.A r) false 3 1) (ho : o ∈ D.orbits) :
    (o.lab.n = 1 ∧ o.lab ≠ ⟨.twD, 2, 1⟩) ∨
      ∃ a b : ℕ, o.lab = ⟨.A, b - 1, 2⟩ ∧ 2 ≤ b ∧ a + 2 * b = r + 1 := by
  have hord : ggMultOrd 3 1 = 2 := by decide
  obtain ⟨m, hmlen, hmsum, hQ, hDeq⟩ :=
    (mem_ggMultTableCl_A (p := 3) (n := 1) (r := r) (tw := false) (D := D)
      (by decide : ggMultOrd 3 1 ≠ 0)).mp hD
  rw [hord] at hQ hDeq
  subst hDeq
  have hsymm : ∀ j, j < 3 → m.getD ((3 - j) % 3) 0 = m.getD j 0 := by
    rcases hQ with ⟨-, h⟩ | ⟨h, -⟩ | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact h
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hmlen
  have hsum : a + b + c = r + 1 := by
    simp only [List.sum_cons, List.sum_nil, add_zero] at hmsum
    omega
  have hcb : c = b := by
    have hh := hsymm 1 (by norm_num)
    simpa using hh
  have hsum' : a + 2 * b = r + 1 := by omega
  simp only [ggMultDatumA] at ho
  rw [if_neg (by decide)] at ho
  rw [List.mem_append] at ho
  rcases ho with ho0 | hoJ
  · left
    have ho0' : o ∈ (if 2 ≤ a then [⟨⟨.A, a - 1, 1⟩, decide (¬ (a - 1 = 1 ∧ 1 = 1))⟩]
        else []) := by
      simpa using ho0
    by_cases ha2 : 2 ≤ a
    · rw [if_pos ha2] at ho0'
      simp only [List.mem_singleton] at ho0'
      rw [ho0']
      exact ⟨rfl, by
        intro hh
        exact absurd (congrArg LargeEvenLabel.tag hh) (by intro h; cases h)⟩
    · rw [if_neg ha2] at ho0'
      exact absurd ho0' (List.not_mem_nil)
  · right
    obtain ⟨hlab, hb2⟩ := ftt_A_orbJ_class (by simpa using hoJ)
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hlab hb2
    exact ⟨a, b, hlab, hb2, hsum'⟩

private theorem ftt_rankThree_not_iso_A12 {l : LargeEvenLabel} {f : ℕ}
    (hl : l = ⟨.A, 3, f⟩ ∨ l = ⟨.D, 3, f⟩) : ¬ GGLabelIso l ⟨.A, 1, 2⟩ := by
  rcases hl with rfl | rfl <;>
    unfold GGLabelIso <;>
    rintro (h | ⟨h1, h2, h3, h4⟩ | h | h | h | h | h | h) <;>
    simp_all

private theorem ftt_A_false_rankThree {r : ℕ} {D : GGKacDatum} {o : GGKacOrbit} {f : ℕ}
    (hD : D ∈ ggMultTableCl (.A r) false 3 1) (ho : o ∈ D.orbits) (hf : 2 ≤ f)
    (hoA : o.lab = ⟨.A, 3, f⟩ ∨ o.lab = ⟨.D, 3, f⟩) : 7 ≤ r := by
  rcases ftt_A_false_orbit hD ho with ⟨hn1, -⟩ | ⟨a, b, hlab, -, hsum⟩
  · rcases hoA with h | h
    · rw [h] at hn1
      have hf1 : f = 1 := by simpa using hn1
      omega
    · rw [h] at hn1
      have hf1 : f = 1 := by simpa using hn1
      omega
  · rcases hoA with h | h
    · rw [h] at hlab
      have hb : b = 4 := by
        have h3 : 3 = b - 1 := by simpa using congrArg LargeEvenLabel.rank hlab
        omega
      omega
    · rw [h] at hlab
      exact absurd (congrArg LargeEvenLabel.tag hlab) (by intro hh; cases hh)

private theorem ftt_A_false_one {r : ℕ} {D : GGKacDatum} {o : GGKacOrbit}
    {labJ : LargeEvenLabel} (hD : D ∈ ggMultTableCl (.A r) false 3 1) (ho : o ∈ D.orbits)
    (hJ : GGLabelIso o.lab labJ) (hJ2 : 2 ≤ labJ.n) :
    GGLabelIso o.lab ⟨.A, 1, 2⟩ ∨ 5 ≤ r := by
  rcases ftt_A_false_orbit hD ho with ⟨hn1, hne⟩ | ⟨a, b, hlab, hb2, hsum⟩
  · exact (ftt_n_one_false hJ hJ2 hn1 hne).elim
  · by_cases hbeq : b = 2
    · subst hbeq
      left
      rw [hlab]
      exact Or.inl rfl
    · right
      have hb3 : 3 ≤ b := by omega
      omega

private theorem ftt_A_true_one_false {r : ℕ} {D : GGKacDatum} {o : GGKacOrbit}
    {labJ : LargeEvenLabel} (hD : D ∈ ggMultTableCl (.A r) true 3 1) (ho : o ∈ D.orbits)
    (hJ : GGLabelIso o.lab labJ) (hJ2 : 2 ≤ labJ.n) : False := by
  have hord : ggMultOrd 3 1 = 2 := by decide
  obtain ⟨m, hmlen, hmsum, hQ, hDeq⟩ :=
    (mem_ggMultTableCl_A (p := 3) (n := 1) (r := r) (tw := true) (D := D)
      (by decide : ggMultOrd 3 1 ≠ 0)).mp hD
  rw [hord] at hQ hDeq
  subst hDeq
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hmlen
  simp only [ggMultDatumA] at ho
  rw [if_pos (by decide)] at ho
  have ho' : o ∈ ((List.range 3).filter (fun j => decide (2 ≤ [a, b, c].getD j 0))).map
      (fun j => ggMultBlockA ([a, b, c].getD j 0 - 1) 1 2) := by
    simpa using ho
  obtain ⟨hn1, hne⟩ := ftt_A_true_orbJ ho'
  exact ftt_n_one_false hJ hJ2 hn1 hne

private theorem ftt_A_false_two {D : GGKacDatum} {o : GGKacOrbit}
    (hD : D ∈ ggMultTableCl (.A 1) false 3 2) (ho : o ∈ D.orbits) :
    GGLabelIso o.lab ⟨.A, 1, 2⟩ := by
  have hord : ggMultOrd 3 2 = 1 := by decide
  obtain ⟨m, hmlen, hmsum, hQ, hDeq⟩ :=
    (mem_ggMultTableCl_A (p := 3) (n := 2) (r := 1) (tw := false) (D := D)
      (by decide : ggMultOrd 3 2 ≠ 0)).mp hD
  rw [hord] at hQ hDeq
  subst hDeq
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hmlen
  have hsum : a + b + c = 2 := by
    simp only [List.sum_cons, List.sum_nil, add_zero] at hmsum
    omega
  simp only [ggMultDatumA] at ho
  rw [if_pos (by decide)] at ho
  have ho' : o ∈ ((List.range 3).filter (fun j => decide (2 ≤ [a, b, c].getD j 0))).map
      (fun j => ggMultBlockA ([a, b, c].getD j 0 - 1) 2 1) := by
    simpa using ho
  rw [List.mem_map] at ho'
  obtain ⟨j, hjmem, hjo⟩ := ho'
  rw [List.mem_filter] at hjmem
  obtain ⟨hj3, hjdec⟩ := hjmem
  rw [List.mem_range] at hj3
  have hj2 : 2 ≤ [a, b, c].getD j 0 := by simpa using hjdec
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj with rfl | rfl | rfl
  · simp only [List.getD_cons_zero] at hj2 hjo
    have ha : a = 2 := by omega
    rw [ha] at hjo
    rw [← hjo]
    exact Or.inl rfl
  · simp only [List.getD_cons_zero, List.getD_cons_succ] at hj2 hjo
    have hb : b = 2 := by omega
    rw [hb] at hjo
    rw [← hjo]
    exact Or.inl rfl
  · simp only [List.getD_cons_zero, List.getD_cons_succ] at hj2 hjo
    have hc : c = 2 := by omega
    rw [hc] at hjo
    rw [← hjo]
    exact Or.inl rfl

private theorem ftt_C_orb0_class {a : ℕ} {x : GGKacOrbit}
    (hx : x ∈ (if a = 1 then [⟨⟨.A, 1, 1⟩, decide (¬ (1 = 1 ∧ 1 = 1))⟩]
      else if a = 2 ∧ 1 = 1 then [⟨⟨.B2der, 0, 1⟩, true⟩]
      else if 2 ≤ a then [⟨⟨.C, a, 1⟩, true⟩] else [])) :
    x.lab.n = 1 ∧ x.lab ≠ ⟨.twD, 2, 1⟩ := by
  by_cases h1 : a = 1
  · rw [if_pos h1] at hx
    simp only [List.mem_singleton] at hx
    rw [hx]
    exact ⟨rfl, by intro hh; exact absurd (congrArg LargeEvenLabel.tag hh) (by intro h; cases h)⟩
  · rw [if_neg h1] at hx
    by_cases h2 : a = 2 ∧ 1 = 1
    · rw [if_pos h2] at hx
      simp only [List.mem_singleton] at hx
      rw [hx]
      exact ⟨rfl, by intro hh; exact absurd (congrArg LargeEvenLabel.tag hh) (by intro h; cases h)⟩
    · rw [if_neg h2] at hx
      by_cases h3 : 2 ≤ a
      · rw [if_pos h3] at hx
        simp only [List.mem_singleton] at hx
        rw [hx]
        exact ⟨rfl, by
          intro hh
          exact absurd (congrArg LargeEvenLabel.tag hh) (by intro h; cases h)⟩
      · rw [if_neg h3] at hx
        exact absurd hx (List.not_mem_nil)

private theorem ftt_C_false {r : ℕ} {D : GGKacDatum} {o : GGKacOrbit}
    {labJ : LargeEvenLabel} (hD : D ∈ ggMultTableCl (.C r) false 3 1) (ho : o ∈ D.orbits)
    (hJ : GGLabelIso o.lab labJ) (hJ2 : 2 ≤ labJ.n) : False := by
  have hord : ggMultOrd 3 1 = 2 := by decide
  obtain ⟨m, hmlen, hmsum, hDeq⟩ :=
    (mem_ggMultTableCl_C (p := 3) (n := 1) (r := r) (D := D)
      (by decide : ggMultOrd 3 1 ≠ 0)).mp hD
  rw [hord] at hDeq
  subst hDeq
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hmlen
  simp only [ggMultDatumC, List.mem_append] at ho
  rcases ho with ho0 | hoJ
  · have ho0' : o ∈ (if a = 1 then [⟨⟨.A, 1, 1⟩, decide (¬ (1 = 1 ∧ 1 = 1))⟩]
        else if a = 2 ∧ 1 = 1 then [⟨⟨.B2der, 0, 1⟩, true⟩]
        else if 2 ≤ a then [⟨⟨.C, a, 1⟩, true⟩] else []) := by
      simpa using ho0
    obtain ⟨hn1, hne⟩ := ftt_C_orb0_class ho0'
    exact ftt_n_one_false hJ hJ2 hn1 hne
  · have hoJ' : o ∈ ((List.range (1 + 1)).filter
        (fun j => decide (1 ≤ j ∧ 2 ≤ [a, b].getD j 0))).map
        (fun j => ggMultBlockA ([a, b].getD j 0 - 1) 1 2) := by
      simpa using hoJ
    obtain ⟨hn1, hne⟩ := ftt_orbJ_blockA hoJ'
    exact ftt_n_one_false hJ hJ2 hn1 hne

private theorem ftt_D {r : ℕ} {tw : Bool} {D : GGKacDatum} {o : GGKacOrbit}
    {labJ : LargeEvenLabel} (hD : D ∈ ggMultTableCl (.D r) tw 3 1) (ho : o ∈ D.orbits)
    (hJ : GGLabelIso o.lab labJ) (hJ2 : 2 ≤ labJ.n) :
    GGLabelIso o.lab ⟨.A, 1, 2⟩ := by
  have hord : ggMultOrd 3 1 = 2 := by decide
  obtain ⟨m, hmlen, hmsum, hadm, hDeq⟩ :=
    (mem_ggMultTableCl_D (p := 3) (n := 1) (r := r) (tw := tw) (D := D)
      (by decide : ggMultOrd 3 1 ≠ 0)).mp hD
  rw [hord] at hDeq hadm
  subst hDeq
  obtain ⟨m0, m1, rfl⟩ := List.length_eq_two.mp hmlen
  simp only [ggMultDatumD, List.mem_append] at ho
  rcases ho with ho0 | hoJ
  · have ho0' : o ∈ ggMultV0 m0 (ggMultEps0 3 2 tw [m0, m1]) 1 := by
      simpa using ho0
    rcases ftt_v0_class ho0' with h | ⟨hn1, hne⟩
    · rw [h]
      exact Or.inl rfl
    · exact (ftt_n_one_false hJ hJ2 hn1 hne).elim
  · have hoJ' : o ∈ ((List.range (1 + 1)).filter
        (fun j => decide (1 ≤ j ∧ 2 ≤ [m0, m1].getD j 0))).map
        (fun j => ggMultBlockA ([m0, m1].getD j 0 - 1) 1 2) := by
      simpa using hoJ
    obtain ⟨hn1, hne⟩ := ftt_orbJ_blockA hoJ'
    exact (ftt_n_one_false hJ hJ2 hn1 hne).elim

private theorem ftt_some_eq {T T' : GGKacTypeCl} {tw tw' : Bool} {m m' : ℕ}
    (h : some (T', tw', m') = some (T, tw, m)) : T' = T ∧ tw' = tw ∧ m' = m := by
  simpa using h

private theorem ftt_twD_false {n k : ℕ} {T : GGKacTypeCl} {tw : Bool} {nf : ℕ}
    {D : GGKacDatum} {o : GGKacOrbit} {f : ℕ} (hn1 : n = 1)
    (htype : ggKacTypeClOfLabel ⟨.twD, k, n⟩ = some (T, tw, nf))
    (hmem : D ∈ ggMultTableCl T tw 3 nf) (ho : o ∈ D.orbits)
    (hf : 2 ≤ f) (hoA : o.lab = ⟨.A, 3, f⟩ ∨ o.lab = ⟨.D, 3, f⟩) : False := by
  have hJ2 : 2 ≤ o.lab.n := by
    rcases hoA with h | h <;> rw [h] <;> simpa using hf
  have hnot : ¬ GGLabelIso o.lab ⟨.A, 1, 2⟩ := ftt_rankThree_not_iso_A12 hoA
  simp only [ggKacTypeClOfLabel] at htype
  by_cases hk4 : 4 ≤ k
  · rw [if_pos hk4] at htype
    obtain ⟨rfl, rfl, rfl⟩ := ftt_some_eq htype
    rw [hn1] at hmem
    exact absurd (ftt_D hmem ho (Or.inl rfl) hJ2) hnot
  · rw [if_neg hk4] at htype
    by_cases hk3 : k = 3
    · rw [if_pos hk3] at htype
      obtain ⟨rfl, rfl, rfl⟩ := ftt_some_eq htype
      rw [hn1] at hmem
      exact (ftt_A_true_one_false hmem ho (Or.inl rfl) hJ2).elim
    · rw [if_neg hk3] at htype
      by_cases hk2 : k = 2
      · rw [if_pos hk2] at htype
        obtain ⟨rfl, rfl, rfl⟩ := ftt_some_eq htype
        have h2n : 2 * n = 2 := by omega
        rw [h2n] at hmem
        exact absurd (ftt_A_false_two hmem ho) hnot
      · rw [if_neg hk2] at htype
        simp at htype

theorem ggFieldTwoTable_outcome {lab : LargeEvenLabel} {D : GGKacDatum} {o : GGKacOrbit}
    {labJ : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hn : lab.n = 1 ∨ lab = ⟨.A, 1, 2⟩) (hD : GGMultValidCl lab 3 D)
    (ho : o ∈ D.orbits) (hqs : o.qs = true)
    (huniq : ∀ o' ∈ D.orbits, o'.qs = true → o' = o)
    (hJ : GGLabelIso o.lab labJ) (hJ2 : 2 ≤ labJ.n) (hX : ¬ GGLabelIso o.lab lab) :
    GGLabelIso o.lab ⟨.A, 1, 2⟩ ∨ (lab.tag = .A ∧ 5 ≤ lab.rank) := by
  obtain ⟨T, tw, nf, htype, hmem⟩ := hD
  rcases lab with ⟨tag, k, n⟩
  obtain ⟨hn_le, hlab'⟩ := hlab
  rcases hn with hn1 | hA12
  · have hn1' : n = 1 := by simpa using hn1
    cases tag with
    | A =>
      simp only [ggKacTypeClOfLabel] at htype
      obtain ⟨rfl, rfl, rfl⟩ := ftt_some_eq htype
      rw [hn1'] at hmem
      rcases ftt_A_false_one hmem ho hJ hJ2 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨rfl, h⟩
    | twA =>
      simp only [ggKacTypeClOfLabel] at htype
      obtain ⟨rfl, rfl, rfl⟩ := ftt_some_eq htype
      rw [hn1'] at hmem
      exact (ftt_A_true_one_false hmem ho hJ hJ2).elim
    | B =>
      simp only [ggKacTypeClOfLabel] at htype
      have hk : 2 ≤ k := hlab'.1
      rw [if_pos hk] at htype
      obtain ⟨rfl, rfl, rfl⟩ := ftt_some_eq htype
      rw [hn1'] at hmem
      exact (ftt_C_false hmem ho hJ hJ2).elim
    | C =>
      simp only [ggKacTypeClOfLabel] at htype
      have hk : 2 ≤ k := hlab'.1
      rw [if_pos hk] at htype
      obtain ⟨rfl, rfl, rfl⟩ := ftt_some_eq htype
      rw [hn1'] at hmem
      exact (ftt_C_false hmem ho hJ hJ2).elim
    | D =>
      simp only [ggKacTypeClOfLabel] at htype
      have hk : 3 ≤ k := hlab'
      by_cases hk4 : 4 ≤ k
      · rw [if_pos hk4] at htype
        obtain ⟨rfl, rfl, rfl⟩ := ftt_some_eq htype
        rw [hn1'] at hmem
        exact Or.inl (ftt_D hmem ho hJ hJ2)
      · rw [if_neg hk4] at htype
        have hk3 : k = 3 := by omega
        rw [if_pos hk3] at htype
        obtain ⟨rfl, rfl, rfl⟩ := ftt_some_eq htype
        rw [hn1'] at hmem
        rcases ftt_A_false_one hmem ho hJ hJ2 with h | h
        · exact Or.inl h
        · exact absurd h (by omega)
    | twD =>
      simp only [ggKacTypeClOfLabel] at htype
      have hk : 2 ≤ k := hlab'
      by_cases hk4 : 4 ≤ k
      · rw [if_pos hk4] at htype
        obtain ⟨rfl, rfl, rfl⟩ := ftt_some_eq htype
        rw [hn1'] at hmem
        exact Or.inl (ftt_D hmem ho hJ hJ2)
      · rw [if_neg hk4] at htype
        by_cases hk3 : k = 3
        · rw [if_pos hk3] at htype
          obtain ⟨rfl, rfl, rfl⟩ := ftt_some_eq htype
          rw [hn1'] at hmem
          exact (ftt_A_true_one_false hmem ho hJ hJ2).elim
        · rw [if_neg hk3] at htype
          by_cases hk2 : k = 2
          · rw [if_pos hk2] at htype
            obtain ⟨rfl, rfl, rfl⟩ := ftt_some_eq htype
            have h2n : 2 * n = 2 := by omega
            rw [h2n] at hmem
            exact Or.inl (ftt_A_false_two hmem ho)
          · rw [if_neg hk2] at htype
            simp at htype
    | E6 => simp only [ggKacTypeClOfLabel] at htype; simp at htype
    | E7 => simp only [ggKacTypeClOfLabel] at htype; simp at htype
    | E8 => simp only [ggKacTypeClOfLabel] at htype; simp at htype
    | F4 => simp only [ggKacTypeClOfLabel] at htype; simp at htype
    | twE6 => simp only [ggKacTypeClOfLabel] at htype; simp at htype
    | triD4 => simp only [ggKacTypeClOfLabel] at htype; simp at htype
    | G2 => simp only [ggKacTypeClOfLabel] at htype; simp at htype
    | twB2 => simp only [ggKacTypeClOfLabel] at htype; simp at htype
    | twF4 => simp only [ggKacTypeClOfLabel] at htype; simp at htype
    | B2der => simp only [ggKacTypeClOfLabel] at htype; simp at htype
    | G2der => simp only [ggKacTypeClOfLabel] at htype; simp at htype
    | twF4der => simp only [ggKacTypeClOfLabel] at htype; simp at htype
  · obtain ⟨rfl, rfl, rfl⟩ := hA12
    simp only [ggKacTypeClOfLabel] at htype
    obtain ⟨rfl, rfl, rfl⟩ := ftt_some_eq htype
    exact Or.inl (ftt_A_false_two hmem ho)

theorem ggFieldTwoTable_rankThree {lab : LargeEvenLabel} {D : GGKacDatum} {o : GGKacOrbit}
    {f : ℕ} (hlab : LargeEvenInLambda2 lab) (hn : lab.n = 1) (hD : GGMultValidCl lab 3 D)
    (ho : o ∈ D.orbits) (hf : 2 ≤ f) (hoA : o.lab = ⟨.A, 3, f⟩ ∨ o.lab = ⟨.D, 3, f⟩) :
    lab.tag = .A ∧ 7 ≤ lab.rank := by
  obtain ⟨T, tw, nf, htype, hmem⟩ := hD
  rcases lab with ⟨tag, k, n⟩
  obtain ⟨hn_le, hlab'⟩ := hlab
  have hn1 : n = 1 := by simpa using hn
  have hJ2 : 2 ≤ o.lab.n := by
    rcases hoA with h | h <;> rw [h] <;> simpa using hf
  have hnot : ¬ GGLabelIso o.lab ⟨.A, 1, 2⟩ := ftt_rankThree_not_iso_A12 hoA
  cases tag with
  | A =>
    simp only [ggKacTypeClOfLabel] at htype
    obtain ⟨rfl, rfl, rfl⟩ := ftt_some_eq htype
    rw [hn1] at hmem
    exact ⟨rfl, ftt_A_false_rankThree hmem ho hf hoA⟩
  | twA =>
    simp only [ggKacTypeClOfLabel] at htype
    obtain ⟨rfl, rfl, rfl⟩ := ftt_some_eq htype
    rw [hn1] at hmem
    exact (ftt_A_true_one_false hmem ho (Or.inl rfl) hJ2).elim
  | B =>
    simp only [ggKacTypeClOfLabel] at htype
    rw [if_pos hlab'.1] at htype
    obtain ⟨rfl, rfl, rfl⟩ := ftt_some_eq htype
    rw [hn1] at hmem
    exact (ftt_C_false hmem ho (Or.inl rfl) hJ2).elim
  | C =>
    simp only [ggKacTypeClOfLabel] at htype
    rw [if_pos hlab'.1] at htype
    obtain ⟨rfl, rfl, rfl⟩ := ftt_some_eq htype
    rw [hn1] at hmem
    exact (ftt_C_false hmem ho (Or.inl rfl) hJ2).elim
  | D =>
    simp only [ggKacTypeClOfLabel] at htype
    by_cases hk4 : 4 ≤ k
    · rw [if_pos hk4] at htype
      obtain ⟨rfl, rfl, rfl⟩ := ftt_some_eq htype
      rw [hn1] at hmem
      exact absurd (ftt_D hmem ho (Or.inl rfl) hJ2) hnot
    · rw [if_neg hk4] at htype
      have hk : 3 ≤ k := by simpa using hlab'
      have hk3 : k = 3 := by omega
      rw [if_pos hk3] at htype
      obtain ⟨rfl, rfl, rfl⟩ := ftt_some_eq htype
      rw [hn1] at hmem
      have h7 := ftt_A_false_rankThree hmem ho hf hoA
      exact absurd h7 (by omega)
  | twD =>
    simp only [ggKacTypeClOfLabel] at htype
    exact (ftt_twD_false hn1 htype hmem ho hf hoA).elim
  | _ =>
    simp only [ggKacTypeClOfLabel] at htype
    cases htype

end CFSG.StandardType

end
