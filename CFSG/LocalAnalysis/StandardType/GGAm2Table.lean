module

public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableCl
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableClDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private local instance (priority := high) am2tDecEqLabel : DecidableEq LargeEvenLabel :=
  fun a b =>
    match a, b with
    | ⟨ta, ra, na⟩, ⟨tb, rb, nb⟩ =>
      if h1 : ta = tb then
        if h2 : ra = rb then
          if h3 : na = nb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private local instance (priority := high) am2tDecEqOrbit : DecidableEq GGKacOrbit :=
  fun a b =>
    match a, b with
    | ⟨la, qa⟩, ⟨lb, qb⟩ =>
      if h1 : la = lb then
        if h2 : qa = qb then isTrue (by cases h1; cases h2; rfl)
        else isFalse (by intro h; injection h with _ h2'; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _; exact h1 h1')

private local instance (priority := high) am2tDecEqDatum : DecidableEq GGKacDatum :=
  fun a b =>
    match a, b with
    | ⟨oa, za, sa⟩, ⟨ob, zb, sb⟩ =>
      if h1 : oa = ob then
        if h2 : za = zb then
          if h3 : sa = sb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private theorem am2t_iso_A_cases {L : LargeEvenLabel} {m : ℕ} (hm : 3 ≤ m)
    (h : GGLabelIso L ⟨.A, m, 1⟩) : L = ⟨.A, m, 1⟩ ∨ L = ⟨.D, 3, 1⟩ := by
  rcases L with ⟨t, r, n⟩
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact absurd h.2.1 (by simp)
  · obtain ⟨h1, h2⟩ := h
    simp only [LargeEvenLabel.mk.injEq] at h1 h2
    obtain ⟨-, rfl, rfl⟩ := h2
    obtain ⟨rfl, rfl, -⟩ := h1
    exact Or.inr rfl
  · exact absurd h.2 (by simp [LargeEvenLabel.mk.injEq])
  · exact absurd h.2 (by simp [LargeEvenLabel.mk.injEq])
  · exact absurd h.2 (by simp [LargeEvenLabel.mk.injEq])
  · exfalso
    obtain ⟨-, h2⟩ := h
    simp only [LargeEvenLabel.mk.injEq] at h2
    omega
  · exfalso
    obtain ⟨h1, -⟩ := h
    simp only [LargeEvenLabel.mk.injEq] at h1
    exact absurd h1.1 (by simp)

private theorem am2t_not_iso_A_of_tag_ne {t : LargeEvenLieTag} {r n m : ℕ}
    (hm : 3 ≤ m) (htA : t ≠ .A) (htD : t ≠ .D) :
    ¬ GGLabelIso (⟨t, r, n⟩ : LargeEvenLabel) ⟨.A, m, 1⟩ := by
  intro h
  rcases am2t_iso_A_cases hm h with h' | h'
  · simp only [LargeEvenLabel.mk.injEq] at h'
    exact htA h'.1
  · simp only [LargeEvenLabel.mk.injEq] at h'
    exact htD h'.1

private theorem am2t_not_iso_A1 {n m : ℕ} (hm : 3 ≤ m) :
    ¬ GGLabelIso (⟨.A, 1, n⟩ : LargeEvenLabel) ⟨.A, m, 1⟩ := by
  intro h
  rcases am2t_iso_A_cases hm h with h' | h'
  · simp only [LargeEvenLabel.mk.injEq] at h'; omega
  · simp only [LargeEvenLabel.mk.injEq] at h'; omega

private theorem am2t_not_iso_A_D_ge4 {a n m : ℕ} (ha : 4 ≤ a) (hm : 3 ≤ m) :
    ¬ GGLabelIso (⟨.D, a, n⟩ : LargeEvenLabel) ⟨.A, m, 1⟩ := by
  intro h
  rcases am2t_iso_A_cases hm h with h' | h'
  · simp only [LargeEvenLabel.mk.injEq] at h'
    exact absurd h'.1 (by simp)
  · simp only [LargeEvenLabel.mk.injEq] at h'; omega

private theorem am2t_not_iso_A_nf_ne_one {r nf m : ℕ} (hnf : nf ≠ 1) (hm : 3 ≤ m) :
    ¬ GGLabelIso (⟨.A, r, nf⟩ : LargeEvenLabel) ⟨.A, m, 1⟩ := by
  intro h
  rcases am2t_iso_A_cases hm h with h' | h'
  · simp only [LargeEvenLabel.mk.injEq] at h'
    exact hnf h'.2.2
  · simp only [LargeEvenLabel.mk.injEq] at h'
    exact absurd h'.1 (by simp)

private theorem am2t_blockA_two_eq (r : ℕ) (hr : 2 ≤ r) :
    ggMultBlockA r 1 2 = ⟨⟨.twA, r, 1⟩, decide (r ≠ 2)⟩ := by
  simp only [ggMultBlockA]
  rw [if_neg (by decide : ¬ ((2 : ℕ) = 1)), if_pos hr]
  simp

private theorem am2t_blockA_two_eq' (r : ℕ) (hr : ¬ 2 ≤ r) :
    ggMultBlockA r 1 2 = ⟨⟨.A, 1, 1⟩, false⟩ := by
  simp only [ggMultBlockA]
  rw [if_neg (by decide : ¬ ((2 : ℕ) = 1)), if_neg hr]
  rfl

private theorem am2t_not_iso_blockA_two {r m : ℕ} (hm : 3 ≤ m) :
    ¬ GGLabelIso (ggMultBlockA r 1 2).lab ⟨.A, m, 1⟩ := by
  by_cases hr : 2 ≤ r
  · rw [am2t_blockA_two_eq r hr]
    exact am2t_not_iso_A_of_tag_ne hm (by decide) (by decide)
  · rw [am2t_blockA_two_eq' r hr]
    exact am2t_not_iso_A1 hm

private theorem am2t_blockA_one_eq (r nf : ℕ) :
    ggMultBlockA r nf 1 = ⟨⟨.A, r, nf⟩, decide (¬ (r = 1 ∧ nf = 1))⟩ := by
  simp only [ggMultBlockA]
  simp

private theorem am2t_not_iso_blockA_one_two {r m : ℕ} (hm : 3 ≤ m) :
    ¬ GGLabelIso (ggMultBlockA r 2 1).lab ⟨.A, m, 1⟩ := by
  rw [am2t_blockA_one_eq r 2]
  exact am2t_not_iso_A_nf_ne_one (by decide) hm

private theorem am2t_v0_le_one (a : ℕ) (ha : a ≤ 1) (eps : Bool) : ggMultV0 a eps 1 = [] := by
  simp [ggMultV0, ha]

private theorem am2t_v0_two_true : ggMultV0 2 true 1 =
    [⟨⟨.A, 1, 1⟩, false⟩, ⟨⟨.A, 1, 1⟩, false⟩] := by decide

private theorem am2t_v0_two_false : ggMultV0 2 false 1 = [⟨⟨.A, 1, 2⟩, true⟩] := by decide

private theorem am2t_v0_three_true : ggMultV0 3 true 1 = [⟨⟨.A, 3, 1⟩, true⟩] := by decide

private theorem am2t_v0_three_false : ggMultV0 3 false 1 = [⟨⟨.twA, 3, 1⟩, true⟩] := by decide

private theorem am2t_v0_ge_four_true (a : ℕ) (ha1 : ¬ a ≤ 1) (ha2 : a ≠ 2) (ha3 : a ≠ 3) :
    ggMultV0 a true 1 = [⟨⟨.D, a, 1⟩, true⟩] := by
  simp only [ggMultV0, if_neg ha1, if_neg ha2, if_neg ha3]
  rw [if_pos trivial]

private theorem am2t_v0_ge_four_false (a : ℕ) (ha1 : ¬ a ≤ 1) (ha2 : a ≠ 2) (ha3 : a ≠ 3) :
    ggMultV0 a false 1 = [⟨⟨.twD, a, 1⟩, true⟩] := by
  simp only [ggMultV0, if_neg ha1, if_neg ha2, if_neg ha3]
  rw [if_neg (by decide : ¬ (false = true))]

private theorem am2t_v0_iso {a : ℕ} {eps : Bool} {o : GGKacOrbit} {m : ℕ} (hm : 3 ≤ m)
    (ho : o ∈ ggMultV0 a eps 1) (h : GGLabelIso o.lab ⟨.A, m, 1⟩) :
    a = 3 ∧ eps = true := by
  by_cases ha : a ≤ 1
  · rw [am2t_v0_le_one a ha eps] at ho; simp at ho
  · by_cases ha2 : a = 2
    · subst ha2
      by_cases he : eps = true
      · subst he
        rw [am2t_v0_two_true] at ho
        rw [List.mem_cons, List.mem_singleton] at ho
        rcases ho with ho | ho <;> rw [ho] at h <;> exact absurd h (am2t_not_iso_A1 hm)
      · have hef : eps = false := by cases eps <;> simp_all
        subst hef
        rw [am2t_v0_two_false] at ho
        rw [List.mem_singleton] at ho
        rw [ho] at h; exact absurd h (am2t_not_iso_A1 hm)
    · by_cases ha3 : a = 3
      · subst ha3
        by_cases he : eps = true
        · exact ⟨rfl, he⟩
        · have hef : eps = false := by cases eps <;> simp_all
          subst hef
          rw [am2t_v0_three_false] at ho
          rw [List.mem_singleton] at ho
          rw [ho] at h
          exact absurd h (am2t_not_iso_A_of_tag_ne hm (by decide) (by decide))
      · by_cases he : eps = true
        · subst he
          rw [am2t_v0_ge_four_true a ha ha2 ha3] at ho
          rw [List.mem_singleton] at ho
          rw [ho] at h; exact absurd h (am2t_not_iso_A_D_ge4 (by omega) hm)
        · have hef : eps = false := by cases eps <;> simp_all
          subst hef
          rw [am2t_v0_ge_four_false a ha ha2 ha3] at ho
          rw [List.mem_singleton] at ho
          rw [ho] at h
          exact absurd h (am2t_not_iso_A_of_tag_ne hm (by decide) (by decide))

private theorem am2t_orbits_A_false (a b c : ℕ) :
    (ggMultDatumA 3 1 2 false [a, b, c]).orbits =
      (if 2 ≤ a then [⟨⟨.A, a - 1, 1⟩, decide (a ≠ 2)⟩] else []) ++
      (if 2 ≤ b then [⟨⟨.A, b - 1, 2⟩, true⟩] else []) := by
  by_cases ha : 2 ≤ a <;> by_cases hb : 2 ≤ b <;>
    simp [ggMultDatumA, ggMultBlockA, ggMultAllEq, List.range_succ, List.getD_cons_zero,
      List.getD_cons_succ, List.headD_cons, ha, hb]

private theorem am2t_orbits_A_true (a b c : ℕ) :
    (ggMultDatumA 3 1 2 true [a, b, c]).orbits =
      (if 2 ≤ a then [ggMultBlockA (a - 1) 1 2] else []) ++
      (if 2 ≤ b then [ggMultBlockA (b - 1) 1 2] else []) ++
      (if 2 ≤ c then [ggMultBlockA (c - 1) 1 2] else []) := by
  by_cases ha : 2 ≤ a <;> by_cases hb : 2 ≤ b <;> by_cases hc : 2 ≤ c <;>
    simp [ggMultDatumA, ggMultAllEq, List.range_succ, List.getD_cons_zero,
      List.getD_cons_succ, List.headD_cons, ha, hb, hc]

private theorem am2t_orbits_C (a b : ℕ) :
    (ggMultDatumC 3 1 2 [a, b]).orbits =
      (if a = 1 then [⟨⟨.A, 1, 1⟩, false⟩]
        else if a = 2 then [⟨⟨.B2der, 0, 1⟩, true⟩]
        else if 2 ≤ a then [⟨⟨.C, a, 1⟩, true⟩] else []) ++
      (if 2 ≤ b then [ggMultBlockA (b - 1) 1 2] else []) := by
  by_cases ha1 : a = 1 <;> by_cases ha2 : a = 2 <;> by_cases ha : 2 ≤ a <;>
    by_cases hb : 2 ≤ b <;>
    simp [ggMultDatumC, List.range_succ, List.getD_cons_zero,
      List.getD_cons_succ, List.headD_cons, ha1, ha2, ha, hb]

private theorem am2t_orbits_D (a b : ℕ) (tw : Bool) :
    (ggMultDatumD 3 1 2 tw [a, b]).orbits =
      ggMultV0 a (ggMultEps0 3 2 tw [a, b]) 1 ++
      (if 2 ≤ b then [ggMultBlockA (b - 1) 1 2] else []) := by
  by_cases hb : 2 ≤ b <;>
    simp [ggMultDatumD, List.range_succ, List.getD_cons_zero,
      List.getD_cons_succ, List.headD_cons, hb]

private theorem am2t_eps0_false (a b : ℕ) :
    ggMultEps0 3 2 false [a, b] = true ↔ b % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one b with h | h
  · rw [h]; simp [ggMultEps0, List.getD_cons_zero, List.getD_cons_succ, h]
  · rw [h]; simp [ggMultEps0, List.getD_cons_zero, List.getD_cons_succ, h]

private theorem am2t_eps0_true (a b : ℕ) :
    ggMultEps0 3 2 true [a, b] = true ↔ b % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one b with h | h
  · rw [h]; simp [ggMultEps0, List.getD_cons_zero, List.getD_cons_succ, h]
  · rw [h]; simp [ggMultEps0, List.getD_cons_zero, List.getD_cons_succ, h]

private theorem am2t_mem_A_false {a b c : ℕ} {o : GGKacOrbit}
    (ho : o ∈ (ggMultDatumA 3 1 2 false [a, b, c]).orbits) :
    (2 ≤ a ∧ o = ⟨⟨.A, a - 1, 1⟩, decide (a ≠ 2)⟩) ∨
      (2 ≤ b ∧ o = ⟨⟨.A, b - 1, 2⟩, true⟩) := by
  rw [am2t_orbits_A_false] at ho
  by_cases ha : 2 ≤ a <;> by_cases hb : 2 ≤ b <;>
    simp only [ha, hb, if_true, if_false, List.mem_append, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, List.mem_nil_iff, or_false, false_or,
      and_true, true_and] at ho <;>
    tauto

private theorem am2t_mem_A_true {a b c : ℕ} {o : GGKacOrbit}
    (ho : o ∈ (ggMultDatumA 3 1 2 true [a, b, c]).orbits) :
    (2 ≤ a ∧ o = ggMultBlockA (a - 1) 1 2) ∨ (2 ≤ b ∧ o = ggMultBlockA (b - 1) 1 2) ∨
      (2 ≤ c ∧ o = ggMultBlockA (c - 1) 1 2) := by
  rw [am2t_orbits_A_true] at ho
  by_cases ha : 2 ≤ a <;> by_cases hb : 2 ≤ b <;> by_cases hc : 2 ≤ c <;>
    simp only [ha, hb, hc, if_true, if_false, List.mem_append, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, List.mem_nil_iff, or_false, false_or,
      and_true, true_and] at ho <;>
    tauto

private theorem am2t_mem_C {a b : ℕ} {o : GGKacOrbit}
    (ho : o ∈ (ggMultDatumC 3 1 2 [a, b]).orbits) :
    (a = 1 ∧ o = ⟨⟨.A, 1, 1⟩, false⟩) ∨ (a = 2 ∧ o = ⟨⟨.B2der, 0, 1⟩, true⟩) ∨
      (2 ≤ a ∧ o = ⟨⟨.C, a, 1⟩, true⟩) ∨ (2 ≤ b ∧ o = ggMultBlockA (b - 1) 1 2) := by
  rw [am2t_orbits_C] at ho
  by_cases ha1 : a = 1 <;> by_cases ha2 : a = 2 <;> by_cases ha : 2 ≤ a <;>
    by_cases hb : 2 ≤ b <;>
    simp [ha1, ha2, ha, hb] at ho <;>
    tauto

private theorem am2t_mem_D {a b : ℕ} {tw : Bool} {o : GGKacOrbit}
    (ho : o ∈ (ggMultDatumD 3 1 2 tw [a, b]).orbits) :
    o ∈ ggMultV0 a (ggMultEps0 3 2 tw [a, b]) 1 ∨
      (2 ≤ b ∧ o = ggMultBlockA (b - 1) 1 2) := by
  rw [am2t_orbits_D, List.mem_append] at ho
  by_cases hb : 2 ≤ b <;>
    simp only [hb, if_true, if_false, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, List.mem_nil_iff, or_false, false_or, and_true, true_and] at ho <;>
    tauto


private theorem am2t_length_three {m : List ℕ} (h : m.length = 3) : ∃ a b c, m = [a, b, c] := by
  obtain ⟨a, m1, hm1, h1⟩ := List.length_eq_succ_iff.mp h
  obtain ⟨b, m2, hm2, h2⟩ := List.length_eq_succ_iff.mp h1
  obtain ⟨c, hm3⟩ := List.length_eq_one_iff.mp h2
  exact ⟨a, b, c, by rw [← hm1, ← hm2, hm3]⟩

private theorem am2t_length_two {m : List ℕ} (h : m.length = 2) : ∃ a b, m = [a, b] := by
  obtain ⟨a, m1, hm1, h1⟩ := List.length_eq_succ_iff.mp h
  obtain ⟨b, hm2⟩ := List.length_eq_one_iff.mp h1
  exact ⟨a, b, by rw [← hm1, hm2]⟩


private theorem am2t_row_A_add_two {m : ℕ} (hm : 3 ≤ m) :
    GGTablePRow 3 (⟨.A, m, 1⟩ : LargeEvenLabel) ⟨.A, m + 2, 1⟩ := by
  unfold GGTablePRow
  simp
  tauto

private theorem am2t_row_D3_twD4 :
    GGTablePRow 3 (⟨.D, 3, 1⟩ : LargeEvenLabel) ⟨.twD, 4, 1⟩ := by
  unfold GGTablePRow
  simp

private theorem am2t_lambda2_A {k n : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k) :
    LargeEvenInLambda2 (⟨.A, k, n⟩ : LargeEvenLabel) := by
  show 1 ≤ n ∧ 1 ≤ k ∧ (k = 1 → 2 ≤ n)
  exact ⟨hn, by omega, fun h => by omega⟩

private theorem am2t_blockA_contra {r m : ℕ} (hm : 3 ≤ m) {o : GGKacOrbit}
    (ho : o = ggMultBlockA r 1 2) (hJ : GGLabelIso o.lab ⟨.A, m, 1⟩) : False := by
  rw [ho] at hJ
  exact am2t_not_iso_blockA_two hm hJ

private theorem am2t_twA {r : ℕ} {D : GGKacDatum} {o : GGKacOrbit} {m : ℕ}
    (hDm : D ∈ ggMultTableCl (.A r) true 3 1) (ho : o ∈ D.orbits)
    (hJ : GGLabelIso o.lab ⟨.A, m, 1⟩) (hm : 3 ≤ m) : False := by
  have hd : ggMultOrd 3 1 ≠ 0 := by decide
  obtain ⟨mvec, hlen, hsum, hT5, hDeq⟩ :=
    (mem_ggMultTableCl_A (r := r) (p := 3) (n := 1) hd).mp hDm
  rw [show ggMultOrd 3 1 = 2 by decide] at hDeq
  subst hDeq
  obtain ⟨a, b, c, rfl⟩ := am2t_length_three hlen
  rcases am2t_mem_A_true ho with ⟨-, ho⟩ | ⟨-, ho⟩ | ⟨-, ho⟩
  · exact am2t_blockA_contra hm ho hJ
  · exact am2t_blockA_contra hm ho hJ
  · exact am2t_blockA_contra hm ho hJ

private theorem am2t_BC {r : ℕ} {D : GGKacDatum} {o : GGKacOrbit} {m : ℕ}
    (hDm : D ∈ ggMultTableCl (.C r) false 3 1) (ho : o ∈ D.orbits)
    (hJ : GGLabelIso o.lab ⟨.A, m, 1⟩) (hm : 3 ≤ m) : False := by
  have hd : ggMultOrd 3 1 ≠ 0 := by decide
  obtain ⟨mvec, hlen, hsum, hDeq⟩ :=
    (mem_ggMultTableCl_C (r := r) (p := 3) (n := 1) hd).mp hDm
  rw [show ggMultOrd 3 1 = 2 by decide] at hDeq
  subst hDeq
  obtain ⟨a, b, rfl⟩ := am2t_length_two hlen
  rcases am2t_mem_C ho with ⟨-, ho⟩ | ⟨-, ho⟩ | ⟨-, ho⟩ | ⟨-, ho⟩
  · rw [ho] at hJ; exact am2t_not_iso_A1 hm hJ
  · rw [ho] at hJ
    exact am2t_not_iso_A_of_tag_ne hm (by decide) (by decide) hJ
  · rw [ho] at hJ
    exact am2t_not_iso_A_of_tag_ne hm (by decide) (by decide) hJ
  · exact am2t_blockA_contra hm ho hJ



private theorem am2t_orbits_A_nf2 (a b c : ℕ) :
    (ggMultDatumA 3 2 1 false [a, b, c]).orbits =
      (if 2 ≤ a then [ggMultBlockA (a - 1) 2 1] else []) ++
      (if 2 ≤ b then [ggMultBlockA (b - 1) 2 1] else []) ++
      (if 2 ≤ c then [ggMultBlockA (c - 1) 2 1] else []) := by
  by_cases ha : 2 ≤ a <;> by_cases hb : 2 ≤ b <;> by_cases hc : 2 ≤ c <;>
    simp [ggMultDatumA, ggMultAllEq, List.range_succ, List.getD_cons_zero,
      List.getD_cons_succ, List.headD_cons, ha, hb, hc]

private theorem am2t_mem_A_nf2 {a b c : ℕ} {o : GGKacOrbit}
    (ho : o ∈ (ggMultDatumA 3 2 1 false [a, b, c]).orbits) :
    (2 ≤ a ∧ o = ggMultBlockA (a - 1) 2 1) ∨ (2 ≤ b ∧ o = ggMultBlockA (b - 1) 2 1) ∨
      (2 ≤ c ∧ o = ggMultBlockA (c - 1) 2 1) := by
  rw [am2t_orbits_A_nf2] at ho
  by_cases ha : 2 ≤ a <;> by_cases hb : 2 ≤ b <;> by_cases hc : 2 ≤ c <;>
    simp only [ha, hb, hc, if_true, if_false, List.mem_append, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, List.mem_nil_iff, or_false, false_or,
      and_true, true_and] at ho <;>
    tauto

private theorem am2t_blockA_two_qs {r : ℕ} (hr : 3 ≤ r) : (ggMultBlockA r 1 2).qs = true := by
  rw [am2t_blockA_two_eq r (by omega)]
  simp [show r ≠ 2 by omega]

private theorem am2t_lambda2_D3 : LargeEvenInLambda2 (⟨.D, 3, 1⟩ : LargeEvenLabel) := by
  show 1 ≤ 1 ∧ 3 ≤ 3
  exact ⟨le_rfl, le_rfl⟩

private theorem am2t_twD2 {D : GGKacDatum} {o : GGKacOrbit} {m : ℕ}
    (hDm : D ∈ ggMultTableCl (.A 1) false 3 2) (ho : o ∈ D.orbits)
    (hJ : GGLabelIso o.lab ⟨.A, m, 1⟩) (hm : 3 ≤ m) : False := by
  have hd : ggMultOrd 3 2 ≠ 0 := by decide
  obtain ⟨mvec, hlen, hsum, hT5, hDeq⟩ :=
    (mem_ggMultTableCl_A (r := 1) (p := 3) (n := 2) hd).mp hDm
  rw [show ggMultOrd 3 2 = 1 by decide] at hDeq
  subst hDeq
  obtain ⟨a, b, c, rfl⟩ := am2t_length_three hlen
  rcases am2t_mem_A_nf2 ho with ⟨-, ho⟩ | ⟨-, ho⟩ | ⟨-, ho⟩
  · rw [ho] at hJ; exact am2t_not_iso_blockA_one_two hm hJ
  · rw [ho] at hJ; exact am2t_not_iso_blockA_one_two hm hJ
  · rw [ho] at hJ; exact am2t_not_iso_blockA_one_two hm hJ

private theorem am2t_D3 {D : GGKacDatum} {o : GGKacOrbit} {m : ℕ}
    (hDm : D ∈ ggMultTableCl (.A 3) false 3 1) (ho : o ∈ D.orbits)
    (hqs : o.qs = true) (hJ : GGLabelIso o.lab ⟨.A, m, 1⟩) (hm : 3 ≤ m)
    (hX : ¬ GGLabelIso o.lab ⟨.D, 3, 1⟩) : False := by
  have hd : ggMultOrd 3 1 ≠ 0 := by decide
  obtain ⟨mvec, hlen, hsum, hT5, hDeq⟩ :=
    (mem_ggMultTableCl_A (r := 3) (p := 3) (n := 1) hd).mp hDm
  rw [show ggMultOrd 3 1 = 2 by decide] at hDeq
  subst hDeq
  obtain ⟨a, b, c, rfl⟩ := am2t_length_three hlen
  have hsymm : ∀ j, j < 3 → [a, b, c].getD ((3 - j) % 3) 0 = [a, b, c].getD j 0 := by
    rcases hT5 with h | h | h
    · exact absurd h.2 (by decide)
    · exact absurd h.1 (by decide)
    · exact h
  have hcb : c = b := by have := hsymm 1 (by norm_num); simpa using this
  subst c
  have hsum' : a + 2 * b = 4 := by
    simp only [List.sum_cons, List.sum_nil] at hsum; omega
  rcases am2t_mem_A_false ho with ⟨ha, ho⟩ | ⟨hb2, ho⟩
  · have hlab_eq := congrArg GGKacOrbit.lab ho
    have hqs_eq := congrArg GGKacOrbit.qs ho
    rw [hqs_eq] at hqs
    rw [hlab_eq] at hJ
    have ha2 : a ≠ 2 := by simpa using hqs
    have ham : a - 1 = m := by
      rcases am2t_iso_A_cases hm hJ with h | h
      · simp only [LargeEvenLabel.mk.injEq] at h; omega
      · simp only [LargeEvenLabel.mk.injEq] at h; exact absurd h.1 (by simp)
    have ha24 : a = 2 ∨ a = 4 := by omega
    rcases ha24 with rfl | rfl
    · exact ha2 rfl
    · apply hX
      rw [hlab_eq]
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · rw [ho] at hJ
    exact am2t_not_iso_A_nf_ne_one (by decide) hm hJ

private theorem am2t_A {r : ℕ} {D : GGKacDatum} {o : GGKacOrbit} {m : ℕ}
    (hDm : D ∈ ggMultTableCl (.A r) false 3 1) (ho : o ∈ D.orbits)
    (hqs : o.qs = true) (huniq : ∀ o' ∈ D.orbits, o'.qs = true → o' = o)
    (hJ : GGLabelIso o.lab ⟨.A, m, 1⟩) (hm : 3 ≤ m)
    (hX : ¬ GGLabelIso o.lab ⟨.A, r, 1⟩)
    (hlab : LargeEvenInLambda2 (⟨.A, r, 1⟩ : LargeEvenLabel)) :
    ∃ labJ labX : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      GGLabelIso (⟨.A, r, 1⟩ : LargeEvenLabel) labX ∧ LargeEvenInLambda2 labJ ∧
      LargeEvenInLambda2 labX ∧ GGTablePRow 3 labJ labX := by
  have hd : ggMultOrd 3 1 ≠ 0 := by decide
  obtain ⟨mvec, hlen, hsum, hT5, hDeq⟩ :=
    (mem_ggMultTableCl_A (r := r) (p := 3) (n := 1) hd).mp hDm
  rw [show ggMultOrd 3 1 = 2 by decide] at hDeq
  subst hDeq
  obtain ⟨a, b, c, rfl⟩ := am2t_length_three hlen
  have hsymm : ∀ j, j < 3 → [a, b, c].getD ((3 - j) % 3) 0 = [a, b, c].getD j 0 := by
    rcases hT5 with h | h | h
    · exact absurd h.2 (by decide)
    · exact absurd h.1 (by decide)
    · exact h
  have hcb : c = b := by have := hsymm 1 (by norm_num); simpa using this
  subst c
  have hsum' : a + 2 * b = r + 1 := by
    simp only [List.sum_cons, List.sum_nil] at hsum; omega
  have hb_le : b ≤ 1 := by
    by_contra hb
    have hmem : (⟨⟨.A, b - 1, 2⟩, true⟩ : GGKacOrbit) ∈
        (ggMultDatumA 3 1 2 false [a, b, b]).orbits := by
      rw [am2t_orbits_A_false a b b, if_pos (show 2 ≤ b by omega)]
      exact List.mem_append_right _ (by simp)
    have heq := huniq _ hmem rfl
    have hiso : GGLabelIso (⟨.A, b - 1, 2⟩ : LargeEvenLabel) ⟨.A, m, 1⟩ := by
      rw [← congrArg GGKacOrbit.lab heq] at hJ
      exact hJ
    exact absurd hiso (am2t_not_iso_A_nf_ne_one (by decide) hm)
  interval_cases b
  · rcases am2t_mem_A_false ho with ⟨ha, ho⟩ | ⟨hb2, -⟩
    · have hlab_eq := congrArg GGKacOrbit.lab ho
      rw [hlab_eq] at hJ
      have ham : a - 1 = m := by
        rcases am2t_iso_A_cases hm hJ with h | h
        · simp only [LargeEvenLabel.mk.injEq] at h; omega
        · simp only [LargeEvenLabel.mk.injEq] at h; exact absurd h.1 (by simp)
      have hr : r = m := by omega
      exact (hX (Or.inl (by rw [hlab_eq, ham, ← hr]))).elim
    · omega
  · rcases am2t_mem_A_false ho with ⟨ha, ho⟩ | ⟨hb2, -⟩
    · have hlab_eq := congrArg GGKacOrbit.lab ho
      rw [hlab_eq] at hJ
      have ham : a - 1 = m := by
        rcases am2t_iso_A_cases hm hJ with h | h
        · simp only [LargeEvenLabel.mk.injEq] at h; omega
        · simp only [LargeEvenLabel.mk.injEq] at h; exact absurd h.1 (by simp)
      have hr : r = m + 2 := by omega
      refine ⟨⟨.A, m, 1⟩, ⟨.A, r, 1⟩, ?_, Or.inl rfl, ?_, hlab, ?_⟩
      · rw [hlab_eq, ham]; exact Or.inl rfl
      · exact am2t_lambda2_A (by norm_num) (by omega)
      · rw [hr]; exact am2t_row_A_add_two hm
    · omega

private theorem am2t_D_false {r : ℕ} {D : GGKacDatum} {o : GGKacOrbit} {m : ℕ}
    (hDm : D ∈ ggMultTableCl (.D r) false 3 1) (ho : o ∈ D.orbits)
    (hqs : o.qs = true) (huniq : ∀ o' ∈ D.orbits, o'.qs = true → o' = o)
    (hJ : GGLabelIso o.lab ⟨.A, m, 1⟩) (hm : 3 ≤ m) (hr4 : 4 ≤ r)
    (hX : ¬ GGLabelIso o.lab ⟨.D, r, 1⟩)
    (hlab : LargeEvenInLambda2 (⟨.D, r, 1⟩ : LargeEvenLabel)) :
    (∃ labJ labX : LargeEvenLabel, GGLabelIso o.lab labJ ∧
        GGLabelIso (⟨.D, r, 1⟩ : LargeEvenLabel) labX ∧ LargeEvenInLambda2 labJ ∧
        LargeEvenInLambda2 labX ∧ GGTablePRow 3 labJ labX) ∨
      ((⟨.D, r, 1⟩ : LargeEvenLabel) = ⟨.D, 5, 1⟩ ∧ o.lab = ⟨.A, 3, 1⟩) := by
  have hd : ggMultOrd 3 1 ≠ 0 := by decide
  obtain ⟨mvec, hlen, hsum, hadm, hDeq⟩ :=
    (mem_ggMultTableCl_D (r := r) (p := 3) (n := 1) hd).mp hDm
  rw [show ggMultOrd 3 1 = 2 by decide] at hDeq
  subst hDeq
  obtain ⟨a, b, rfl⟩ := am2t_length_two hlen
  have hsum' : a + b = r := by
    simp only [List.sum_cons, List.sum_nil] at hsum; omega
  rcases am2t_mem_D (tw := false) ho with hv0 | ⟨hb2, ho⟩
  · obtain ⟨ha3, heps⟩ := am2t_v0_iso hm hv0 hJ
    subst ha3
    have holab : o.lab = ⟨.A, 3, 1⟩ := by
      rw [heps] at hv0
      rw [am2t_v0_three_true] at hv0
      rw [List.mem_singleton] at hv0
      rw [hv0]
    have hb_le : b ≤ 3 := by
      by_contra hb
      have hmem : ggMultBlockA (b - 1) 1 2 ∈ (ggMultDatumD 3 1 2 false [3, b]).orbits := by
        rw [am2t_orbits_D]
        simp [show 2 ≤ b by omega]
      have hqsb : (ggMultBlockA (b - 1) 1 2).qs = true := am2t_blockA_two_qs (by omega)
      have heq := huniq _ hmem hqsb
      have hbl : (ggMultBlockA (b - 1) 1 2).lab = o.lab := congrArg GGKacOrbit.lab heq
      rw [holab] at hbl
      rw [am2t_blockA_two_eq (b - 1) (by omega)] at hbl
      have hbl' : (⟨.twA, b - 1, 1⟩ : LargeEvenLabel) = ⟨.A, 3, 1⟩ := hbl
      simp only [LargeEvenLabel.mk.injEq] at hbl'
      exact absurd hbl'.1 (by simp)
    have hpar : b % 2 = 0 := (am2t_eps0_false 3 b).mp heps
    have hb02 : b = 0 ∨ b = 2 := by omega
    rcases hb02 with rfl | rfl
    · omega
    · right
      refine ⟨?_, holab⟩
      have hr5 : r = 5 := by omega
      rw [hr5]
  · rw [ho] at hJ
    exact absurd hJ (am2t_not_iso_blockA_two hm)

private theorem am2t_D_true {r : ℕ} {D : GGKacDatum} {o : GGKacOrbit} {m : ℕ}
    (hDm : D ∈ ggMultTableCl (.D r) true 3 1) (ho : o ∈ D.orbits)
    (hqs : o.qs = true) (huniq : ∀ o' ∈ D.orbits, o'.qs = true → o' = o)
    (hJ : GGLabelIso o.lab ⟨.A, m, 1⟩) (hm : 3 ≤ m) (hr4 : 4 ≤ r)
    (hX : ¬ GGLabelIso o.lab ⟨.twD, r, 1⟩)
    (hlab : LargeEvenInLambda2 (⟨.twD, r, 1⟩ : LargeEvenLabel)) :
    (∃ labJ labX : LargeEvenLabel, GGLabelIso o.lab labJ ∧
        GGLabelIso (⟨.twD, r, 1⟩ : LargeEvenLabel) labX ∧ LargeEvenInLambda2 labJ ∧
        LargeEvenInLambda2 labX ∧ GGTablePRow 3 labJ labX) ∨
      ((⟨.twD, r, 1⟩ : LargeEvenLabel) = ⟨.twD, 6, 1⟩ ∧ o.lab = ⟨.A, 3, 1⟩) := by
  have hd : ggMultOrd 3 1 ≠ 0 := by decide
  obtain ⟨mvec, hlen, hsum, hadm, hDeq⟩ :=
    (mem_ggMultTableCl_D (r := r) (p := 3) (n := 1) hd).mp hDm
  rw [show ggMultOrd 3 1 = 2 by decide] at hDeq
  subst hDeq
  obtain ⟨a, b, rfl⟩ := am2t_length_two hlen
  have hsum' : a + b = r := by
    simp only [List.sum_cons, List.sum_nil] at hsum; omega
  rcases am2t_mem_D (tw := true) ho with hv0 | ⟨hb2, ho⟩
  · obtain ⟨ha3, heps⟩ := am2t_v0_iso hm hv0 hJ
    subst ha3
    have holab : o.lab = ⟨.A, 3, 1⟩ := by
      rw [heps] at hv0
      rw [am2t_v0_three_true] at hv0
      rw [List.mem_singleton] at hv0
      rw [hv0]
    have hb_le : b ≤ 3 := by
      by_contra hb
      have hmem : ggMultBlockA (b - 1) 1 2 ∈ (ggMultDatumD 3 1 2 true [3, b]).orbits := by
        rw [am2t_orbits_D]
        simp [show 2 ≤ b by omega]
      have hqsb : (ggMultBlockA (b - 1) 1 2).qs = true := am2t_blockA_two_qs (by omega)
      have heq := huniq _ hmem hqsb
      have hbl : (ggMultBlockA (b - 1) 1 2).lab = o.lab := congrArg GGKacOrbit.lab heq
      rw [holab] at hbl
      rw [am2t_blockA_two_eq (b - 1) (by omega)] at hbl
      have hbl' : (⟨.twA, b - 1, 1⟩ : LargeEvenLabel) = ⟨.A, 3, 1⟩ := hbl
      simp only [LargeEvenLabel.mk.injEq] at hbl'
      exact absurd hbl'.1 (by simp)
    have hpar : b % 2 = 1 := (am2t_eps0_true 3 b).mp heps
    have hb13 : b = 1 ∨ b = 3 := by omega
    rcases hb13 with rfl | rfl
    · left
      have hr4' : r = 4 := by omega
      subst hr4'
      refine ⟨⟨.D, 3, 1⟩, ⟨.twD, 4, 1⟩, ?_, Or.inl rfl, am2t_lambda2_D3, hlab, ?_⟩
      · rw [holab]
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      · exact am2t_row_D3_twD4
    · right
      refine ⟨?_, holab⟩
      have hr6 : r = 6 := by omega
      rw [hr6]
  · rw [ho] at hJ
    exact absurd hJ (am2t_not_iso_blockA_two hm)

private theorem am2t_some_eq {T T' : GGKacTypeCl} {tw tw' : Bool} {nf nf' : ℕ}
    (h : some (T', tw', nf') = some (T, tw, nf)) : T' = T ∧ tw' = tw ∧ nf' = nf := by
  simpa using h

theorem ggAm2Table_outcome {lab : LargeEvenLabel} {D : GGKacDatum} {o : GGKacOrbit} {m : ℕ}
    (hlab : LargeEvenInLambda2 lab) (hn : lab.n = 1) (hD : GGMultValidCl lab 3 D)
    (ho : o ∈ D.orbits) (hqs : o.qs = true)
    (huniq : ∀ o' ∈ D.orbits, o'.qs = true → o' = o)
    (hJ : GGLabelIso o.lab ⟨.A, m, 1⟩) (hm : 3 ≤ m) (hX : ¬ GGLabelIso o.lab lab) :
    (∃ labJ labX : LargeEvenLabel, GGLabelIso o.lab labJ ∧ GGLabelIso lab labX ∧
        LargeEvenInLambda2 labJ ∧ LargeEvenInLambda2 labX ∧ GGTablePRow 3 labJ labX) ∨
      (lab = ⟨.D, 5, 1⟩ ∧ o.lab = ⟨.A, 3, 1⟩) ∨ (lab = ⟨.twD, 6, 1⟩ ∧ o.lab = ⟨.A, 3, 1⟩) := by
  obtain ⟨T, tw, nf, hTlab, hDm⟩ := hD
  rcases lab with ⟨tag, r, n⟩
  subst hn
  cases tag
  ·
    simp only [ggKacTypeClOfLabel] at hTlab
    obtain ⟨hT, htw, hnf⟩ := am2t_some_eq hTlab
    rw [← hT, ← htw, ← hnf] at hDm
    exact Or.inl (am2t_A hDm ho hqs huniq hJ hm hX hlab)
  ·
    simp only [ggKacTypeClOfLabel] at hTlab
    obtain ⟨hT, htw, hnf⟩ := am2t_some_eq hTlab
    rw [← hT, ← htw, ← hnf] at hDm
    exact (am2t_twA hDm ho hJ hm).elim
  ·
    simp only [ggKacTypeClOfLabel] at hTlab
    by_cases h2 : 2 ≤ r
    · rw [if_pos h2] at hTlab
      obtain ⟨hT, htw, hnf⟩ := am2t_some_eq hTlab
      rw [← hT, ← htw, ← hnf] at hDm
      exact (am2t_BC hDm ho hJ hm).elim
    · rw [if_neg h2] at hTlab; simp at hTlab
  ·
    simp only [ggKacTypeClOfLabel] at hTlab
    by_cases h2 : 2 ≤ r
    · rw [if_pos h2] at hTlab
      obtain ⟨hT, htw, hnf⟩ := am2t_some_eq hTlab
      rw [← hT, ← htw, ← hnf] at hDm
      exact (am2t_BC hDm ho hJ hm).elim
    · rw [if_neg h2] at hTlab; simp at hTlab
  ·
    simp only [ggKacTypeClOfLabel] at hTlab
    by_cases h4 : 4 ≤ r
    · rw [if_pos h4] at hTlab
      obtain ⟨hT, htw, hnf⟩ := am2t_some_eq hTlab
      rw [← hT, ← htw, ← hnf] at hDm
      rcases am2t_D_false hDm ho hqs huniq hJ hm h4 hX hlab with hrow | ⟨h5, holab⟩
      · exact Or.inl hrow
      · exact Or.inr (Or.inl ⟨h5, holab⟩)
    · rw [if_neg h4] at hTlab
      by_cases h3 : r = 3
      · rw [if_pos h3] at hTlab
        obtain ⟨hT, htw, hnf⟩ := am2t_some_eq hTlab
        rw [← hT, ← htw, ← hnf] at hDm
        subst h3
        exact (am2t_D3 hDm ho hqs hJ hm hX).elim
      · rw [if_neg h3] at hTlab; simp at hTlab
  ·
    simp only [ggKacTypeClOfLabel] at hTlab
    by_cases h4 : 4 ≤ r
    · rw [if_pos h4] at hTlab
      obtain ⟨hT, htw, hnf⟩ := am2t_some_eq hTlab
      rw [← hT, ← htw, ← hnf] at hDm
      rcases am2t_D_true hDm ho hqs huniq hJ hm h4 hX hlab with hrow | ⟨h6, holab⟩
      · exact Or.inl hrow
      · exact Or.inr (Or.inr ⟨h6, holab⟩)
    · rw [if_neg h4] at hTlab
      by_cases h3 : r = 3
      · rw [if_pos h3] at hTlab
        obtain ⟨hT, htw, hnf⟩ := am2t_some_eq hTlab
        rw [← hT, ← htw, ← hnf] at hDm
        subst h3
        exact (am2t_twA hDm ho hJ hm).elim
      · rw [if_neg h3] at hTlab
        by_cases h2 : r = 2
        · rw [if_pos h2] at hTlab
          obtain ⟨hT, htw, hnf⟩ := am2t_some_eq hTlab
          rw [← hT, ← htw, ← hnf] at hDm
          subst h2
          exact (am2t_twD2 hDm ho hJ hm).elim
        · rw [if_neg h2] at hTlab; simp at hTlab
  all_goals
    simp only [ggKacTypeClOfLabel] at hTlab
    simp at hTlab

end CFSG.StandardType

end
