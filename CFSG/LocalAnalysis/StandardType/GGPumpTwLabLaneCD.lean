module

public import CFSG.LocalAnalysis.StandardType.GGPumpTwLabDefs
public import CFSG.LocalAnalysis.StandardType.GGPumpTwLabRigid
public import CFSG.LocalAnalysis.StandardType.GGPumpTwLabCompNe
public import CFSG.LocalAnalysis.StandardType.GGKacK1
public import CFSG.LocalAnalysis.StandardType.GGKacExcB2
public import CFSG.LocalAnalysis.StandardType.GGTCJHolds
import CFSG.LocalAnalysis.StandardType.GGK1ScMain
import CFSG.LocalAnalysis.StandardType.GGMultTableCl
import CFSG.LocalAnalysis.StandardType.GGTableB
import CFSG.LocalAnalysis.StandardType.GGNbrLangRegNTUnivHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly
private theorem l04fHL3_blockA_d1 (r nf : ℕ) :
    ggMultBlockA r nf 1 = ⟨⟨.A, r, nf⟩, decide (¬ (r = 1 ∧ nf = 1))⟩ := by
  simp [ggMultBlockA]

private theorem l04fHL3_blockA_d2_ge (r nf : ℕ) (hr : 2 ≤ r) :
    ggMultBlockA r nf 2 = ⟨⟨.twA, r, nf⟩, decide (¬ (r = 2 ∧ nf = 1))⟩ := by
  simp only [ggMultBlockA]
  rw [if_neg (by decide : ¬ ((2 : ℕ) = 1)), if_pos hr]

private theorem l04fHL3_blockA_d2_le (r nf : ℕ) (hr : ¬ 2 ≤ r) :
    ggMultBlockA r nf 2 = ⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩ := by
  simp only [ggMultBlockA]
  rw [if_neg (by decide : ¬ ((2 : ℕ) = 1)), if_neg hr]

private theorem l04fHL3_blockA_d1_lab (r nf : ℕ) :
    (ggMultBlockA r nf 1).lab = ⟨.A, r, nf⟩ := by rw [l04fHL3_blockA_d1]

private theorem l04fHL3_blockA_d2_ge_lab (r nf : ℕ) (hr : 2 ≤ r) :
    (ggMultBlockA r nf 2).lab = ⟨.twA, r, nf⟩ := by rw [l04fHL3_blockA_d2_ge r nf hr]

private theorem l04fHL3_blockA_d2_le_lab (r nf : ℕ) (hr : ¬ 2 ≤ r) :
    (ggMultBlockA r nf 2).lab = ⟨.A, 1, nf⟩ := by rw [l04fHL3_blockA_d2_le r nf hr]

private theorem l04fHL3_length_two {m : List ℕ} (h : m.length = 2) : ∃ a b, m = [a, b] := by
  obtain ⟨a, m1, hm1, h1⟩ := List.length_eq_succ_iff.mp h
  obtain ⟨b, hm2⟩ := List.length_eq_one_iff.mp h1
  exact ⟨a, b, by rw [← hm1, hm2]⟩

private theorem l04fHL3_eps0_eq (d : ℕ) (tw : Bool) (a b : ℕ) :
    ggMultEps0 3 d tw [a, b] = (if d = 2 ∧ b % 2 = 1 then tw else !tw) := by
  simp [ggMultEps0, List.range_succ]

private theorem l04fHL3_datumD_orbits (nf d : ℕ) (tw : Bool) (a b : ℕ) :
    (ggMultDatumD 3 nf d tw [a, b]).orbits =
      ggMultV0 a (ggMultEps0 3 d tw [a, b]) nf ++
        (if 2 ≤ b then [ggMultBlockA (b - 1) nf d] else []) := by
  by_cases hb : 2 ≤ b <;>
    simp [ggMultDatumD, List.range_succ, hb]

private theorem l04fHL3_v0_le_one (a : ℕ) (ha : a ≤ 1) (eps : Bool) (nf : ℕ) :
    ggMultV0 a eps nf = [] := by
  simp [ggMultV0, ha]

private theorem l04fHL3_v0_two_true (nf : ℕ) :
    ggMultV0 2 true nf = [⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩, ⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩] := by
  simp [ggMultV0]

private theorem l04fHL3_v0_two_false (nf : ℕ) :
    ggMultV0 2 false nf = [⟨⟨.A, 1, 2 * nf⟩, true⟩] := by
  simp [ggMultV0]

private theorem l04fHL3_v0_three_true (nf : ℕ) :
    ggMultV0 3 true nf = [⟨⟨.A, 3, nf⟩, true⟩] := by
  simp [ggMultV0]

private theorem l04fHL3_v0_three_false (nf : ℕ) :
    ggMultV0 3 false nf = [⟨⟨.twA, 3, nf⟩, true⟩] := by
  simp [ggMultV0]

private theorem l04fHL3_v0_ge_four_true (a nf : ℕ) (ha1 : ¬ a ≤ 1) (ha2 : a ≠ 2) (ha3 : a ≠ 3) :
    ggMultV0 a true nf = [⟨⟨.D, a, nf⟩, true⟩] := by
  simp only [ggMultV0, if_neg ha1, if_neg ha2, if_neg ha3]
  rw [if_pos trivial]

private theorem l04fHL3_v0_ge_four_false (a nf : ℕ) (ha1 : ¬ a ≤ 1) (ha2 : a ≠ 2) (ha3 : a ≠ 3) :
    ggMultV0 a false nf = [⟨⟨.twD, a, nf⟩, true⟩] := by
  simp only [ggMultV0, if_neg ha1, if_neg ha2, if_neg ha3]
  rw [if_neg (by decide : ¬ (false = true))]

private theorem l04fHL3_not_dvd_both (m : ℕ) : ¬ (3 ∣ 2 ^ m - 1 ∧ 3 ∣ 2 ^ m + 1) := by
  rintro ⟨h1, h2⟩
  have h3 : 3 ∣ 2 := by
    have hsub := Nat.dvd_sub h2 h1
    have hpos : 0 < 2 ^ m := by positivity
    rwa [show 2 ^ m + 1 - (2 ^ m - 1) = 2 by omega] at hsub
  norm_num at h3

private theorem l04fHL3_ggMultOrd_ne_zero {nf : ℕ} :
    ggMultOrd 3 nf ≠ 0 ↔ 3 ∣ 2 ^ nf - 1 ∨ 3 ∣ 2 ^ nf + 1 := by
  unfold ggMultOrd
  by_cases h1 : 3 ∣ 2 ^ nf - 1
  · rw [if_pos h1]
    exact ⟨fun _ => Or.inl h1, fun _ => by simp⟩
  · rw [if_neg h1]
    by_cases h2 : 3 ∣ 2 ^ nf + 1
    · rw [if_pos h2]
      exact ⟨fun _ => Or.inr h2, fun _ => by simp⟩
    · rw [if_neg h2]
      constructor
      · intro h; exact absurd rfl h
      · rintro (h | h)
        · exact absurd h h1
        · exact absurd h h2

private theorem l04fHL3_ggMultOrd_eq_one {nf : ℕ} (h : ggMultOrd 3 nf = 1) :
    3 ∣ 2 ^ nf - 1 := by
  by_contra hc
  by_cases h2 : 3 ∣ 2 ^ nf + 1
  · rw [ggMultOrd, if_neg hc, if_pos h2] at h; norm_num at h
  · rw [ggMultOrd, if_neg hc, if_neg h2] at h; norm_num at h

private theorem l04fHL3_ggMultOrd_eq_two {nf : ℕ} (h : ggMultOrd 3 nf = 2) :
    3 ∣ 2 ^ nf + 1 := by
  by_contra hc
  by_cases h1 : 3 ∣ 2 ^ nf - 1
  · rw [ggMultOrd, if_pos h1] at h; norm_num at h
  · rw [ggMultOrd, if_neg h1, if_neg hc] at h; norm_num at h

private theorem l04fHL3_ggMultOrd_cases {nf : ℕ} (h : ggMultOrd 3 nf ≠ 0) :
    ggMultOrd 3 nf = 1 ∨ ggMultOrd 3 nf = 2 := by
  by_cases h1 : 3 ∣ 2 ^ nf - 1
  · left; simp [ggMultOrd, h1]
  · by_cases h2 : 3 ∣ 2 ^ nf + 1
    · right; simp [ggMultOrd, h1, h2]
    · exact absurd (by simp [ggMultOrd, h1, h2]) h

private theorem l04fHL3_blockA_not_J {nf r f : ℕ} (hne : ggMultOrd 3 nf ≠ 0)
    (hJ : ((ggMultBlockA r nf (ggMultOrd 3 nf)).lab = ⟨.A, 5, f⟩ ∧ 3 ∣ 2 ^ f + 1) ∨
          ((ggMultBlockA r nf (ggMultOrd 3 nf)).lab = ⟨.twA, 5, f⟩ ∧ 3 ∣ 2 ^ f - 1) ∨
          (ggMultBlockA r nf (ggMultOrd 3 nf)).lab = ⟨.twD, 4, f⟩) : False := by
  rcases l04fHL3_ggMultOrd_cases hne with hd | hd
  · have harith := l04fHL3_ggMultOrd_eq_one hd
    rw [hd, l04fHL3_blockA_d1_lab] at hJ
    rcases hJ with ⟨h, hplus⟩ | ⟨h, _⟩ | h
    · have hnf : nf = f := by have := congrArg LargeEvenLabel.n h; simpa using this
      exact l04fHL3_not_dvd_both f ⟨by rw [← hnf]; exact harith, hplus⟩
    · have htag : LargeEvenLieTag.A = LargeEvenLieTag.twA := by
        have h' := congrArg LargeEvenLabel.tag h; simp at h'
      exact absurd htag (by decide)
    · have htag : LargeEvenLieTag.A = LargeEvenLieTag.twD := by
        have h' := congrArg LargeEvenLabel.tag h; simp at h'
      exact absurd htag (by decide)
  · have harith := l04fHL3_ggMultOrd_eq_two hd
    by_cases hr : 2 ≤ r
    · rw [hd, l04fHL3_blockA_d2_ge_lab r nf hr] at hJ
      rcases hJ with ⟨h, _⟩ | ⟨h, hminus⟩ | h
      · have htag : LargeEvenLieTag.twA = LargeEvenLieTag.A := by
          have h' := congrArg LargeEvenLabel.tag h; simp at h'
        exact absurd htag (by decide)
      · have hnf : nf = f := by have := congrArg LargeEvenLabel.n h; simpa using this
        exact l04fHL3_not_dvd_both f ⟨hminus, by rw [← hnf]; exact harith⟩
      · have htag : LargeEvenLieTag.twA = LargeEvenLieTag.twD := by
          have h' := congrArg LargeEvenLabel.tag h; simp at h'
        exact absurd htag (by decide)
    · rw [hd, l04fHL3_blockA_d2_le_lab r nf hr] at hJ
      rcases hJ with ⟨h, _⟩ | ⟨h, _⟩ | h
      · have hr15 : (1 : ℕ) = 5 := by have h' := congrArg LargeEvenLabel.rank h; simp at h'
        omega
      · have htag : LargeEvenLieTag.A = LargeEvenLieTag.twA := by
          have h' := congrArg LargeEvenLabel.tag h; simp at h'
        exact absurd htag (by decide)
      · have htag : LargeEvenLieTag.A = LargeEvenLieTag.twD := by
          have h' := congrArg LargeEvenLabel.tag h; simp at h'
        exact absurd htag (by decide)

private theorem l04fHL3_v0_lab_cases {a : ℕ} {eps : Bool} {nf : ℕ} {o : GGKacOrbit}
    (ho : o ∈ ggMultV0 a eps nf) :
    (a = 2 ∧ eps = true ∧ o.lab = ⟨.A, 1, nf⟩) ∨
    (a = 2 ∧ eps = false ∧ o.lab = ⟨.A, 1, 2 * nf⟩) ∨
    (a = 3 ∧ eps = true ∧ o.lab = ⟨.A, 3, nf⟩) ∨
    (a = 3 ∧ eps = false ∧ o.lab = ⟨.twA, 3, nf⟩) ∨
    (4 ≤ a ∧ eps = true ∧ o.lab = ⟨.D, a, nf⟩) ∨
    (4 ≤ a ∧ eps = false ∧ o.lab = ⟨.twD, a, nf⟩) := by
  by_cases h1 : a ≤ 1
  · rw [l04fHL3_v0_le_one a h1 eps nf] at ho; simp at ho
  · by_cases h2 : a = 2
    · subst h2
      by_cases he : eps = true
      · subst he
        rw [l04fHL3_v0_two_true nf] at ho
        rcases List.mem_cons.mp ho with h | h
        · exact Or.inl ⟨rfl, rfl, by rw [h]⟩
        · rw [List.mem_singleton] at h
          exact Or.inl ⟨rfl, rfl, by rw [h]⟩
      · have hef : eps = false := by cases eps <;> simp_all
        subst hef
        rw [l04fHL3_v0_two_false nf] at ho
        simp only [List.mem_singleton] at ho
        exact Or.inr (Or.inl ⟨rfl, rfl, by rw [ho]⟩)
    · by_cases h3 : a = 3
      · subst h3
        by_cases he : eps = true
        · subst he
          rw [l04fHL3_v0_three_true nf] at ho
          simp only [List.mem_singleton] at ho
          exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by rw [ho]⟩))
        · have hef : eps = false := by cases eps <;> simp_all
          subst hef
          rw [l04fHL3_v0_three_false nf] at ho
          simp only [List.mem_singleton] at ho
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by rw [ho]⟩)))
      · have ha : 4 ≤ a := by omega
        by_cases he : eps = true
        · subst he
          rw [l04fHL3_v0_ge_four_true a nf h1 h2 h3] at ho
          simp only [List.mem_singleton] at ho
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, rfl, by rw [ho]⟩))))
        · have hef : eps = false := by cases eps <;> simp_all
          subst hef
          rw [l04fHL3_v0_ge_four_false a nf h1 h2 h3] at ho
          simp only [List.mem_singleton] at ho
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ha, rfl, by rw [ho]⟩))))

private theorem l04fHL3_v0_twD4 {a : ℕ} {eps : Bool} {nf : ℕ} {o : GGKacOrbit} {f : ℕ}
    (ho : o ∈ ggMultV0 a eps nf) (h : o.lab = ⟨.twD, 4, f⟩) :
    eps = false ∧ a = 4 ∧ f = nf := by
  rcases l04fHL3_v0_lab_cases ho with ⟨-, he, hl⟩ | ⟨-, he, hl⟩ | ⟨-, he, hl⟩ |
    ⟨-, he, hl⟩ | ⟨-, he, hl⟩ | ⟨ha, he, hl⟩
  · exfalso; rw [hl] at h; simp [LargeEvenLabel.mk.injEq] at h
  · exfalso; rw [hl] at h; simp [LargeEvenLabel.mk.injEq] at h
  · exfalso; rw [hl] at h; simp [LargeEvenLabel.mk.injEq] at h
  · exfalso; rw [hl] at h; simp [LargeEvenLabel.mk.injEq] at h
  · exfalso; rw [hl] at h; simp [LargeEvenLabel.mk.injEq] at h
  · rw [hl] at h
    have ha4 : a = 4 := by have := congrArg LargeEvenLabel.rank h; simpa using this
    have hnf : nf = f := by have := congrArg LargeEvenLabel.n h; simpa using this
    exact ⟨he, ha4, hnf.symm⟩

private theorem l04fHL3_v0_J_twD {a : ℕ} {eps : Bool} {nf : ℕ} {o : GGKacOrbit} {f : ℕ}
    (ho : o ∈ ggMultV0 a eps nf)
    (hJ : (o.lab = ⟨.A, 5, f⟩ ∧ 3 ∣ 2 ^ f + 1) ∨
          (o.lab = ⟨.twA, 5, f⟩ ∧ 3 ∣ 2 ^ f - 1) ∨ o.lab = ⟨.twD, 4, f⟩) :
    o.lab = ⟨.twD, 4, f⟩ := by
  rcases l04fHL3_v0_lab_cases ho with ⟨-, -, hl⟩ | ⟨-, -, hl⟩ | ⟨-, -, hl⟩ |
    ⟨-, -, hl⟩ | ⟨-, -, hl⟩ | ⟨-, -, hl⟩
  · exfalso; rw [hl] at hJ
    rcases hJ with h | h | h <;> simp [LargeEvenLabel.mk.injEq] at h
  · exfalso; rw [hl] at hJ
    rcases hJ with h | h | h <;> simp [LargeEvenLabel.mk.injEq] at h
  · exfalso; rw [hl] at hJ
    rcases hJ with h | h | h <;> simp [LargeEvenLabel.mk.injEq] at h
  · exfalso; rw [hl] at hJ
    rcases hJ with h | h | h <;> simp [LargeEvenLabel.mk.injEq] at h
  · exfalso; rw [hl] at hJ
    rcases hJ with h | h | h <;> simp [LargeEvenLabel.mk.injEq] at h
  · rw [hl] at hJ
    rcases hJ with h | h | h
    · exfalso; simp [LargeEvenLabel.mk.injEq] at h
    · exfalso; simp [LargeEvenLabel.mk.injEq] at h
    · rw [← hl] at h; exact h

private theorem l04fHL3_mem_D_orbit {nf d : ℕ} {tw : Bool} {a b : ℕ} {o : GGKacOrbit}
    (ho : o ∈ (ggMultDatumD 3 nf d tw [a, b]).orbits) :
    o ∈ ggMultV0 a (ggMultEps0 3 d tw [a, b]) nf ∨
      (2 ≤ b ∧ o = ggMultBlockA (b - 1) nf d) := by
  rw [l04fHL3_datumD_orbits, List.mem_append] at ho
  by_cases hb : 2 ≤ b <;>
    simp only [hb, if_true, if_false, List.mem_cons, List.mem_nil_iff, or_false] at ho <;>
    tauto

private theorem l04fHL3_D_shape {nf : ℕ} {tw : Bool} {a b : ℕ} {o : GGKacOrbit} {f : ℕ}
    (hne : ggMultOrd 3 nf ≠ 0)
    (ho : o ∈ (ggMultDatumD 3 nf (ggMultOrd 3 nf) tw [a, b]).orbits)
    (hJ : (o.lab = (⟨.A, 5, f⟩ : LargeEvenLabel) ∧ 3 ∣ 2 ^ f + 1) ∨
          (o.lab = (⟨.twA, 5, f⟩ : LargeEvenLabel) ∧ 3 ∣ 2 ^ f - 1) ∨
          o.lab = (⟨.twD, 4, f⟩ : LargeEvenLabel)) :
    o.lab = (⟨.twD, 4, f⟩ : LargeEvenLabel) ∧ f = nf ∧ a = 4 ∧
      ((tw = true ∧ (ggMultOrd 3 nf = 1 ∨ b % 2 = 0)) ∨
        (tw = false ∧ ggMultOrd 3 nf = 2 ∧ b % 2 = 1)) := by
  rcases l04fHL3_mem_D_orbit ho with hv0 | ⟨-, hblk⟩
  · have hlab : o.lab = (⟨.twD, 4, f⟩ : LargeEvenLabel) := l04fHL3_v0_J_twD hv0 hJ
    obtain ⟨hEpsF, ha4, hnf⟩ := l04fHL3_v0_twD4 hv0 hlab
    have heps : (if ggMultOrd 3 nf = 2 ∧ b % 2 = 1 then tw else !tw) = false := by
      rw [l04fHL3_eps0_eq] at hEpsF; exact hEpsF
    refine ⟨hlab, hnf, ha4, ?_⟩
    by_cases hp : ggMultOrd 3 nf = 2 ∧ b % 2 = 1
    · have htw : tw = false := by simpa [hp] using heps
      exact Or.inr ⟨htw, hp.1, hp.2⟩
    · have htw : tw = true := by
        have h' : (!tw) = false := by simpa [hp] using heps
        cases tw <;> simp_all
      rcases l04fHL3_ggMultOrd_cases hne with hd1 | hd2
      · exact Or.inl ⟨htw, Or.inl hd1⟩
      · have hb2 : b % 2 = 0 := by
          rcases Nat.mod_two_eq_zero_or_one b with h | h
          · exact h
          · exact absurd ⟨hd2, h⟩ hp
        exact Or.inl ⟨htw, Or.inr hb2⟩
  · rw [hblk] at hJ
    exact (l04fHL3_blockA_not_J hne hJ).elim

private theorem l04fHL3_orbit_D
    {lab : LargeEvenLabel} (hF : GGKacGenericClD lab 3)
    {D : GGKacDatum} (hvalid : GGMultValidCl lab 3 D)
    {o : GGKacOrbit} (ho : o ∈ D.orbits) {f : ℕ}
    (hrig : (o.lab = (⟨.A, 5, f⟩ : LargeEvenLabel) ∧ 3 ∣ 2 ^ f + 1) ∨
            (o.lab = (⟨.twA, 5, f⟩ : LargeEvenLabel) ∧ 3 ∣ 2 ^ f - 1) ∨
            o.lab = (⟨.twD, 4, f⟩ : LargeEvenLabel))
    (hne : o.lab ≠ lab) : GGPumpTwLabConcl lab f := by
  rcases lab with ⟨tag, r, n⟩
  obtain ⟨hgen, htag, hr4⟩ := hF
  obtain ⟨T, tw, nf, hT, hDmem⟩ := hvalid
  have hdiv : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := hgen.2.2.1
  have hd : ggMultOrd 3 n ≠ 0 := l04fHL3_ggMultOrd_ne_zero.mpr hdiv
  rcases htag with hD | htwD
  · subst hD
    simp only [ggKacTypeClOfLabel] at hT
    rw [if_pos hr4] at hT
    simp only [Option.some.injEq, Prod.mk.injEq] at hT
    obtain ⟨rfl, rfl, rfl⟩ := hT
    obtain ⟨m, hmlen, hmsum, _hadm, hDeq⟩ := (mem_ggMultTableCl_D hd).mp hDmem
    rw [hDeq] at ho
    have hmlen2 : m.length = 2 := by simp [hmlen]
    obtain ⟨a, b, hmab⟩ := l04fHL3_length_two hmlen2
    subst hmab
    have hsum : a + b = r := by simpa using hmsum
    obtain ⟨hlabo, hnf, ha4, hcond⟩ := l04fHL3_D_shape hd ho hrig
    rcases hcond with ⟨hbad, -⟩ | ⟨-, hord2, hbodd⟩
    · exact absurd hbad (by decide)
    · have hb1 : 1 ≤ b := by
        by_contra hb
        have hb0 : b = 0 := by omega
        rw [hb0] at hbodd
        norm_num at hbodd
      have hk : r - 4 = b := by omega
      refine ⟨by rw [hnf], Or.inl ⟨r - 4, by omega,
        Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))⟩⟩
      · rw [hnf, show 4 + (r - 4) = r by omega]
      · rw [hnf]; exact l04fHL3_ggMultOrd_eq_two hord2
      · rw [hk]; exact Nat.odd_iff.mpr hbodd
  · subst htwD
    simp only [ggKacTypeClOfLabel] at hT
    rw [if_pos hr4] at hT
    simp only [Option.some.injEq, Prod.mk.injEq] at hT
    obtain ⟨rfl, rfl, rfl⟩ := hT
    obtain ⟨m, hmlen, hmsum, _hadm, hDeq⟩ := (mem_ggMultTableCl_D hd).mp hDmem
    rw [hDeq] at ho
    have hmlen2 : m.length = 2 := by simp [hmlen]
    obtain ⟨a, b, hmab⟩ := l04fHL3_length_two hmlen2
    subst hmab
    have hsum : a + b = r := by simpa using hmsum
    obtain ⟨hlabo, hnf, ha4, hcond⟩ := l04fHL3_D_shape hd ho hrig
    have hr5 : 5 ≤ r := by
      by_contra h5
      have hr4eq : r = 4 := by omega
      apply hne
      rw [hlabo, hr4eq, hnf]
    rcases hcond with ⟨-, hcase⟩ | ⟨hbad, -⟩
    · refine ⟨by rw [hnf], Or.inl ⟨r - 4, by omega,
        Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))⟩⟩
      · rw [hnf, show 4 + (r - 4) = r by omega]
      · rcases hcase with hord1 | hbeven
        · exact Or.inl (by rw [hnf]; exact l04fHL3_ggMultOrd_eq_one hord1)
        · rcases l04fHL3_ggMultOrd_cases hd with hd1 | hd2
          · exact Or.inl (by rw [hnf]; exact l04fHL3_ggMultOrd_eq_one hd1)
          · refine Or.inr ⟨by rw [hnf]; exact l04fHL3_ggMultOrd_eq_two hd2, ?_⟩
            have hk : r - 4 = b := by omega
            rw [hk]; exact Nat.even_iff.mpr hbeven
    · exact absurd hbad (by decide)

private theorem l04fHL3_laneD
    (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab) (hF : GGKacGenericClD lab 3) :
    GGPumpTwLabAt lab := by
  refine LargeEvenLabelAll.mono ?_ (largeEvenLabelAll_and (ggK0Main_cl 3 lab hlab hF.1)
    (largeEvenLabelAll_hasLabel lab))
  intro R _ I F hP L' _ _ ψ hψ hker hperf e J f he1 he3 hφ hJ hJlab
  obtain ⟨D, hvalid, ha, -⟩ := hP.1 L' ψ hψ hker hperf e he3 hφ
  obtain ⟨o, ho, _, _, hoΛ, hohas⟩ := ha J hJ
  exact l04fHL3_orbit_D hF hvalid ho (ggPumpTwJLab_rigid hJlab hoΛ hohas) (by
    intro h
    exact ggPumpTw_component_label_ne ψ hψ hker hperf hP.2 he1 hJ (h ▸ hohas))

private theorem l04fHL3_datumC_orbits (nf d : ℕ) (a b : ℕ) :
    (ggMultDatumC 3 nf d [a, b]).orbits =
      (if a = 1 then [⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩]
        else if a = 2 ∧ nf = 1 then [⟨⟨.B2der, 0, 1⟩, true⟩]
        else if 2 ≤ a then [⟨⟨.C, a, nf⟩, true⟩] else []) ++
        (if 2 ≤ b then [ggMultBlockA (b - 1) nf d] else []) := by
  by_cases ha1 : a = 1 <;> by_cases ha2 : a = 2 ∧ nf = 1 <;>
    by_cases ha : 2 ≤ a <;> by_cases hb : 2 ≤ b <;>
    simp [ggMultDatumC, List.range_succ, ha1, ha2, ha, hb]

private theorem l04fHL3_mem_C_orbit {nf d : ℕ} {a b : ℕ} {o : GGKacOrbit}
    (ho : o ∈ (ggMultDatumC 3 nf d [a, b]).orbits) :
    (a = 1 ∧ o = ⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩) ∨
      (a = 2 ∧ nf = 1 ∧ o = ⟨⟨.B2der, 0, 1⟩, true⟩) ∨
      (2 ≤ a ∧ o = ⟨⟨.C, a, nf⟩, true⟩) ∨ (2 ≤ b ∧ o = ggMultBlockA (b - 1) nf d) := by
  rw [l04fHL3_datumC_orbits, List.mem_append] at ho
  rcases ho with h0 | hJ
  · by_cases ha1 : a = 1
    · left; refine ⟨ha1, ?_⟩
      have hmem : o ∈ [⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩] := by simpa [ha1] using h0
      simpa using List.mem_singleton.mp hmem
    · by_cases ha2 : a = 2 ∧ nf = 1
      · right; left; refine ⟨ha2.1, ha2.2, ?_⟩
        have hmem : o ∈ [⟨⟨.B2der, 0, 1⟩, true⟩] := by simpa [ha1, ha2] using h0
        simpa using List.mem_singleton.mp hmem
      · by_cases ha : 2 ≤ a
        · right; right; left; refine ⟨ha, ?_⟩
          have hmem : o ∈ [⟨⟨.C, a, nf⟩, true⟩] := by simpa [ha1, ha2, ha] using h0
          simpa using List.mem_singleton.mp hmem
        · simp [ha1, ha2, ha] at h0
  · by_cases hb : 2 ≤ b
    · right; right; right; refine ⟨hb, ?_⟩
      have hmem : o ∈ [ggMultBlockA (b - 1) nf d] := by simpa [hb] using hJ
      simpa using List.mem_singleton.mp hmem
    · simp [hb] at hJ

private theorem l04fHL3_C_vacuous {nf : ℕ} {a b : ℕ} {o : GGKacOrbit} {f : ℕ}
    (hne : ggMultOrd 3 nf ≠ 0)
    (ho : o ∈ (ggMultDatumC 3 nf (ggMultOrd 3 nf) [a, b]).orbits)
    (hJ : (o.lab = ⟨.A, 5, f⟩ ∧ 3 ∣ 2 ^ f + 1) ∨
          (o.lab = ⟨.twA, 5, f⟩ ∧ 3 ∣ 2 ^ f - 1) ∨ o.lab = ⟨.twD, 4, f⟩) : False := by
  rcases l04fHL3_mem_C_orbit ho with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · rw [h] at hJ
    rcases hJ with h | h | h <;> simp [LargeEvenLabel.mk.injEq] at h
  · rw [h] at hJ
    rcases hJ with h | h | h <;> simp [LargeEvenLabel.mk.injEq] at h
  · rw [h] at hJ
    rcases hJ with h | h | h <;> simp [LargeEvenLabel.mk.injEq] at h
  · rw [h] at hJ
    exact l04fHL3_blockA_not_J hne hJ

private theorem l04fHL3_laneC
    (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab) (hF : GGKacGenericClC lab 3) :
    GGPumpTwLabAt lab := by
  refine LargeEvenLabelAll.mono ?_ (ggK0Main_cl 3 lab hlab hF.1)
  intro R _ I F hP L' _ _ ψ hψ hker hperf e J f he1 he3 hφ hJ hJlab
  obtain ⟨D, hvalid, ha, -⟩ := hP L' ψ hψ hker hperf e he3 hφ
  obtain ⟨o, ho, _hqs, _hdvd, hoΛ, hohas⟩ := ha J hJ
  have hrig := ggPumpTwJLab_rigid hJlab hoΛ hohas
  rcases lab with ⟨tag, r, n⟩
  have htag : tag = .B ∨ tag = .C := hF.2
  rcases htag with rfl | rfl
  all_goals
    obtain ⟨T, tw, nf, hT, hDmem⟩ := hvalid
    simp only [ggKacTypeClOfLabel] at hT
    by_cases hr : 2 ≤ r
    · rw [if_pos hr, Option.some.injEq, Prod.mk.injEq] at hT
      obtain ⟨rfl, rfl, rfl⟩ := hT
      have hdiv : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := hF.1.2.2.1
      have hd : ggMultOrd 3 n ≠ 0 := l04fHL3_ggMultOrd_ne_zero.mpr hdiv
      obtain ⟨m, hmlen, _hmsum, hDeq⟩ := (mem_ggMultTableCl_C hd).mp hDmem
      have hmlen2 : m.length = 2 := by simpa using hmlen
      obtain ⟨a, b, rfl⟩ := l04fHL3_length_two hmlen2
      rw [hDeq] at ho
      exact (l04fHL3_C_vacuous hd ho hrig).elim
    · rw [if_neg hr] at hT
      exact absurd hT (by simp)

theorem ggPumpTwLab_laneCD
    (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab)
    (hF : GGKacGenericClC lab 3 ∨ GGKacGenericClD lab 3) : GGPumpTwLabAt lab := by
  rcases hF with hC | hD
  · exact l04fHL3_laneC lab hlab hC
  · exact l04fHL3_laneD lab hlab hD

end CFSG.StandardType

end
