module

public import CFSG.LocalAnalysis.StandardType.GGN2Defs
public import CFSG.LocalAnalysis.StandardType.GGN2RANine
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRACore
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ltrn2a4_labelIso_twA {lab : LargeEvenLabel}
    (h : GGLabelIso (⟨.twA, 3, 1⟩ : LargeEvenLabel) lab) :
    lab = ⟨.twA, 3, 1⟩ ∨ lab = ⟨.twD, 3, 1⟩ := by
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inl h.symm
  · exact absurd h.1 (by decide)
  · exact absurd (congrArg LargeEvenLabel.tag h.1) (by decide)
  · exact absurd (congrArg LargeEvenLabel.tag h.1) (by decide)
  · exact absurd (congrArg LargeEvenLabel.tag h.1) (by decide)
  · exact Or.inr (by simpa using h.2)
  · exact absurd (congrArg LargeEvenLabel.tag h.1) (by decide)
  · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)

theorem ggN2RA_classify (hrig : GGLabelRigidInput) {X : Type} [Group X] [Finite X]
    {A Ab : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X} {n : ℕ}
    (hd : GGTPNDatumB 3 n (fun _ _ => True) A Ab σ J) {labX : LargeEvenLabel}
    (hΛX : LargeEvenInLambda2 labX) (hRA : GGKacRA labX 3)
    (hhJ : GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J))
    (hhX : GGHasLabel labX (X ⧸ Subgroup.center X)) :
    labX = ⟨.twA, 5, 1⟩ ∨ labX = ⟨.twA, 8, 1⟩ := by
  obtain ⟨⟨hloc, -, -, -, -, -, h8, hm⟩, -⟩ := hd
  have hΛJ : LargeEvenInLambda2 (⟨.twA, 3, 1⟩ : LargeEvenLabel) := by
    simp [LargeEvenInLambda2]
  obtain ⟨t, r, n⟩ := labX
  have hm' : GGTPNMarked 3 (fun _ lab => lab = (⟨t, r, n⟩ : LargeEvenLabel)) A :=
    ggTPNMarked_eq_of_ggKacRA hrig Nat.prime_three hm hΛX hRA hhX
  rcases split_or_fieldType_of_ggKacRA Nat.prime_three hloc h8 hRA hm' with
    ⟨a, ds, hsum, hne, hlt, hds, hcase⟩ | ⟨-, -, hcase⟩
  ·
    rcases hcase with ⟨hΛ', hJ'⟩ | ⟨-, ha, hΛ', hJ'⟩
    · rcases ltrn2a4_labelIso_twA
          (hrig (⟨.twA, 3, 1⟩ : LargeEvenLabel) (⟨t, a - 1, n⟩ : LargeEvenLabel)
            (↥J ⧸ Subgroup.center ↥J) hΛJ hΛ' hhJ hJ') with heq | heq
      ·
        have ht : t = .twA := congrArg LargeEvenLabel.tag heq
        have ha1 : a - 1 = 3 := congrArg LargeEvenLabel.rank heq
        have hn : n = 1 := congrArg LargeEvenLabel.n heq
        have ha : a = 4 := by omega
        have hdvd : 3 ∣ r + 1 := by
          rcases hRA with ⟨hA, -, -⟩ | ⟨-, hd, -⟩
          · exact absurd (hA.symm.trans ht) (by decide)
          · exact hd
        have hds' : ∀ x ∈ ds, x = 1 ∨ x = 2 ∨ x = 3 := by
          intro x hx
          rcases hds x hx with h1 | ⟨-, -, h23⟩
          · exact Or.inl h1
          · rcases h23 with h2 | h3
            · exact Or.inr (Or.inl h2)
            · exact Or.inr (Or.inr h3)
        rw [ha] at hsum
        rcases ds with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
        · exact absurd rfl hne
        · have hsum' : r + 1 = 4 + x := by simpa using hsum
          have hdvd' : 3 ∣ 4 + x := by rw [← hsum']; exact hdvd
          have hx : x = 1 ∨ x = 2 ∨ x = 3 := hds' x (by simp)
          have hr : r = 5 := by
            obtain ⟨k, hk⟩ := hdvd'
            have hx1 : 1 ≤ x := by rcases hx with h | h | h <;> omega
            have hx3 : x ≤ 3 := by rcases hx with h | h | h <;> omega
            omega
          left
          rw [ht, hn, hr]
        · have hsum' : r + 1 = 4 + (x + y) := by simpa using hsum
          have hdvd' : 3 ∣ 4 + (x + y) := by rw [← hsum']; exact hdvd
          have hx : x = 1 ∨ x = 2 ∨ x = 3 := hds' x (by simp)
          have hy : y = 1 ∨ y = 2 ∨ y = 3 := hds' y (by simp)
          have hres : r = 5 ∨ r = 8 := by
            obtain ⟨k, hk⟩ := hdvd'
            have hx1 : 1 ≤ x := by rcases hx with h | h | h <;> omega
            have hx3 : x ≤ 3 := by rcases hx with h | h | h <;> omega
            have hy1 : 1 ≤ y := by rcases hy with h | h | h <;> omega
            have hy3 : y ≤ 3 := by rcases hy with h | h | h <;> omega
            omega
          rcases hres with hr | hr
          · left; rw [ht, hn, hr]
          · right; rw [ht, hn, hr]
        · exfalso
          simp only [List.length_cons] at hlt
          omega
      ·
        have ht : t = .twD := congrArg LargeEvenLabel.tag heq
        rcases hRA with ⟨hA, -, -⟩ | ⟨hA, -, -⟩ <;>
          exact absurd (hA.symm.trans ht) (by decide)
    ·
      rcases ltrn2a4_labelIso_twA
          (hrig (⟨.twA, 3, 1⟩ : LargeEvenLabel) (⟨.A, 1, n⟩ : LargeEvenLabel)
            (↥J ⧸ Subgroup.center ↥J) hΛJ hΛ' hhJ hJ') with heq | heq <;>
        exact absurd (congrArg LargeEvenLabel.tag heq) (by simp)
  ·
    rcases hcase with ⟨-, hΛ', hJ'⟩ | ⟨-, -, hΛ', hJ'⟩
    · rcases ltrn2a4_labelIso_twA
          (hrig (⟨.twA, 3, 1⟩ : LargeEvenLabel)
            (⟨.A, (r + 1) / 3 - 1, 3 * n⟩ : LargeEvenLabel)
            (↥J ⧸ Subgroup.center ↥J) hΛJ hΛ' hhJ hJ') with heq | heq <;>
        exact absurd (congrArg LargeEvenLabel.tag heq) (by simp)
    · rcases ltrn2a4_labelIso_twA
          (hrig (⟨.twA, 3, 1⟩ : LargeEvenLabel)
            (⟨.twA, (r + 1) / 3 - 1, 3 * n⟩ : LargeEvenLabel)
            (↥J ⧸ Subgroup.center ↥J) hΛJ hΛ' hhJ hJ') with heq | heq
      · have h3n : 3 * n = 1 := congrArg LargeEvenLabel.n heq
        omega
      · exact absurd (congrArg LargeEvenLabel.tag heq) (by simp)

theorem ggTablePKnownR_n2RA :
    GGTablePKnownR GGRegimeN2RA := by
  intro p hp hp2 X _ _ A Ab σ J n hd labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨⟨hp3, hn, hlabJ⟩, hRA⟩ := hr
  subst hp3
  subst hn
  subst hlabJ
  rcases ggN2RA_classify ggLabelRigidInput_holds hd hΛX hRA hhJ hhX with h | h
  · subst h
    exact ggN2RA_row_six hhJ hhX
  · subst h
    exact (ggN2RA_not_nine hd hhX).elim

end CFSG.StandardType

end
