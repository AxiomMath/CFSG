module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTablePRow_three_qTwo {labJ labX : LargeEvenLabel} (hrow : GGTablePRow 3 labJ labX)
    (hJ : 2 ≤ labJ.n) (hX : labX.n < 2) :
    (labJ.tag = .A ∧ 2 ≤ labJ.rank ∧ labJ.n = 2 ∧
        (labX = ⟨.A, 2 * labJ.rank + 1, 1⟩ ∨ labX = ⟨.A, 2 * labJ.rank + 2, 1⟩)) ∨
      (labJ.tag = .twA ∧ 2 ≤ labJ.rank ∧ labJ.n = 3 ∧ labX.tag = .twE6 ∧ labX.n = 1) := by
  obtain ⟨tJ, rJ, nJ⟩ := labJ
  obtain ⟨tX, rX, nX⟩ := labX
  change 2 ≤ nJ at hJ
  change nX < 2 at hX
  have e1 : (nX = nJ) = False := eq_false (by omega)
  have e2 : (nJ = 1) = False := eq_false (by omega)
  have e3 : (nX = 3 * nJ) = False := eq_false (by omega)
  simp only [GGTablePRow, LargeEvenLabel.mk.injEq, e1, e2, e3,
    show (3 = 7) = False by decide, show (3 = 5) = False by decide,
    and_false, false_and, false_or, or_false, true_and] at hrow
  rcases hrow with ⟨htJ, -, hrJ, hbad | hlin⟩ | ⟨htJ, -, hrJ, htX, hn⟩
  · obtain ⟨-, -, -, hn, hdvd⟩ := hbad
    have hnX : nX = 1 := by omega
    norm_num [hnX] at hdvd
  · obtain ⟨htX, hrX, hn, -⟩ := hlin
    have hnX : nX = 1 := by omega
    have hnJ : nJ = 2 := by omega
    refine Or.inl ⟨htJ, hrJ, hnJ, ?_⟩
    rcases hrX with hrX | hrX
    · exact Or.inl (by cases htX; cases hrX; cases hnX; rfl)
    · exact Or.inr (by cases htX; cases hrX; cases hnX; rfl)
  · have hnX : nX = 1 := by omega
    change 3 * nX = nJ at hn
    have hnJ : nJ = 3 := by omega
    exact Or.inr ⟨htJ, hrJ, hnJ, htX, hnX⟩

theorem ggTablePRow_three_A2_qTwo {labJ labX : LargeEvenLabel} (hΛ : LargeEvenInLambda2 labJ)
    (hJ : (labJ.tag = .A ∧ labJ.rank = 2 ∧ 3 ∣ 2 ^ labJ.n - 1) ∨
      (labJ.tag = .twA ∧ labJ.rank = 2 ∧ 3 ∣ 2 ^ labJ.n + 1))
    (hrow : GGTablePRow 3 labJ labX) (hX : labX.n < 2) :
    (labJ = ⟨.A, 2, 2⟩ ∧ (labX = ⟨.A, 5, 1⟩ ∨ labX = ⟨.A, 6, 1⟩)) ∨
      (labJ = ⟨.twA, 2, 3⟩ ∧ labX.tag = .twE6 ∧ labX.n = 1) := by
  have hr : labJ.rank = 2 := hJ.elim (fun h => h.2.1) (fun h => h.2.1)
  have hn : 2 ≤ labJ.n := by
    rcases hJ with ⟨ht, -, hdvd⟩ | ⟨ht, hr, -⟩
    · have hpos := hΛ.1
      by_contra! hlt
      have h1 : labJ.n = 1 := by omega
      norm_num [h1] at hdvd
    · have hLam : 2 ≤ labJ.rank ∧ (labJ.rank = 2 → 2 ≤ labJ.n) := by
        simpa [ht] using hΛ.2
      exact hLam.2 hr
  rcases ggTablePRow_three_qTwo hrow hn hX with
      ⟨ht, -, hn, hX⟩ | ⟨ht, -, hn, htX, hnX⟩
  · refine Or.inl ⟨?_, ?_⟩
    · cases labJ; simp_all
    · simpa [hr] using hX
  · refine Or.inr ⟨?_, htX, hnX⟩
    cases labJ; simp_all

theorem ggTablePRow_three_A2_qTwo_iso {labJ labK labX : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 labJ)
    (hJ : (labJ.tag = .A ∧ labJ.rank = 2 ∧ 3 ∣ 2 ^ labJ.n - 1) ∨
      (labJ.tag = .twA ∧ labJ.rank = 2 ∧ 3 ∣ 2 ^ labJ.n + 1))
    (hrow : GGTablePRow 3 labJ labX) (hΛK : LargeEvenInLambda2 labK)
    (hiso : GGLabelIso labK labX) (hK : labK.n < 2) :
    (labJ = ⟨.A, 2, 2⟩ ∧ (labX = ⟨.A, 5, 1⟩ ∨ labX = ⟨.A, 6, 1⟩)) ∨
      (labJ = ⟨.twA, 2, 3⟩ ∧ labX.tag = .twE6 ∧ labX.n = 1) := by
  have hX : labX.n < 2 := by
    rcases hiso with rfl | ⟨-, -, -, hn⟩ | ⟨-, hx⟩ | ⟨-, hx⟩ | ⟨-, hx⟩ |
        ⟨-, hx⟩ | ⟨-, hx⟩ | ⟨hx, hk⟩
    · exact hK
    · omega
    · simpa [hx] using hK
    · simpa [hx] using hK
    · simpa [hx] using hK
    · simpa [hx] using hK
    · exfalso
      rcases hJ with ⟨ht, hr, -⟩ | ⟨ht, hr, -⟩ <;>
        simp [GGTablePRow, ht, hr, hx, LargeEvenLabel.mk.injEq] at hrow
    · have hn := congrArg LargeEvenLabel.n hk
      have hpos := hΛK.1
      dsimp only at hn
      omega
  exact ggTablePRow_three_A2_qTwo hΛ hJ hrow hX

theorem ggLabelIso_A2_eq {labJ labJ' : LargeEvenLabel}
    (hJ : (labJ.tag = .A ∧ labJ.rank = 2) ∨ (labJ.tag = .twA ∧ labJ.rank = 2))
    (hiso : GGLabelIso labJ labJ') : labJ' = labJ := by
  obtain ⟨t, r, n⟩ := labJ
  obtain ⟨t', r', n'⟩ := labJ'
  rcases hJ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simpa [GGLabelIso, LargeEvenLabel.mk.injEq, eq_comm] using hiso

end CFSG.StandardType

end
