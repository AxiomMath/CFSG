module

public import CFSG.LocalAnalysis.StandardType.GGExcRERegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNExcKacDatum
public import CFSG.LocalAnalysis.StandardType.GGKacTable
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUClauses
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGTypeADefs
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private local instance (priority := high) one3DecidableEqLargeEvenLabel :
    DecidableEq LargeEvenLabel :=
  fun a b =>
    match a, b with
    | ⟨ta, ra, na⟩, ⟨tb, rb, nb⟩ =>
      if h1 : ta = tb then
        if h2 : ra = rb then
          if h3 : na = nb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private local instance (priority := high) one3DecidableEqGGKacOrbit : DecidableEq GGKacOrbit :=
  fun a b =>
    match a, b with
    | ⟨la, qa⟩, ⟨lb, qb⟩ =>
      if h1 : la = lb then
        if h2 : qa = qb then isTrue (by cases h1; cases h2; rfl)
        else isFalse (by intro h; injection h with _ h2'; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _; exact h1 h1')

private local instance (priority := high) one3DecidableEqGGKacDatum : DecidableEq GGKacDatum :=
  fun a b =>
    match a, b with
    | ⟨oa, za, sa⟩, ⟨ob, zb, sb⟩ =>
      if h1 : oa = ob then
        if h2 : za = zb then
          if h3 : sa = sb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private abbrev One3Check (T : GGKacType) : Prop :=
  ∀ D ∈ ggKacTable T false 3 1, ∀ o ∈ D.orbits, o.qs = true → o.lab.n = 1

private theorem one3_chk_F4 : One3Check .F4 := by decide +kernel

private theorem one3_chk_E7 : One3Check .E7 := by decide +kernel

private theorem one3_chk_E8 : One3Check .E8 := by decide +kernel

theorem ggExcOneThreeRK_of_fieldExp
    (hBS : GGK0ExcBS) {R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop}
    (hR : ∀ p n labJ labX, R p n labJ labX → ∀ lab : LargeEvenLabel, GGLabelIso lab labJ →
      2 ≤ lab.n) :
    GGTablePKnownRK fun p n labJ labX =>
      R p n labJ labX ∧ GGKacExcPair labX p ∧ GGKacCentred labX p ∧ labX.n = 1 ∧ p = 3 := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨hreg, hpair, hcen, hn1, hp3⟩ := hr
  obtain ⟨D, hDval, ha, hb, hc, he⟩ := ggTPNExcKac_datum hBS hd hΛX hpair hhX
  have hJfix : IsComponentOf J (ggFixSub σ) := by
    have hsub : ggFixSub σ = ggAutFixedSubgroup σ := by
      ext x; simp [ggFixSub, ggAutFixedSubgroup]
    rw [hsub]
    exact hd.1.1.2.2.2.1
  obtain ⟨o, ho, hoq, hdvd, hΛo, hlabo⟩ := ha J hJfix
  have hn2 : 2 ≤ o.lab.n :=
    hR p n labJ labX hreg o.lab (ggLabelRigidInput_holds _ _ _ hΛo hΛJ hlabo hhJ)
  obtain ⟨T, tw, hty, hDmem⟩ := hDval
  rw [hn1, hp3] at hDmem
  have hnotE6 : ¬ (labX.tag = .E6 ∨ labX.tag = .twE6) := fun h => hcen ⟨h, hp3⟩
  have h1 : o.lab.n = 1 := by
    rcases hpair.2.2.2 with hE6 | htwE6 | hE7 | hE8 | hF4
    · exact absurd (Or.inl hE6) hnotE6
    · exact absurd (Or.inr htwE6) hnotE6
    · have hty' : ggKacTypeOfLabel labX = some (.E7, false) := by
        obtain ⟨tx, rx, nx⟩ := labX
        simp only at hE7
        subst hE7
        rfl
      obtain ⟨rfl, rfl⟩ := Option.some.inj (hty.symm.trans hty')
      exact one3_chk_E7 D hDmem o ho hoq
    · have hty' : ggKacTypeOfLabel labX = some (.E8, false) := by
        obtain ⟨tx, rx, nx⟩ := labX
        simp only at hE8
        subst hE8
        rfl
      obtain ⟨rfl, rfl⟩ := Option.some.inj (hty.symm.trans hty')
      exact one3_chk_E8 D hDmem o ho hoq
    · have hty' : ggKacTypeOfLabel labX = some (.F4, false) := by
        obtain ⟨tx, rx, nx⟩ := labX
        simp only at hF4
        subst hF4
        rfl
      obtain ⟨rfl, rfl⟩ := Option.some.inj (hty.symm.trans hty')
      exact one3_chk_F4 D hDmem o ho hoq
  omega

private theorem one3_typeA_fieldExp {p n : ℕ} {labJ labX : LargeEvenLabel}
    (hreg : GGRegimeTypeA p n labJ labX) (lab : LargeEvenLabel) (hiso : GGLabelIso lab labJ) :
    2 ≤ lab.n := by
  obtain ⟨hA, hr2, hn2, -⟩ := hreg
  obtain ⟨tJ, r, f⟩ := labJ
  obtain ⟨t, l, m⟩ := lab
  simp only at hA hr2 hn2
  subst hA
  unfold GGLabelIso at hiso
  simp only [LargeEvenLabel.mk.injEq, reduceCtorEq, false_and, and_false, or_false,
    false_or] at hiso
  rcases hiso with ⟨rfl, rfl, rfl⟩ | ⟨⟨rfl, rfl, -⟩, -, -, rfl⟩ | ⟨-, -, hr1, -⟩
  · exact hn2
  · exact hn2
  · omega

theorem ggTypeAExcOneThree_holds
    (hBS : GGK0ExcBS) : GGTypeAExcOneThreeRK :=
  ggExcOneThreeRK_of_fieldExp hBS fun _ _ _ _ hreg lab hiso => one3_typeA_fieldExp hreg lab hiso

end CFSG.StandardType

end
