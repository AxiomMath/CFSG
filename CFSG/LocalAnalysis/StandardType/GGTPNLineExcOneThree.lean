module

public import CFSG.LocalAnalysis.StandardType.GGTPNLineDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNExcKacDatum
public import CFSG.LocalAnalysis.StandardType.GGKacTable
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private local instance (priority := high) lo13DecidableEqLargeEvenLabel :
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

private local instance (priority := high) lo13DecidableEqGGKacOrbit : DecidableEq GGKacOrbit :=
  fun a b =>
    match a, b with
    | ⟨la, qa⟩, ⟨lb, qb⟩ =>
      if h1 : la = lb then
        if h2 : qa = qb then isTrue (by cases h1; cases h2; rfl)
        else isFalse (by intro h; injection h with _ h2'; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _; exact h1 h1')

private local instance (priority := high) lo13DecidableEqGGKacDatum : DecidableEq GGKacDatum :=
  fun a b =>
    match a, b with
    | ⟨oa, za, sa⟩, ⟨ob, zb, sb⟩ =>
      if h1 : oa = ob then
        if h2 : za = zb then
          if h3 : sa = sb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private local instance (priority := high) lo13DecidableGGResLineJLabel
    (T : GGResLineJType) (lab : LargeEvenLabel) : Decidable (ggResLineJLabel T lab) := by
  cases T <;> unfold ggResLineJLabel <;> infer_instance

private abbrev lo13NoLine (lab : LargeEvenLabel) : Prop :=
  ¬ ggResLineJLabel .A2 lab ∧ ¬ ggResLineJLabel .B2 lab ∧
    ¬ ggResLineJLabel .A3 lab ∧ ¬ ggResLineJLabel .B3 lab ∧
    ¬ ggResLineJLabel .C3 lab

private theorem lo13_noLine_of {lab : LargeEvenLabel} (h : lo13NoLine lab)
    (T : GGResLineJType) : ¬ ggResLineJLabel T lab := by
  rcases h with ⟨h1, h2, h3, h4, h5⟩
  cases T <;> assumption

private abbrev lo13LineFree (T : GGKacType) : Prop :=
  ∀ D ∈ ggKacTable T false 3 1, ∀ o ∈ D.orbits, o.qs = true → lo13NoLine o.lab

private theorem lo13_lineFree_E7 : lo13LineFree .E7 := by decide +kernel

private theorem lo13_lineFree_E8 : lo13LineFree .E8 := by decide +kernel

private theorem lo13_f4_orbits :
    ∀ D ∈ ggKacTable .F4 false 3 1, ∀ o ∈ D.orbits, o.qs = true →
      o.lab = ⟨.C, 3, 1⟩ ∨ o.lab = ⟨.F4, 0, 1⟩ := by decide +kernel

private theorem lo13_f4_noLine : lo13NoLine ⟨.F4, 0, 1⟩ := by decide +kernel

private theorem lo13_row_C3_F4 : GGTablePRow 3 ⟨.C, 3, 1⟩ ⟨.F4, 0, 1⟩ := by
  unfold GGTablePRow
  simp

theorem ggLineExcOneThree_holds
    (hBS : GGK0ExcBS) : GGLineExcOneThreeRK := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨⟨_, -, T, hT⟩, hpair, hcen, hn1, hp3⟩ := hr
  obtain ⟨D, hDval, ha, -, -, -⟩ := ggTPNExcKac_datum hBS hd hΛX hpair hhX
  have hJfix : IsComponentOf J (ggFixSub σ) := by
    have hsub : ggFixSub σ = ggAutFixedSubgroup σ := by
      ext x; simp [ggFixSub, ggAutFixedSubgroup]
    rw [hsub]
    exact hd.1.1.2.2.2.1
  obtain ⟨o, ho, hoq, -, hΛo, hlabo⟩ := ha J hJfix
  have hiso : GGLabelIso labJ o.lab :=
    ggLabelRigidInput_holds labJ o.lab (↥J ⧸ Subgroup.center ↥J) hΛJ hΛo hhJ hlabo
  have hTo : ggResLineJLabel T o.lab := ggResLineJLabel_of_iso hT hiso
  obtain ⟨Tk, tw, hty, hDmem⟩ := hDval
  rw [hn1, hp3] at hDmem
  have hnotE6 : ¬ (labX.tag = .E6 ∨ labX.tag = .twE6) := fun h => hcen ⟨h, hp3⟩
  rcases hpair.2.2.2 with hE6 | htwE6 | hE7 | hE8 | hF4
  · exact absurd (Or.inl hE6) hnotE6
  · exact absurd (Or.inr htwE6) hnotE6
  · have hty' : ggKacTypeOfLabel labX = some (.E7, false) := by
      obtain ⟨tx, rx, nx⟩ := labX
      simp only at hE7
      subst hE7
      rfl
    obtain ⟨rfl, rfl⟩ := Option.some.inj (hty.symm.trans hty')
    exact absurd hTo ((lo13_noLine_of (lo13_lineFree_E7 D hDmem o ho hoq) T))
  · have hty' : ggKacTypeOfLabel labX = some (.E8, false) := by
      obtain ⟨tx, rx, nx⟩ := labX
      simp only at hE8
      subst hE8
      rfl
    obtain ⟨rfl, rfl⟩ := Option.some.inj (hty.symm.trans hty')
    exact absurd hTo ((lo13_noLine_of (lo13_lineFree_E8 D hDmem o ho hoq) T))
  · have hty' : ggKacTypeOfLabel labX = some (.F4, false) := by
      obtain ⟨tx, rx, nx⟩ := labX
      simp only at hF4
      subst hF4
      rfl
    obtain ⟨rfl, rfl⟩ := Option.some.inj (hty.symm.trans hty')
    have hXeq : labX = ⟨.F4, 0, 1⟩ := by
      obtain ⟨tx, rx, nx⟩ := labX
      simp only at hF4
      subst hF4
      have hrx : rx = 0 := by
        have h := hΛX
        dsimp only [LargeEvenInLambda2] at h
        exact h.2
      have hnx : nx = 1 := hn1
      rw [hrx, hnx]
    subst labX
    have hF4mem := lo13_f4_orbits D hDmem o ho hoq
    rcases hF4mem with hCo | hFo
    · rw [hCo] at hΛo hlabo
      refine ⟨⟨.C, 3, 1⟩, ⟨.F4, 0, 1⟩, hΛo, hΛX, ?_, hlabo, hhX⟩
      rw [hp3]
      exact lo13_row_C3_F4
    · rw [hFo] at hTo
      exact absurd hTo ((lo13_noLine_of lo13_f4_noLine T))

end CFSG.StandardType

end
