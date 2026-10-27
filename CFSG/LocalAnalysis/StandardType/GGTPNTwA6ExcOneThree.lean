module

public import CFSG.LocalAnalysis.StandardType.GGTPNTwA6Defs
public import CFSG.LocalAnalysis.StandardType.GGTPNExcKacDatum
public import CFSG.LocalAnalysis.StandardType.GGKacTable
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private local instance (priority := high) tw13DecidableEqLargeEvenLabel :
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

private local instance (priority := high) tw13DecidableEqGGKacOrbit : DecidableEq GGKacOrbit :=
  fun a b =>
    match a, b with
    | ⟨la, qa⟩, ⟨lb, qb⟩ =>
      if h1 : la = lb then
        if h2 : qa = qb then isTrue (by cases h1; cases h2; rfl)
        else isFalse (by intro h; injection h with _ h2'; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _; exact h1 h1')

private local instance (priority := high) tw13DecidableEqGGKacDatum : DecidableEq GGKacDatum :=
  fun a b =>
    match a, b with
    | ⟨oa, za, sa⟩, ⟨ob, zb, sb⟩ =>
      if h1 : oa = ob then
        if h2 : za = zb then
          if h3 : sa = sb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private theorem tw13_e7_check :
    ∀ D ∈ ggKacTable .E7 false 3 1, ∀ o ∈ D.orbits, o.qs = true →
      o.lab.tag = .twA → o.lab.rank = 6 → o.lab.n = 1 := by decide +kernel

private theorem tw13_f4_check :
    ∀ D ∈ ggKacTable .F4 false 3 1, ∀ o ∈ D.orbits, o.qs = true →
      ¬ (o.lab.tag = .twA ∧ o.lab.rank = 6) := by decide +kernel

private theorem tw13_e8_check :
    ∀ D ∈ ggKacTable .E8 false 3 1, ∀ o ∈ D.orbits, o.qs = true →
      ¬ (o.lab.tag = .twA ∧ o.lab.rank = 6) := by decide +kernel

private theorem tw13_row_twA6_E7 : GGTablePRow 3 ⟨.twA, 6, 1⟩ ⟨.E7, 0, 1⟩ := by
  unfold GGTablePRow
  simp

theorem ggTwA6ExcOneThree_holds
    (hBS : GGK0ExcBS) : GGTwA6ExcOneThreeRK := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨⟨-, -, hJtag, hJrank, -⟩, hpair, hcen, hn1, hp3⟩ := hr
  obtain ⟨D, hDval, ha, -, -, -⟩ := ggTPNExcKac_datum hBS hd hΛX hpair hhX
  have hJfix : IsComponentOf J (ggFixSub σ) := by
    have hsub : ggFixSub σ = ggAutFixedSubgroup σ := by
      ext x; simp [ggFixSub, ggAutFixedSubgroup]
    rw [hsub]
    exact hd.1.1.2.2.2.1
  obtain ⟨o, ho, hoq, hdvd, hΛo, hlabo⟩ := ha J hJfix
  obtain ⟨tJ, rJ, m⟩ := labJ
  simp only at hJtag hJrank
  subst hJtag hJrank
  have hiso : GGLabelIso ⟨.twA, 6, m⟩ o.lab :=
    ggLabelRigidInput_holds ⟨.twA, 6, m⟩ o.lab (↥J ⧸ Subgroup.center ↥J) hΛJ hΛo hhJ hlabo
  have hlaboeq : o.lab = ⟨.twA, 6, m⟩ := ggLabelIso_twA6_left hiso
  obtain ⟨Tk, tw, hty, hDmem⟩ := hDval
  rw [hn1, hp3] at hDmem
  have hnotE6 : ¬ (labX.tag = .E6 ∨ labX.tag = .twE6) := fun h => hcen ⟨h, hp3⟩
  rcases hpair.2.2.2 with hE6 | htwE6 | hE7 | hE8 | hF4
  · exact absurd (Or.inl hE6) hnotE6
  · exact absurd (Or.inr htwE6) hnotE6
  ·
    have hty' : ggKacTypeOfLabel labX = some (.E7, false) := by
      obtain ⟨tx, rx, nx⟩ := labX
      simp only at hE7
      subst hE7
      rfl
    obtain ⟨rfl, rfl⟩ := Option.some.inj (hty.symm.trans hty')
    have hm : m = 1 := by
      have h1 : o.lab.tag = .twA := by rw [hlaboeq]
      have h2 : o.lab.rank = 6 := by rw [hlaboeq]
      have h3 : o.lab.n = 1 := tw13_e7_check D hDmem o ho hoq h1 h2
      rw [hlaboeq] at h3
      exact h3
    have hlabo' : o.lab = ⟨.twA, 6, 1⟩ := by rw [hlaboeq, hm]
    have hXeq : labX = ⟨.E7, 0, 1⟩ := by
      obtain ⟨tx, rx, nx⟩ := labX
      simp only at hE7
      subst hE7
      have hrx : rx = 0 := by
        have h := hΛX
        dsimp only [LargeEvenInLambda2] at h
        exact h.2
      have hnx : nx = 1 := hn1
      rw [hrx, hnx]
    subst labX
    rw [hlabo'] at hΛo hlabo
    refine ⟨⟨.twA, 6, 1⟩, ⟨.E7, 0, 1⟩, hΛo, hΛX, ?_, hlabo, hhX⟩
    rw [hp3]
    exact tw13_row_twA6_E7
  ·
    have hty' : ggKacTypeOfLabel labX = some (.E8, false) := by
      obtain ⟨tx, rx, nx⟩ := labX
      simp only at hE8
      subst hE8
      rfl
    obtain ⟨rfl, rfl⟩ := Option.some.inj (hty.symm.trans hty')
    exact absurd ⟨by rw [hlaboeq], by rw [hlaboeq]⟩ (tw13_e8_check D hDmem o ho hoq)
  ·
    have hty' : ggKacTypeOfLabel labX = some (.F4, false) := by
      obtain ⟨tx, rx, nx⟩ := labX
      simp only at hF4
      subst hF4
      rfl
    obtain ⟨rfl, rfl⟩ := Option.some.inj (hty.symm.trans hty')
    exact absurd ⟨by rw [hlaboeq], by rw [hlaboeq]⟩ (tw13_f4_check D hDmem o ho hoq)

end CFSG.StandardType

end
