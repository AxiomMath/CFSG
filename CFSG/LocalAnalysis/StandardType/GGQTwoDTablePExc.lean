module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDTablePDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNExcKacDatum
public import CFSG.LocalAnalysis.StandardType.GGKacTable
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private local instance (priority := high) ggDelUExc_decidableEqLargeEvenLabel :
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

private local instance (priority := high) ggDelUExc_decidableEqGGKacOrbit :
    DecidableEq GGKacOrbit :=
  fun a b =>
    match a, b with
    | ⟨la, qa⟩, ⟨lb, qb⟩ =>
      if h1 : la = lb then
        if h2 : qa = qb then isTrue (by cases h1; cases h2; rfl)
        else isFalse (by intro h; injection h with _ h2'; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _; exact h1 h1')

private local instance (priority := high) ggDelUExc_decidableEqGGKacDatum :
    DecidableEq GGKacDatum :=
  fun a b =>
    match a, b with
    | ⟨oa, za, sa⟩, ⟨ob, zb, sb⟩ =>
      if h1 : oa = ob then
        if h2 : za = zb then
          if h3 : sa = sb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private theorem ggDelUExc_e6_check :
    ∀ D ∈ ggKacTable .E6 false 3 1, ∀ o ∈ D.orbits, o.qs = true →
      ¬ (o.lab.tag = .twA ∧ 4 ≤ o.lab.rank) := by decide +kernel

private theorem ggDelUExc_twE6_check :
    ∀ D ∈ ggKacTable .E6 true 3 1, ∀ o ∈ D.orbits, o.qs = true →
      o.lab.tag = .twA → o.lab.rank ≤ 5 := by decide +kernel

private theorem ggDelUExc_twE6_sigma_check :
    ∀ D ∈ ggKacTable .E6 true 3 1, (∃ o ∈ D.orbits, o.qs = true ∧ o.lab = ⟨.twA, 4, 1⟩) →
      ∃ o ∈ D.orbits, o.lab = ⟨.A, 1, 1⟩ ∧ o.qs = false := by decide +kernel

private theorem ggDelUExc_e7_check :
    ∀ D ∈ ggKacTable .E7 false 3 1, ∀ o ∈ D.orbits, o.qs = true →
      o.lab.tag = .twA → o.lab.rank = 5 ∨ o.lab.rank = 6 := by decide +kernel

private theorem ggDelUExc_e8_check :
    ∀ D ∈ ggKacTable .E8 false 3 1, ∀ o ∈ D.orbits, o.qs = true →
      o.lab.tag = .twA → o.lab.rank = 8 := by decide +kernel

private theorem ggDelUExc_f4_check :
    ∀ D ∈ ggKacTable .F4 false 3 1, ∀ o ∈ D.orbits, o.qs = true →
      ¬ (o.lab.tag = .twA ∧ 4 ≤ o.lab.rank) := by decide +kernel

private theorem ggDelUExc_row_twA5_twE6 :
    GGTablePRow 3 ⟨.twA, 5, 1⟩ ⟨.twE6, 0, 1⟩ := by
  unfold GGTablePRow
  simp

private theorem ggDelUExc_row_twA6_E7 :
    GGTablePRow 3 ⟨.twA, 6, 1⟩ ⟨.E7, 0, 1⟩ := by
  unfold GGTablePRow
  simp

private theorem ggDelUExc_row_twA8_E8 :
    GGTablePRow 3 ⟨.twA, 8, 1⟩ ⟨.E8, 0, 1⟩ := by
  unfold GGTablePRow
  simp

private theorem ggDelUExc_classify
    (hBS : GGK0ExcBS) {p n : ℕ} {X : Type} [Group X] [Finite X]
    {A Ab : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    {labJ labX : LargeEvenLabel} {d : ℕ}
    (hd : GGTPNDatumB p n (fun _ _ => True) A Ab σ J)
    (hΛX : LargeEvenInLambda2 labX) (hpair : GGKacExcPair labX p)
    (hhX : GGHasLabel labX (X ⧸ Subgroup.center X))
    (hΛJ : LargeEvenInLambda2 labJ) (hhJ : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hk : GGTPNKernel A σ J) (hd5 : 5 ≤ d) (hlabJ : labJ = ⟨.twA, d - 1, 1⟩) :
    (labX = ⟨.twE6, 0, 1⟩ ∧ d = 6) ∨ (labX = ⟨.E7, 0, 1⟩ ∧ d = 7) ∨
      (labX = ⟨.E8, 0, 1⟩ ∧ d = 9) ∨ (labX = ⟨.E7, 0, 1⟩ ∧ d = 6) := by
  obtain ⟨D, hDval, ha, -, -, -, hSig⟩ := ggTPNExcKac_datum_sigma hBS hd hΛX hpair hhX
  have hsc : GGTPNSelfCent p A := hd.1.2.2.2.2.2.1
  have hJfix : IsComponentOf J (ggFixSub σ) := by
    have hsub : ggFixSub σ = ggAutFixedSubgroup σ := by
      ext x; simp [ggFixSub, ggAutFixedSubgroup]
    rw [hsub]
    exact hd.1.1.2.2.2.1
  obtain ⟨o, ho, hoq, hdvd, hΛo, hlabo⟩ := ha J hJfix
  have hiso : GGLabelIso labJ o.lab :=
    ggLabelRigidInput_holds labJ o.lab (↥J ⧸ Subgroup.center ↥J) hΛJ hΛo hhJ hlabo
  have hlaboeq : o.lab = ⟨.twA, d - 1, 1⟩ := by
    rw [hlabJ] at hiso
    exact ggLabelIso_twA_left (by omega) hiso
  have hn1 : labX.n = 1 := by
    have h := hdvd
    rw [hlaboeq] at h
    simpa using h
  have hp3 : p = 3 := by
    obtain ⟨hpp, hp2, hdiv, -⟩ := hpair
    rw [hn1] at hdiv
    norm_num at hdiv
    have hp2le := hpp.two_le
    rcases hdiv with h | h
    · omega
    · have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) h
      omega
  obtain ⟨Tk, tw, hty, hDmem⟩ := hDval
  rw [hn1, hp3] at hDmem
  obtain ⟨-, -, -, htag⟩ := hpair
  rcases htag with hE6 | htwE6 | hE7 | hE8 | hF4
  ·
    have hty' : ggKacTypeOfLabel labX = some (.E6, false) := by
      obtain ⟨tx, rx, nx⟩ := labX
      simp only at hE6
      subst hE6
      rfl
    obtain ⟨rfl, rfl⟩ := Option.some.inj (hty.symm.trans hty')
    have hrank : o.lab.rank = d - 1 := by rw [hlaboeq]
    exact absurd ⟨by rw [hlaboeq], by rw [hrank]; omega⟩
      (ggDelUExc_e6_check D hDmem o ho hoq)
  ·
    have hty' : ggKacTypeOfLabel labX = some (.E6, true) := by
      obtain ⟨tx, rx, nx⟩ := labX
      simp only at htwE6
      subst htwE6
      rfl
    obtain ⟨rfl, rfl⟩ := Option.some.inj (hty.symm.trans hty')
    have hrank : o.lab.rank = d - 1 := by rw [hlaboeq]
    have hrk := ggDelUExc_twE6_check D hDmem o ho hoq (by rw [hlaboeq])
    rw [hrank] at hrk
    have hd6' : d = 6 := by
      by_contra hd6'
      obtain rfl : d = 5 := by omega
      obtain ⟨o', ho', hlab', hqs'⟩ :=
        ggDelUExc_twE6_sigma_check D hDmem ⟨o, ho, hoq, hlaboeq⟩
      obtain ⟨t, ht3, htA, htJ, htσ⟩ := hSig o' ho' hlab' hqs'
      refine htσ (hk _ (hsc t htA ht3) fun j hj => ?_)
      change t * j * t⁻¹ = j
      rw [htJ J hJfix j hj, mul_inv_cancel_right]
    have hXeq : labX = ⟨.twE6, 0, 1⟩ := by
      obtain ⟨tx, rx, nx⟩ := labX
      simp only at htwE6
      subst htwE6
      have hrx : rx = 0 := by
        have h := hΛX
        dsimp only [LargeEvenInLambda2] at h
        exact h.2
      have hnx : nx = 1 := hn1
      rw [hrx, hnx]
    exact Or.inl ⟨hXeq, hd6'⟩
  ·
    have hty' : ggKacTypeOfLabel labX = some (.E7, false) := by
      obtain ⟨tx, rx, nx⟩ := labX
      simp only at hE7
      subst hE7
      rfl
    obtain ⟨rfl, rfl⟩ := Option.some.inj (hty.symm.trans hty')
    have hrank : o.lab.rank = d - 1 := by rw [hlaboeq]
    have hrk := ggDelUExc_e7_check D hDmem o ho hoq (by rw [hlaboeq])
    rw [hrank] at hrk
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
    rcases hrk with h5 | h6
    · exact Or.inr (Or.inr (Or.inr ⟨hXeq, by omega⟩))
    · exact Or.inr (Or.inl ⟨hXeq, by omega⟩)
  ·
    have hty' : ggKacTypeOfLabel labX = some (.E8, false) := by
      obtain ⟨tx, rx, nx⟩ := labX
      simp only at hE8
      subst hE8
      rfl
    obtain ⟨rfl, rfl⟩ := Option.some.inj (hty.symm.trans hty')
    have hrank : o.lab.rank = d - 1 := by rw [hlaboeq]
    have hrk : o.lab.rank = 8 :=
      ggDelUExc_e8_check D hDmem o ho hoq (by rw [hlaboeq])
    rw [hrank] at hrk
    have hd9 : d = 9 := by omega
    have hXeq : labX = ⟨.E8, 0, 1⟩ := by
      obtain ⟨tx, rx, nx⟩ := labX
      simp only at hE8
      subst hE8
      have hrx : rx = 0 := by
        have h := hΛX
        dsimp only [LargeEvenInLambda2] at h
        exact h.2
      have hnx : nx = 1 := hn1
      rw [hrx, hnx]
    exact Or.inr (Or.inr (Or.inl ⟨hXeq, hd9⟩))
  ·
    have hty' : ggKacTypeOfLabel labX = some (.F4, false) := by
      obtain ⟨tx, rx, nx⟩ := labX
      simp only at hF4
      subst hF4
      rfl
    obtain ⟨rfl, rfl⟩ := Option.some.inj (hty.symm.trans hty')
    have hrank : o.lab.rank = d - 1 := by rw [hlaboeq]
    exact absurd ⟨by rw [hlaboeq], by rw [hrank]; omega⟩
      (ggDelUExc_f4_check D hDmem o ho hoq)

theorem ggDelUExcOneThree_holds
    (hBS : GGK0ExcBS) (hSU3 : GGQTwoDE7SU6Cof) : GGDelUExcOneThreeRK := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨⟨hp3, d, hd5, hn, hlabJ⟩, hpair, hcen, hnx, -⟩ := hr
  subst hp3
  rcases ggDelUExc_classify hBS hd hΛX hpair hhX hΛJ hhJ hk hd5 hlabJ with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd ⟨Or.inr rfl, rfl⟩ hcen
  · norm_num at hlabJ
    subst hlabJ
    exact ⟨⟨.twA, 6, 1⟩, ⟨.E7, 0, 1⟩, hΛJ, hΛX, ggDelUExc_row_twA6_E7, hhJ, hhX⟩
  · norm_num at hlabJ
    subst hlabJ
    exact ⟨⟨.twA, 8, 1⟩, ⟨.E8, 0, 1⟩, hΛJ, hΛX, ggDelUExc_row_twA8_E8, hhJ, hhX⟩
  · norm_num at hlabJ
    subst hlabJ
    exfalso
    exact hSU3 X A Ab σ J n hd hk hhJ hhX (by rw [hn])

theorem ggDelUE6Three_holds
    (hBS : GGK0ExcBS) : GGDelUE6ThreeRK := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨⟨hp3, d, hd5, hn, hlabJ⟩, htagX, -, hpair⟩ := hr
  subst hp3
  rcases ggDelUExc_classify hBS hd hΛX hpair hhX hΛJ hhJ hk hd5 hlabJ with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · norm_num at hlabJ
    subst hlabJ
    exact ⟨⟨.twA, 5, 1⟩, ⟨.twE6, 0, 1⟩, hΛJ, hΛX, ggDelUExc_row_twA5_twE6, hhJ, hhX⟩
  · simp at htagX
  · simp at htagX
  · simp at htagX

end CFSG.StandardType

end
