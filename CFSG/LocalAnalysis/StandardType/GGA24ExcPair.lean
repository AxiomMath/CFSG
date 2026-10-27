module

public import CFSG.LocalAnalysis.StandardType.GGA24Defs
public import CFSG.LocalAnalysis.StandardType.GGKacExcB2
public import CFSG.LocalAnalysis.StandardType.GGTPNExcKacDatum
public import CFSG.LocalAnalysis.StandardType.GGTPNExcTwoSlices
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUClauses
public import CFSG.LocalAnalysis.StandardType.GGE6TwoCenter
public import CFSG.LocalAnalysis.StandardType.GGE6TwoLocalRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private local instance (priority := high) a24xDecidableEqLargeEvenLabel :
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

private local instance (priority := high) a24xDecidableEqGGKacOrbit : DecidableEq GGKacOrbit :=
  fun a b =>
    match a, b with
    | ⟨la, qa⟩, ⟨lb, qb⟩ =>
      if h1 : la = lb then
        if h2 : qa = qb then isTrue (by cases h1; cases h2; rfl)
        else isFalse (by intro h; injection h with _ h2'; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _; exact h1 h1')

private local instance (priority := high) a24xDecidableEqGGKacDatum : DecidableEq GGKacDatum :=
  fun a b =>
    match a, b with
    | ⟨oa, za, sa⟩, ⟨ob, zb, sb⟩ =>
      if h1 : oa = ob then
        if h2 : za = zb then
          if h3 : sa = sb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private theorem a24x_fixSub_eq {X : Type*} [Group X] (σ : MulAut X) :
    ggFixSub σ = ggAutFixedSubgroup σ := by
  ext x; simp [ggFixSub, ggAutFixedSubgroup]

private theorem a24x_iso_A22 {l : LargeEvenLabel} (h : GGLabelIso ⟨.A, 2, 2⟩ l) :
    l = ⟨.A, 2, 2⟩ := by
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · exact h.symm
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · exact absurd (congrArg LargeEvenLabel.rank h.1) (by simp)
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · exact absurd (congrArg LargeEvenLabel.rank h.2) (by simp)

private theorem a24x_two_qs_false {p : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X]
    {σ : MulAut X} {J : Subgroup X} {D : GGKacDatum}
    (honly : GGTPNOnlyComp p σ J)
    (hc : ∀ J' : Subgroup X, IsComponentOf J' (ggFixSub σ) → p ∣ Nat.card J')
    (he : GGKacCompBij D X σ)
    (h2 : 2 ≤ Fintype.card {i : Fin D.orbits.length // D.orbits[i].qs = true}) : False := by
  obtain ⟨f, -⟩ := he
  have hfix : ggFixSub σ = ggAutFixedSubgroup σ := a24x_fixSub_eq σ
  have hsub : Subsingleton {J' : Subgroup X // IsComponentOf J' (ggFixSub σ)} :=
    ⟨fun a b => Subtype.ext (by
      rw [eq_of_isComponentOf_of_ggTPNOnlyComp honly (hfix ▸ a.2) (hc a.1 a.2),
          eq_of_isComponentOf_of_ggTPNOnlyComp honly (hfix ▸ b.2) (hc b.1 b.2)])⟩
  haveI : Subsingleton {i : Fin D.orbits.length // D.orbits[i].qs = true} :=
    ⟨fun x y => f.symm.injective (Subsingleton.elim (f.symm x) (f.symm y))⟩
  have hle : Fintype.card {i : Fin D.orbits.length // D.orbits[i].qs = true} ≤ 1 :=
    Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  omega

private abbrev A24Check (T : GGKacType) (tw : Bool) (n : ℕ) : Prop :=
  ∀ D ∈ ggKacTable T tw 3 n, ⟨⟨.A, 2, 2⟩, true⟩ ∈ D.orbits →
    2 ≤ Fintype.card {i : Fin D.orbits.length // D.orbits[i].qs = true}

private theorem a24x_chk_1 : A24Check .E6 false 2 := by decide +kernel
private theorem a24x_chk_2 : A24Check .E6 true 1 := by decide +kernel
private theorem a24x_chk_3 : A24Check .E6 true 2 := by decide +kernel
private theorem a24x_chk_4 : A24Check .E7 false 1 := by decide +kernel
private theorem a24x_chk_5 : A24Check .E7 false 2 := by decide +kernel
private theorem a24x_chk_6 : A24Check .E8 false 1 := by decide +kernel
private theorem a24x_chk_7 : A24Check .E8 false 2 := by decide +kernel
private theorem a24x_chk_8 : A24Check .F4 false 1 := by decide +kernel
private theorem a24x_chk_9 : A24Check .F4 false 2 := by decide +kernel

private theorem a24x_type_eq {labX : LargeEvenLabel} {T : GGKacType} {tw : Bool}
    {T0 : GGKacType} {tw0 : Bool} (h : ggKacTypeOfLabel labX = some (T, tw))
    (h0 : ggKacTypeOfLabel labX = some (T0, tw0)) : T = T0 ∧ tw = tw0 := by
  have h' := Option.some.inj (h.symm.trans h0)
  exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩

private theorem a24x_lab_eq_E6 {labX : LargeEvenLabel} (ht : labX.tag = .E6)
    (hΛ : LargeEvenInLambda2 labX) (hn : labX.n = 1) : labX = ⟨.E6, 0, 1⟩ := by
  obtain ⟨t, r, nn⟩ := labX
  change t = .E6 at ht
  subst ht
  have hr : r = 0 := by simpa using hΛ.2
  have hn' : nn = 1 := by simpa using hn
  rw [hr, hn']

theorem ggA24ExcPairRK_holds
    (hBS : GGK0ExcBS) : GGA24ExcPairRK := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨⟨hp3, hlabJ⟩, hpair⟩ := hr
  subst hp3
  subst hlabJ
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨D, hDval, ha, hb, hc, he⟩ := ggTPNExcKac_datum hBS hd hΛX hpair hhX
  have hfix : ggFixSub σ = ggAutFixedSubgroup σ := a24x_fixSub_eq σ
  have hJfix : IsComponentOf J (ggFixSub σ) := by
    rw [hfix]; exact hd.1.1.2.2.2.1
  obtain ⟨o, ho, hoq, hdvd, hΛo, hlabo⟩ := ha J hJfix
  have hiso : GGLabelIso ⟨.A, 2, 2⟩ o.lab :=
    ggLabelRigidInput_holds ⟨.A, 2, 2⟩ o.lab (↥J ⧸ Subgroup.center ↥J) hΛJ hΛo hhJ hlabo
  have hlabo' : o.lab = ⟨.A, 2, 2⟩ := a24x_iso_A22 hiso
  have hdvd2 : labX.n ∣ 2 := by
    have h := hdvd
    rw [hlabo'] at h
    simpa using h
  have hnX : labX.n = 1 ∨ labX.n = 2 := (Nat.dvd_prime Nat.prime_two).mp hdvd2
  have ho_eq : o = ⟨⟨.A, 2, 2⟩, true⟩ := by
    obtain ⟨ol, oq⟩ := o
    change ol = ⟨.A, 2, 2⟩ at hlabo'
    change oq = true at hoq
    rw [hlabo', hoq]
  have hoC : (⟨⟨.A, 2, 2⟩, true⟩ : GGKacOrbit) ∈ D.orbits := by
    rw [← ho_eq]; exact ho
  obtain ⟨T, tw, hty, hDmem⟩ := hDval
  obtain ⟨hlocCore, -, -, -, -, -, honly, -⟩ := hd.1
  rcases hpair.2.2.2 with hE6 | htwE6 | hE7 | hE8 | hF4
  ·
    have h0 : ggKacTypeOfLabel labX = some (.E6, false) := by
      obtain ⟨t, r, nn⟩ := labX
      change t = .E6 at hE6
      subst hE6
      rfl
    obtain ⟨rfl, rfl⟩ := a24x_type_eq hty h0
    rcases hnX with hn1 | hn2
    · have hlabX : labX = ⟨.E6, 0, 1⟩ := a24x_lab_eq_E6 hE6 hΛX hn1
      exact (ltqSl_T4 (ggE6TwoCenterBot_holds) (ggE6TwoLocalRankThree_holds) hd
        (hlabX ▸ hhX) hhJ).elim
    · have hmem : D ∈ ggKacTable .E6 false 3 2 := by simpa [hn2] using hDmem
      exact (a24x_two_qs_false honly hc he (a24x_chk_1 D hmem hoC)).elim
  ·
    have h0 : ggKacTypeOfLabel labX = some (.E6, true) := by
      obtain ⟨t, r, nn⟩ := labX
      change t = .twE6 at htwE6
      subst htwE6
      rfl
    obtain ⟨rfl, rfl⟩ := a24x_type_eq hty h0
    rcases hnX with hn1 | hn2
    · have hmem : D ∈ ggKacTable .E6 true 3 1 := by simpa [hn1] using hDmem
      exact (a24x_two_qs_false honly hc he (a24x_chk_2 D hmem hoC)).elim
    · have hmem : D ∈ ggKacTable .E6 true 3 2 := by simpa [hn2] using hDmem
      exact (a24x_two_qs_false honly hc he (a24x_chk_3 D hmem hoC)).elim
  ·
    have h0 : ggKacTypeOfLabel labX = some (.E7, false) := by
      obtain ⟨t, r, nn⟩ := labX
      change t = .E7 at hE7
      subst hE7
      rfl
    obtain ⟨rfl, rfl⟩ := a24x_type_eq hty h0
    rcases hnX with hn1 | hn2
    · have hmem : D ∈ ggKacTable .E7 false 3 1 := by simpa [hn1] using hDmem
      exact (a24x_two_qs_false honly hc he (a24x_chk_4 D hmem hoC)).elim
    · have hmem : D ∈ ggKacTable .E7 false 3 2 := by simpa [hn2] using hDmem
      exact (a24x_two_qs_false honly hc he (a24x_chk_5 D hmem hoC)).elim
  ·
    have h0 : ggKacTypeOfLabel labX = some (.E8, false) := by
      obtain ⟨t, r, nn⟩ := labX
      change t = .E8 at hE8
      subst hE8
      rfl
    obtain ⟨rfl, rfl⟩ := a24x_type_eq hty h0
    rcases hnX with hn1 | hn2
    · have hmem : D ∈ ggKacTable .E8 false 3 1 := by simpa [hn1] using hDmem
      exact (a24x_two_qs_false honly hc he (a24x_chk_6 D hmem hoC)).elim
    · have hmem : D ∈ ggKacTable .E8 false 3 2 := by simpa [hn2] using hDmem
      exact (a24x_two_qs_false honly hc he (a24x_chk_7 D hmem hoC)).elim
  ·
    have h0 : ggKacTypeOfLabel labX = some (.F4, false) := by
      obtain ⟨t, r, nn⟩ := labX
      change t = .F4 at hF4
      subst hF4
      rfl
    obtain ⟨rfl, rfl⟩ := a24x_type_eq hty h0
    rcases hnX with hn1 | hn2
    · have hmem : D ∈ ggKacTable .F4 false 3 1 := by simpa [hn1] using hDmem
      exact (a24x_two_qs_false honly hc he (a24x_chk_8 D hmem hoC)).elim
    · have hmem : D ∈ ggKacTable .F4 false 3 2 := by simpa [hn2] using hDmem
      exact (a24x_two_qs_false honly hc he (a24x_chk_9 D hmem hoC)).elim

end CFSG.StandardType

end
