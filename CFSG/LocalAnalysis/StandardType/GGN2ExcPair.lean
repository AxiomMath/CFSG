module

public import CFSG.LocalAnalysis.StandardType.GGN2Defs
public import CFSG.LocalAnalysis.StandardType.GGTPNExcKacDatum

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private local instance (priority := high) ltrn2cDecidableEqLargeEvenLabel :
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

private local instance (priority := high) ltrn2cDecidableEqGGKacOrbit : DecidableEq GGKacOrbit :=
  fun a b =>
    match a, b with
    | ⟨la, qa⟩, ⟨lb, qb⟩ =>
      if h1 : la = lb then
        if h2 : qa = qb then isTrue (by cases h1; cases h2; rfl)
        else isFalse (by intro h; injection h with _ h2'; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _; exact h1 h1')

private local instance (priority := high) ltrn2cDecidableEqGGKacDatum : DecidableEq GGKacDatum :=
  fun a b =>
    match a, b with
    | ⟨oa, za, sa⟩, ⟨ob, zb, sb⟩ =>
      if h1 : oa = ob then
        if h2 : za = zb then
          if h3 : sa = sb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private theorem ltrn2c_fixSub_eq {X : Type*} [Group X] (σ : MulAut X) :
    ggFixSub σ = ggAutFixedSubgroup σ := by
  ext x; simp [ggFixSub, ggAutFixedSubgroup]

private theorem ltrn2c_iso_twA31 {l : LargeEvenLabel} (h : GGLabelIso ⟨.twA, 3, 1⟩ l) :
    l = ⟨.twA, 3, 1⟩ ∨ l = ⟨.twD, 3, 1⟩ := by
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inl h.symm
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · exact Or.inr h.2
  · exact absurd h.1 (by decide)
  · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)

private abbrev ltrn2c_N2Check (T : GGKacType) (tw : Bool) : Prop :=
  ∀ D ∈ ggKacTable T tw 3 1, ∀ o ∈ D.orbits, o.lab ≠ ⟨.twA, 3, 1⟩ ∧ o.lab ≠ ⟨.twD, 3, 1⟩

private theorem ltrn2c_chk_1 : ltrn2c_N2Check .E6 false := by decide +kernel
private theorem ltrn2c_chk_2 : ltrn2c_N2Check .E6 true := by decide +kernel
private theorem ltrn2c_chk_3 : ltrn2c_N2Check .E7 false := by decide +kernel
private theorem ltrn2c_chk_4 : ltrn2c_N2Check .E8 false := by decide +kernel
private theorem ltrn2c_chk_5 : ltrn2c_N2Check .F4 false := by decide +kernel

private theorem ltrn2c_not_label {o : GGKacOrbit}
    (h : o.lab ≠ ⟨.twA, 3, 1⟩ ∧ o.lab ≠ ⟨.twD, 3, 1⟩)
    (h' : o.lab = ⟨.twA, 3, 1⟩ ∨ o.lab = ⟨.twD, 3, 1⟩) : False := by
  rcases h' with h' | h'
  · exact h.1 h'
  · exact h.2 h'

private theorem ltrn2c_type_eq {labX : LargeEvenLabel} {T : GGKacType} {tw : Bool}
    {T0 : GGKacType} {tw0 : Bool} (h : ggKacTypeOfLabel labX = some (T, tw))
    (h0 : ggKacTypeOfLabel labX = some (T0, tw0)) : T = T0 ∧ tw = tw0 := by
  have h' := Option.some.inj (h.symm.trans h0)
  exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩

private theorem ltrn2c_excKacDatum
    (hB : GGK0ExcB) {p n : ℕ} {X : Type} [Group X] [Finite X]
    {A Ab : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hd : GGTPNDatumB p n (fun _ _ => True) A Ab σ J) {labX : LargeEvenLabel}
    (hΛX : LargeEvenInLambda2 labX) (hpair : GGKacExcPair labX p)
    (hhX : GGHasLabel labX (X ⧸ Subgroup.center X)) :
    ∃ D : GGKacDatum, GGKacValid labX p D ∧
      (∀ J' : Subgroup X, IsComponentOf J' (ggFixSub σ) →
        ∃ o ∈ D.orbits, o.qs = true ∧ labX.n ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab ∧
          GGHasLabel o.lab (J' ⧸ Subgroup.center J')) := by
  obtain ⟨hlocCore, -, -, -, -, -, -, hmarked⟩ := hd.1
  obtain ⟨hperfX, lab', hΛlab', hraw⟩ := hmarked
  have hHasLabel_lab' : GGHasLabel lab' (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim (fun θ _ => ⟨θ⟩)) hraw
  have hiso_mark : GGLabelIso lab' labX :=
    ggLabelRigidInput_holds lab' labX (X ⧸ Subgroup.center X) hΛlab' hΛX hHasLabel_lab' hhX
  have hrawX := largeEvenRawDatum_of_ggLabelIso hiso_mark hraw
  have hmain := hB p labX hΛX hpair _ hrawX
  obtain ⟨R, _, I, F, hQR⟩ := largeEvenRawDatum_exists hmain
  obtain ⟨hQ, hP⟩ := hQR
  obtain ⟨-, -, htheta⟩ := hQ
  obtain ⟨θ, -, -, hInd⟩ := htheta
  let ψ : X →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψ : Function.Surjective ψ := by
    intro r
    obtain ⟨q, hq⟩ := θ.surjective r
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) q
    refine ⟨x, ?_⟩
    show θ (QuotientGroup.mk' (Subgroup.center X) x) = r
    rw [hx]
    exact hq
  have hker_le : ψ.ker ≤ Subgroup.center X := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : θ (QuotientGroup.mk' (Subgroup.center X) x) = 1 := by simpa [ψ] using hx
    have hx'' : QuotientGroup.mk' (Subgroup.center X) x = 1 := θ.injective (by simpa using hx')
    exact (QuotientGroup.eq_one_iff x).mp hx''
  have hσpow : σ ^ p = 1 := hlocCore.1.2 σ hlocCore.2.1
  have hφ_apply : ∀ l : X, ggInducedAut θ σ (ψ l) = ψ (σ l) := by
    intro l
    change ggInducedAut θ σ (θ (l : X ⧸ Subgroup.center X)) =
      θ ((σ l : X) : X ⧸ Subgroup.center X)
    exact ggInducedAut_apply θ σ l
  have hφ_mem : ggInducedAut θ σ ∈ I := hInd σ hlocCore.2.1
  obtain ⟨D, hDval, ha, -, -, -, -⟩ := hP X ψ hψ hker_le hperfX σ hσpow
    ⟨ggInducedAut θ σ, hφ_mem, hφ_apply⟩
  exact ⟨D, hDval, ha⟩

theorem ggN2ExcPairRK_holds
    (hB : GGK0ExcB) : GGN2ExcPairRK := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨⟨hp3, hn, hlabJ⟩, hpair⟩ := hr
  subst hp3
  subst hlabJ
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨D, hDval, ha⟩ := ltrn2c_excKacDatum hB hd hΛX hpair hhX
  have hfix : ggFixSub σ = ggAutFixedSubgroup σ := ltrn2c_fixSub_eq σ
  have hJfix : IsComponentOf J (ggFixSub σ) := by
    rw [hfix]; exact hd.1.1.2.2.2.1
  obtain ⟨o, ho, hoq, hdvd, hΛo, hlabo⟩ := ha J hJfix
  have hiso : GGLabelIso ⟨.twA, 3, 1⟩ o.lab :=
    ggLabelRigidInput_holds ⟨.twA, 3, 1⟩ o.lab (↥J ⧸ Subgroup.center ↥J) hΛJ hΛo hhJ hlabo
  have hlabo' : o.lab = ⟨.twA, 3, 1⟩ ∨ o.lab = ⟨.twD, 3, 1⟩ := ltrn2c_iso_twA31 hiso
  have hnX : labX.n = 1 := by
    rcases hlabo' with h' | h' <;> rw [h'] at hdvd <;> exact Nat.dvd_one.mp hdvd
  obtain ⟨T, tw, hty, hDmem⟩ := hDval
  rcases hpair.2.2.2 with hE6 | htwE6 | hE7 | hE8 | hF4
  ·
    have h0 : ggKacTypeOfLabel labX = some (.E6, false) := by
      obtain ⟨t, r, nn⟩ := labX
      change t = .E6 at hE6
      subst hE6
      rfl
    obtain ⟨rfl, rfl⟩ := ltrn2c_type_eq hty h0
    have hmem : D ∈ ggKacTable .E6 false 3 1 := by simpa [hnX] using hDmem
    have hchk := ltrn2c_chk_1 D hmem o ho
    exact (ltrn2c_not_label hchk hlabo').elim
  ·
    have h0 : ggKacTypeOfLabel labX = some (.E6, true) := by
      obtain ⟨t, r, nn⟩ := labX
      change t = .twE6 at htwE6
      subst htwE6
      rfl
    obtain ⟨rfl, rfl⟩ := ltrn2c_type_eq hty h0
    have hmem : D ∈ ggKacTable .E6 true 3 1 := by simpa [hnX] using hDmem
    have hchk := ltrn2c_chk_2 D hmem o ho
    exact (ltrn2c_not_label hchk hlabo').elim
  ·
    have h0 : ggKacTypeOfLabel labX = some (.E7, false) := by
      obtain ⟨t, r, nn⟩ := labX
      change t = .E7 at hE7
      subst hE7
      rfl
    obtain ⟨rfl, rfl⟩ := ltrn2c_type_eq hty h0
    have hmem : D ∈ ggKacTable .E7 false 3 1 := by simpa [hnX] using hDmem
    have hchk := ltrn2c_chk_3 D hmem o ho
    exact (ltrn2c_not_label hchk hlabo').elim
  ·
    have h0 : ggKacTypeOfLabel labX = some (.E8, false) := by
      obtain ⟨t, r, nn⟩ := labX
      change t = .E8 at hE8
      subst hE8
      rfl
    obtain ⟨rfl, rfl⟩ := ltrn2c_type_eq hty h0
    have hmem : D ∈ ggKacTable .E8 false 3 1 := by simpa [hnX] using hDmem
    have hchk := ltrn2c_chk_4 D hmem o ho
    exact (ltrn2c_not_label hchk hlabo').elim
  ·
    have h0 : ggKacTypeOfLabel labX = some (.F4, false) := by
      obtain ⟨t, r, nn⟩ := labX
      change t = .F4 at hF4
      subst hF4
      rfl
    obtain ⟨rfl, rfl⟩ := ltrn2c_type_eq hty h0
    have hmem : D ∈ ggKacTable .F4 false 3 1 := by simpa [hnX] using hDmem
    have hchk := ltrn2c_chk_5 D hmem o ho
    exact (ltrn2c_not_label hchk hlabo').elim

end CFSG.StandardType

end
