module

public import CFSG.LocalAnalysis.StandardType.GGB36Defs
public import CFSG.LocalAnalysis.StandardType.GGK0CompREMult
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUClauses
public import CFSG.LocalAnalysis.StandardType.GGKacTable
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private local instance (priority := high) ltqF4sDecidableEqLargeEvenLabel :
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

private local instance (priority := high) ltqF4sDecidableEqGGKacOrbit :
    DecidableEq GGKacOrbit :=
  fun a b =>
    match a, b with
    | ⟨la, qa⟩, ⟨lb, qb⟩ =>
      if h1 : la = lb then
        if h2 : qa = qb then isTrue (by cases h1; cases h2; rfl)
        else isFalse (by intro h; injection h with _ h2'; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _; exact h1 h1')

private local instance (priority := high) ltqF4sDecidableEqGGKacDatum :
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

private theorem ltqF4s_three_dvd (n : ℕ) : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := by
  induction n with
  | zero => left; norm_num
  | succ n ih =>
    rcases ih with h | h
    · right
      obtain ⟨k, hk⟩ := h
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      refine ⟨2 * k + 1, ?_⟩
      rw [pow_succ]; omega
    · left
      obtain ⟨k, hk⟩ := h
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      refine ⟨2 * k - 1, ?_⟩
      rw [pow_succ]; omega

private theorem ltqF4s_kacRE {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (htag : lab.tag = .F4) : GGKacRE lab 3 := by
  refine ⟨by norm_num, by norm_num, ltqF4s_three_dvd lab.n, ?_⟩
  exact Or.inl ⟨htag, rfl⟩

private theorem ltqF4s_rig {labX : LargeEvenLabel} (htag : labX.tag = .F4) :
    ∀ l : LargeEvenLabel, LargeEvenInLambda2 l → GGLabelIso labX l → l = labX := by
  intro l _ hiso
  obtain ⟨tx, rx, nx⟩ := labX
  obtain ⟨t, r, n⟩ := l
  simp only at htag
  subst htag
  unfold GGLabelIso at hiso
  rcases hiso with h | h | h | h | h | h | h | h <;> simp_all

private theorem ltqF4s_tag_iso_of_C {lab l : LargeEvenLabel} (h : GGLabelIso lab l)
    (hl : l.tag = .C) : lab.tag = .B ∨ lab.tag = .C := by
  obtain ⟨tl, rl, nl⟩ := lab
  obtain ⟨t, r, n⟩ := l
  simp only at hl
  subst hl
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem ltqF4s_tag_iso_of_F4 {lab l : LargeEvenLabel} (h : GGLabelIso lab l)
    (hl : l.tag = .F4) : lab.tag = .F4 := by
  obtain ⟨tl, rl, nl⟩ := lab
  obtain ⟨t, r, n⟩ := l
  simp only at hl
  subst hl
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem ltqF4s_tag_of_GGB36JLabel {labL labJ : LargeEvenLabel}
    (h : GGB36JLabel labL labJ) :
    labJ.tag = .D ∨ labJ.tag = .A ∨ labJ.tag = .triD4 ∨ labJ.tag = .twD ∨ labJ.tag = .twA := by
  unfold GGB36JLabel at h
  rcases h with ⟨-, -, h | h | h | h | h⟩ | ⟨-, -, h | h | ⟨h1, h⟩⟩ |
    ⟨-, -, h | h⟩ | ⟨-, -, h | h | h | h | h | ⟨h1, h⟩⟩ <;> rw [h] <;> simp

private theorem ltqF4s_label_eq {lab : LargeEvenLabel} {t : LargeEvenLieTag} {r n : ℕ}
    (ht : lab.tag = t) (hr : lab.rank = r) (hn : lab.n = n) : lab = ⟨t, r, n⟩ := by
  obtain ⟨t', r', n'⟩ := lab
  simp only at ht hr hn
  subst ht; subst hr; subst hn; rfl

private theorem ltqF4s_shape_eq_C3 {m k : ℕ} {o : GGKacOrbit}
    (h : ggKacShapeLabel m o.lab = (.C, 3, k)) :
    o.lab.tag = .C ∧ o.lab.rank = 3 ∧ o.lab.n / m = k := by
  unfold ggKacShapeLabel at h
  split at h
  · simp at h
  · simp only [Prod.mk.injEq] at h
    exact ⟨h.1, h.2.1, h.2.2⟩

private theorem ltqF4s_shape_eq_F4 {m k : ℕ} {o : GGKacOrbit}
    (h : ggKacShapeLabel m o.lab = (.F4, 0, k)) :
    o.lab.tag = .F4 ∧ o.lab.rank = 0 ∧ o.lab.n / m = k := by
  unfold ggKacShapeLabel at h
  split at h
  · simp at h
  · simp only [Prod.mk.injEq] at h
    exact ⟨h.1, h.2.1, h.2.2⟩

private theorem ltqF4s_label_of_shape {m : ℕ} {o : GGKacOrbit} (hdvd : m ∣ o.lab.n)
    (h : ggKacShapeLabel m o.lab = (.C, 3, 1) ∨
      ggKacShapeLabel m o.lab = (.F4, 0, 1)) :
    o.lab = ⟨.C, 3, m⟩ ∨ o.lab = ⟨.F4, 0, m⟩ := by
  rcases h with h | h
  · left
    obtain ⟨ht, hr, hdiv⟩ := ltqF4s_shape_eq_C3 h
    have hn : o.lab.n = m := by
      have h1 : o.lab.n / m * m = o.lab.n := Nat.div_mul_cancel hdvd
      rw [hdiv] at h1; simpa using h1.symm
    exact ltqF4s_label_eq ht hr hn
  · right
    obtain ⟨ht, hr, hdiv⟩ := ltqF4s_shape_eq_F4 h
    have hn : o.lab.n = m := by
      have h1 : o.lab.n / m * m = o.lab.n := Nat.div_mul_cancel hdvd
      rw [hdiv] at h1; simpa using h1.symm
    exact ltqF4s_label_eq ht hr hn

private theorem ltqF4s_fin1_len :
    ∀ D' ∈ ggKacTable .F4 false 3 1, (∃ o' ∈ D'.orbits, o'.qs = true) →
      D'.orbits.length = 1 := by
  decide

private theorem ltqF4s_fin1 :
    ∀ D' ∈ ggKacTable .F4 false 3 1, D'.orbits.length = 1 →
      ∀ o' ∈ D'.orbits,
        ggKacShapeLabel 1 o'.lab = (.C, 3, 1) ∨
          ggKacShapeLabel 1 o'.lab = (.F4, 0, 1) := by
  decide

private theorem ltqF4s_fin2 :
    ∀ D' ∈ ggKacTable .F4 false 3 2, D'.orbits.length = 1 →
      ∀ o' ∈ D'.orbits,
        ggKacShapeLabel 2 o'.lab = (.C, 3, 1) ∨
          ggKacShapeLabel 2 o'.lab = (.F4, 0, 1) := by
  decide

private theorem ltqF4s_extract {m n₀ : ℕ}
    (hshape : (↑((ggKacTable .F4 false 3 m).map (GGKacDatum.shape m)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
      ↑((ggKacTable .F4 false 3 n₀).map (GGKacDatum.shape n₀)))
    {D : GGKacDatum} (hD : D ∈ ggKacTable .F4 false 3 m)
    {o : GGKacOrbit} (ho : o ∈ D.orbits) :
    ∃ D' ∈ ggKacTable .F4 false 3 n₀, ∃ o' ∈ D'.orbits,
      ggKacShapeLabel n₀ o'.lab = ggKacShapeLabel m o.lab ∧
      GGKacDatum.shape n₀ D' = GGKacDatum.shape m D := by
  have hmem : GGKacDatum.shape m D ∈
      (↑((ggKacTable .F4 false 3 m).map (GGKacDatum.shape m)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) :=
    Multiset.mem_coe.mpr (List.mem_map.mpr ⟨D, hD, rfl⟩)
  rw [hshape] at hmem
  obtain ⟨D', hD'mem, hD'eq⟩ := List.mem_map.mp (Multiset.mem_coe.mp hmem)
  have hshapeOrb : ggKacShapeLabel m o.lab ∈
      (↑(D.orbits.map (fun o => ggKacShapeLabel m o.lab)) :
        Multiset (LargeEvenLieTag × ℕ × ℕ)) :=
    Multiset.mem_coe.mpr (List.mem_map.mpr ⟨o, ho, rfl⟩)
  have hfst : (↑(D.orbits.map (fun o => ggKacShapeLabel m o.lab)) :
        Multiset (LargeEvenLieTag × ℕ × ℕ)) =
      ↑(D'.orbits.map (fun o => ggKacShapeLabel n₀ o.lab)) := by
    have := congrArg Prod.fst hD'eq
    simpa [GGKacDatum.shape] using this.symm
  rw [hfst] at hshapeOrb
  obtain ⟨o', ho', heqo⟩ := List.mem_map.mp (Multiset.mem_coe.mp hshapeOrb)
  exact ⟨D', hD'mem, o', ho', heqo, hD'eq⟩


theorem ggTablePKnownRK_b36JExc_F4
    (hRE : GGK0CompREMult) :
    GGTablePKnownRK fun p n labJ labX => GGRegimeB36J p n labJ labX ∧ labX.tag = .F4 := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨hp3, -, labL, htagL, hJL⟩ := hr.1
  obtain htagX := hr.2
  subst hp3
  have hcore : GGTPNLocalCore 3 A σ J := hd.1.1
  have hmarked : GGTPNMarked 3 (fun _ _ => True) A := hd.1.2.2.2.2.2.2.2
  obtain ⟨hcommX, lab', hlab', hraw'⟩ := hmarked
  have hHasLabel_lab' : GGHasLabel lab' (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim (fun θ _ => ⟨θ⟩)) hraw'
  have hrigid : GGLabelIso labX lab' :=
    ggLabelRigidInput_holds labX lab' (X ⧸ Subgroup.center X) hΛX hlab' hhX hHasLabel_lab'
  have hlab'_eq : lab' = labX := ltqF4s_rig htagX lab' hlab' hrigid
  subst lab'
  have hRE' : GGKacRE labX 3 := ltqF4s_kacRE hΛX htagX
  have hmult := hRE 3 labX hΛX hRE' _ hraw'
  obtain ⟨R, _, I, F, hQR⟩ := largeEvenRawDatum_exists hmult
  obtain ⟨hQ, hP⟩ := hQR
  obtain ⟨-, -, htheta⟩ := hQ
  obtain ⟨θ, -, hHalf, hInd⟩ := htheta
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
    have hx' : θ (QuotientGroup.mk' (Subgroup.center X) x) = 1 := by
      simpa [ψ] using hx
    have hx'' : QuotientGroup.mk' (Subgroup.center X) x = 1 := θ.injective (by simpa using hx')
    exact (QuotientGroup.eq_one_iff x).mp hx''
  have hσpow : σ ^ 3 = 1 := hcore.1.2 σ hcore.2.1
  have hσne : σ ≠ 1 := hcore.2.2.1
  have hφ_apply : ∀ l : X, ggInducedAut θ σ (ψ l) = ψ (σ l) := by
    intro l
    change ggInducedAut θ σ (θ (l : X ⧸ Subgroup.center X)) =
      θ ((σ l : X) : X ⧸ Subgroup.center X)
    exact ggInducedAut_apply θ σ l
  have hφ_mem : ggInducedAut θ σ ∈ I := hInd σ hcore.2.1
  obtain ⟨D, hValid, ha, hb, hc, f, hf⟩ :=
    hP X ψ hψ hker_le hcommX σ hσpow ⟨ggInducedAut θ σ, hφ_mem, hφ_apply⟩
  have hJfix : IsComponentOf J (ggFixSub σ) := by
    rw [show ggFixSub σ = ggAutFixedSubgroup σ from by
      ext x; simp [ggFixSub, ggAutFixedSubgroup]]
    exact hcore.2.2.2.1
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨o, ho, hqs, hdvd, hΛo, hlabelo⟩ := ha J hJfix
  have hfixeq : ∀ J' : Subgroup X, IsComponentOf J' (ggFixSub σ) → J' = J := by
    intro J' hJ'
    have hJ'aut : IsComponentOf J' (ggAutFixedSubgroup σ) := by
      rwa [show ggFixSub σ = ggAutFixedSubgroup σ from by
        ext x; simp [ggFixSub, ggAutFixedSubgroup]] at hJ'
    exact eq_of_isComponentOf_of_ggTPNOnlyComp hd.1.2.2.2.2.2.2.1 hJ'aut (hc J' hJ')
  have huniq : ∀ i j : Fin D.orbits.length, D.orbits[i].qs = true →
      D.orbits[j].qs = true → i = j := by
    intro i j hi hj
    have hJi : (f.symm ⟨i, hi⟩).1 = J := hfixeq _ (f.symm ⟨i, hi⟩).2
    have hJj : (f.symm ⟨j, hj⟩).1 = J := hfixeq _ (f.symm ⟨j, hj⟩).2
    have heq : f.symm ⟨i, hi⟩ = f.symm ⟨j, hj⟩ := Subtype.ext (hJi.trans hJj.symm)
    have hsub : (⟨i, hi⟩ : {i : Fin D.orbits.length // D.orbits[i].qs = true}) = ⟨j, hj⟩ := by
      simpa using congrArg f heq
    exact congrArg Subtype.val hsub
  obtain ⟨T, tw, hTtw, hDmem⟩ := hValid
  have hTtw' : ggKacTypeOfLabel labX = some (.F4, false) := by
    obtain ⟨t, r, nn⟩ := labX
    simp only at htagX
    subst htagX
    rfl
  rw [hTtw', Option.some.injEq, Prod.mk.injEq] at hTtw
  obtain ⟨rfl, rfl⟩ := hTtw
  have hrankX : labX.rank = 0 := by
    have h := hΛX
    unfold LargeEvenInLambda2 at h
    rw [htagX] at h
    exact h.2
  have hlabX : labX = ⟨.F4, 0, labX.n⟩ := ltqF4s_label_eq htagX hrankX rfl
  have hoLabel : o.lab = ⟨.C, 3, labX.n⟩ ∨ o.lab = labX := by
    by_cases hm1 : labX.n = 1
    · have hDmem1 : D ∈ ggKacTable .F4 false 3 1 := by
        rw [hm1] at hDmem
        exact hDmem
      have hlen : D.orbits.length = 1 := ltqF4s_fin1_len D hDmem1 ⟨o, ho, hqs⟩
      have hshape := ltqF4s_fin1 D hDmem1 hlen o ho
      have hshape' : ggKacShapeLabel labX.n o.lab = (.C, 3, 1) ∨
          ggKacShapeLabel labX.n o.lab = (.F4, 0, 1) := by
        rw [hm1]
        exact hshape
      rcases ltqF4s_label_of_shape hdvd hshape' with h | h
      · left; exact h
      · right; rw [hlabX]; exact h
    · have hm2 : 2 ≤ labX.n := by
        have h1 : 1 ≤ labX.n := hΛX.1
        omega
      have hall_qs : ∀ i : Fin D.orbits.length, D.orbits[i].qs = true := fun i =>
        ggKacTable_qs_of_two_le .F4 false 3 hm2 D hDmem D.orbits[i] (List.getElem_mem i.isLt)
      have hlen : D.orbits.length = 1 := by
        by_contra hne
        have h1 : 1 ≤ D.orbits.length := by
          cases h : D.orbits with
          | nil => rw [h] at ho; simp at ho
          | cons a t => simp
        have h2 : 2 ≤ D.orbits.length := by omega
        have h0 : (⟨0, by omega⟩ : Fin D.orbits.length) = ⟨1, by omega⟩ :=
          huniq ⟨0, by omega⟩ ⟨1, by omega⟩ (hall_qs ⟨0, by omega⟩) (hall_qs ⟨1, by omega⟩)
        have hv : (0 : ℕ) = 1 := by simpa using congrArg Fin.val h0
        exact absurd hv (by decide)
      have hthree := ltqF4s_three_dvd labX.n
      by_cases h1 : 3 ∣ 2 ^ labX.n - 1
      · have hshape := ggKacTable_shape .F4 false (p := 3) (n := labX.n) (n' := 2)
          (by norm_num) (by exact hΛX.1) (by norm_num) (Or.inl ⟨h1, by norm_num⟩)
        obtain ⟨D', hD'mem, o', ho', heqo, hD'eq⟩ := ltqF4s_extract hshape hDmem ho
        have hlen' : D'.orbits.length = 1 := by
          have hcard : D'.orbits.length = D.orbits.length := by
            have hc := congrArg (Multiset.card) (congrArg Prod.fst hD'eq)
            simpa [GGKacDatum.shape] using hc
          omega
        have hshape' := ltqF4s_fin2 D' hD'mem hlen' o' ho'
        have hCF : ggKacShapeLabel labX.n o.lab = (.C, 3, 1) ∨
            ggKacShapeLabel labX.n o.lab = (.F4, 0, 1) := by
          rcases hshape' with h | h
          · left; exact heqo.symm.trans h
          · right; exact heqo.symm.trans h
        rcases ltqF4s_label_of_shape hdvd hCF with h | h
        · left; exact h
        · right; rw [hlabX]; exact h
      · have h2 : 3 ∣ 2 ^ labX.n + 1 := by
          rcases hthree with h | h
          · exact absurd h h1
          · exact h
        have hshape := ggKacTable_shape .F4 false (p := 3) (n := labX.n) (n' := 1)
          (by norm_num) (by exact hΛX.1) (by norm_num) (Or.inr ⟨h2, by norm_num⟩)
        obtain ⟨D', hD'mem, o', ho', heqo, hD'eq⟩ := ltqF4s_extract hshape hDmem ho
        have hlen' : D'.orbits.length = 1 := by
          have hcard : D'.orbits.length = D.orbits.length := by
            have hc := congrArg (Multiset.card) (congrArg Prod.fst hD'eq)
            simpa [GGKacDatum.shape] using hc
          omega
        have hshape' := ltqF4s_fin1 D' hD'mem hlen' o' ho'
        have hCF : ggKacShapeLabel labX.n o.lab = (.C, 3, 1) ∨
            ggKacShapeLabel labX.n o.lab = (.F4, 0, 1) := by
          rcases hshape' with h | h
          · left; exact heqo.symm.trans h
          · right; exact heqo.symm.trans h
        rcases ltqF4s_label_of_shape hdvd hCF with h | h
        · left; exact h
        · right; rw [hlabX]; exact h
  have hfalse : False := by
    have hiso : GGLabelIso labJ o.lab :=
      ggLabelRigidInput_holds labJ o.lab (J ⧸ Subgroup.center J) hΛJ hΛo hhJ hlabelo
    have htagJ' := ltqF4s_tag_of_GGB36JLabel hJL
    rcases hoLabel with hC | hF
    · have hisoC : GGLabelIso labJ ⟨.C, 3, labX.n⟩ := hC ▸ hiso
      have htagBC := ltqF4s_tag_iso_of_C hisoC rfl
      rcases htagBC with h | h <;> rcases htagJ' with h' | h' | h' | h' | h' <;>
        (rw [h] at h'; exact absurd h' (by decide))
    · have hisoF : GGLabelIso labJ labX := hF ▸ hiso
      have htagF := ltqF4s_tag_iso_of_F4 hisoF htagX
      rcases htagJ' with h' | h' | h' | h' | h' <;>
        (rw [htagF] at h'; exact absurd h' (by decide))
  exact hfalse.elim

end CFSG.StandardType

end
