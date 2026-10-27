module

public import CFSG.LocalAnalysis.StandardType.GGB36Defs
public import CFSG.LocalAnalysis.StandardType.GGK0CompREMult
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeDatum
public import CFSG.LocalAnalysis.StandardType.GGSporKLamOrders

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private local instance (priority := high) ltqS1_decEqLargeEvenLabel : DecidableEq LargeEvenLabel :=
  fun a b =>
    match a, b with
    | ⟨ta, ra, na⟩, ⟨tb, rb, nb⟩ =>
      if h1 : ta = tb then
        if h2 : ra = rb then
          if h3 : na = nb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private local instance (priority := high) ltqS1_decEqGGKacOrbit : DecidableEq GGKacOrbit :=
  fun a b =>
    match a, b with
    | ⟨la, qa⟩, ⟨lb, qb⟩ =>
      if h1 : la = lb then
        if h2 : qa = qb then isTrue (by cases h1; cases h2; rfl)
        else isFalse (by intro h; injection h with _ h2'; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _; exact h1 h1')

private local instance (priority := high) ltqS1_decEqGGKacDatum : DecidableEq GGKacDatum :=
  fun a b =>
    match a, b with
    | ⟨oa, za, sa⟩, ⟨ob, zb, sb⟩ =>
      if h1 : oa = ob then
        if h2 : za = zb then
          if h3 : sa = sb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private theorem ltqS1_three_dvd (n : ℕ) : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := by
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

private theorem ltqS1_kacRE {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (htag : lab.tag = .E6 ∨ lab.tag = .twE6) : GGKacRE lab 3 := by
  refine ⟨by norm_num, by norm_num, ltqS1_three_dvd lab.n, ?_⟩
  rcases htag with h | h
  · exact Or.inr (Or.inl ⟨Or.inl h, Or.inl rfl⟩)
  · exact Or.inr (Or.inl ⟨Or.inr h, Or.inl rfl⟩)

private theorem ltqS1_rank_zero {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (htag : lab.tag = .E6 ∨ lab.tag = .twE6) : lab.rank = 0 := by
  rcases htag with h | h
  · unfold LargeEvenInLambda2 at hΛ
    rw [h] at hΛ
    exact hΛ.2
  · unfold LargeEvenInLambda2 at hΛ
    rw [h] at hΛ
    exact hΛ.2

private theorem ltqS1_label_eq {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (htag : lab.tag = .E6 ∨ lab.tag = .twE6) : lab = ⟨lab.tag, 0, lab.n⟩ := by
  obtain ⟨t, r, n⟩ := lab
  have hr : r = 0 := ltqS1_rank_zero hΛ htag
  subst hr
  rfl

private theorem ltqS1_rig {labX : LargeEvenLabel} (htag : labX.tag = .E6 ∨ labX.tag = .twE6) :
    ∀ l : LargeEvenLabel, LargeEvenInLambda2 l → GGLabelIso labX l → l = labX := by
  intro l _ hiso
  obtain ⟨tx, rx, nx⟩ := labX
  obtain ⟨t, r, n⟩ := l
  rcases htag with h | h <;>
    (subst h
     unfold GGLabelIso at hiso
     rcases hiso with h | h | h | h | h | h | h | h <;> simp_all)

private theorem ltqS1_labOrd_eq_card
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    {X : Type} [Group X] [Finite X] (h : GGHasLabel lab X) :
    CFSG.StandardType.SporadicShape.labOrd lab = Nat.card X := by
  refine CFSG.StandardType.SporadicShape.labOrd_eq_of_rawDatum hΛ ?_
  exact largeEvenRawDatum_mono
    (fun R _ _ _ ⟨e⟩ => (Nat.card_congr e.toEquiv).symm) h

private theorem ltqS1_eq_top_of_card_quotient_le {X : Type*} [Group X] [Finite X]
    (J₀ : Subgroup X) (hcomm : commutator X = ⊤)
    (hcard : Nat.card (X ⧸ Subgroup.center X) ≤
      Nat.card (↥J₀ ⧸ Subgroup.center ↥J₀)) :
    J₀ = ⊤ := by
  let ψ : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  have hker : ψ.ker = Subgroup.center X := QuotientGroup.ker_mk' (Subgroup.center X)
  let f : ↥J₀ →* X ⧸ Subgroup.center X := ψ.comp J₀.subtype
  have hfker : f.ker = (Subgroup.center X).comap J₀.subtype := by
    change (ψ.comp J₀.subtype).ker = _
    rw [← MonoidHom.comap_ker ψ J₀.subtype, hker]
  have hfrange : f.range = Subgroup.map ψ J₀ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hZC : (Subgroup.center X).comap J₀.subtype ≤ Subgroup.center ↥J₀ := by
    intro j hj
    rw [Subgroup.mem_comap] at hj
    rw [Subgroup.mem_center_iff]
    intro k
    have h1 := Subgroup.mem_center_iff.mp hj (k : X)
    exact Subtype.ext (by simpa using h1)
  have hindex : (Subgroup.center ↥J₀).index ≤
      ((Subgroup.center X).comap J₀.subtype).index :=
    Subgroup.index_antitone hZC
  rw [Subgroup.index_eq_card (Subgroup.center ↥J₀),
    Subgroup.index_eq_card ((Subgroup.center X).comap J₀.subtype)] at hindex
  have hiso : Nat.card (↥J₀ ⧸ (Subgroup.center X).comap J₀.subtype) =
      Nat.card (Subgroup.map ψ J₀) := by
    have h := Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    rw [hfrange] at h
    rwa [hfker] at h
  have hle : Nat.card (↥J₀ ⧸ Subgroup.center ↥J₀) ≤ Nat.card (Subgroup.map ψ J₀) :=
    hindex.trans hiso.le
  have htop : Nat.card (Subgroup.map ψ J₀) = Nat.card (X ⧸ Subgroup.center X) :=
    le_antisymm (Subgroup.card_le_card_group _) (hcard.trans hle)
  have hmap_top : Subgroup.map ψ J₀ = ⊤ :=
    Subgroup.eq_of_le_of_card_ge le_top (by rw [htop, Subgroup.card_top])
  have hsup : J₀ ⊔ Subgroup.center X = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : ψ x ∈ Subgroup.map ψ J₀ := by rw [hmap_top]; trivial
    obtain ⟨j, hj, hjx⟩ := Subgroup.mem_map.mp hx
    have hmem : j⁻¹ * x ∈ Subgroup.center X := by
      have h1 : ψ (j⁻¹ * x) = 1 := by rw [map_mul, map_inv, hjx, inv_mul_cancel]
      have h2 : j⁻¹ * x ∈ ψ.ker := MonoidHom.mem_ker.mpr h1
      rwa [hker] at h2
    have hx_eq : x = j * (j⁻¹ * x) := by group
    rw [hx_eq]
    exact Subgroup.mul_mem_sup hj hmem
  have hnorm : J₀.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply le_antisymm le_top
    rw [← hsup]
    exact sup_le Subgroup.le_normalizer (Subgroup.center_le_normalizer (J₀ : Set X))
  haveI := hnorm
  have hcomm_le : commutator X ≤ J₀ :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup
      (Subgroup.center.isMulCommutative X)
  rw [hcomm] at hcomm_le
  exact top_le_iff.mp hcomm_le

private theorem ltqS1_fin_false1 :
    ∀ D' ∈ ggKacTable .E6 false 3 1, ∀ o' ∈ D'.orbits, o'.qs = true →
      GGB36JLabel ⟨.E6, 0, 1⟩ o'.lab ∨ o'.lab = ⟨.E6, 0, 1⟩ := by
  simp only [GGB36JLabel]
  decide

private theorem ltqS1_fin_true1 :
    ∀ D' ∈ ggKacTable .E6 true 3 1, ∀ o' ∈ D'.orbits, o'.qs = true →
      GGB36JLabel ⟨.twE6, 0, 1⟩ o'.lab ∨ o'.lab = ⟨.twE6, 0, 1⟩ := by
  simp only [GGB36JLabel]
  decide

private theorem ltqS1_fin_false2 :
    ∀ D' ∈ ggKacTable .E6 false 3 2, D'.orbits.length = 1 → ∀ o' ∈ D'.orbits,
      ggKacShapeLabel 2 o'.lab ∈
        ([(.D, 5, 1), (.A, 5, 1), (.D, 4, 1), (.triD4, 0, 1), (.A, 2, 3), (.E6, 0, 1)] :
          List (LargeEvenLieTag × ℕ × ℕ)) := by
  decide

private theorem ltqS1_fin_false1shape :
    ∀ D' ∈ ggKacTable .E6 false 3 1, D'.orbits.length = 1 → ∀ o' ∈ D'.orbits,
      ggKacShapeLabel 1 o'.lab ∈
        ([(.A, 5, 1), (.twD, 4, 1), (.E6, 0, 1)] :
          List (LargeEvenLieTag × ℕ × ℕ)) := by
  decide

private theorem ltqS1_fin_true2 :
    ∀ D' ∈ ggKacTable .E6 true 3 2, D'.orbits.length = 1 → ∀ o' ∈ D'.orbits,
      ggKacShapeLabel 2 o'.lab ∈
        ([(.twA, 5, 1), (.twD, 4, 1), (.twE6, 0, 1)] :
          List (LargeEvenLieTag × ℕ × ℕ)) := by
  decide

private theorem ltqS1_fin_true1shape :
    ∀ D' ∈ ggKacTable .E6 true 3 1, D'.orbits.length = 1 → ∀ o' ∈ D'.orbits,
      ggKacShapeLabel 1 o'.lab ∈
        ([(.twD, 5, 1), (.twA, 5, 1), (.D, 4, 1), (.triD4, 0, 1), (.twA, 2, 3),
          (.twE6, 0, 1)] : List (LargeEvenLieTag × ℕ × ℕ)) := by
  decide

private theorem ltqS1_eq_of_shape {n : ℕ} {o : GGKacOrbit} {t : LargeEvenLieTag} {r k : ℕ}
    (h : ggKacShapeLabel n o.lab = (t, r, k)) (hC : t ≠ .C) (hdvd : n ∣ o.lab.n) :
    o.lab = ⟨t, r, k * n⟩ := by
  unfold ggKacShapeLabel at h
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hC
  · simp only [Prod.mk.injEq] at h
    obtain ⟨ht, hr, hk⟩ := h
    subst ht
    subst hr
    have h2 : k * n = o.lab.n := by
      rw [← hk]; exact Nat.div_mul_cancel hdvd
    rw [h2]

private theorem ltqS1_extract {T : GGKacType} {tw : Bool} {n n₀ : ℕ}
    {P : LargeEvenLieTag × ℕ × ℕ → Prop}
    (hshape : (↑((ggKacTable T tw 3 n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
      ↑((ggKacTable T tw 3 n₀).map (GGKacDatum.shape n₀)))
    {D : GGKacDatum} (hD : D ∈ ggKacTable T tw 3 n) (hlen : D.orbits.length = 1)
    {o : GGKacOrbit} (ho : o ∈ D.orbits)
    (hfin : ∀ D' ∈ ggKacTable T tw 3 n₀, D'.orbits.length = 1 → ∀ o' ∈ D'.orbits,
      P (ggKacShapeLabel n₀ o'.lab)) :
    P (ggKacShapeLabel n o.lab) := by
  have hmem : GGKacDatum.shape n D ∈
      (↑((ggKacTable T tw 3 n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) :=
    Multiset.mem_coe.mpr (List.mem_map.mpr ⟨D, hD, rfl⟩)
  rw [hshape] at hmem
  obtain ⟨D', hD'mem, hD'eq⟩ := List.mem_map.mp (Multiset.mem_coe.mp hmem)
  have hlen' : D'.orbits.length = 1 := by
    have hc := congrArg (fun x => Multiset.card x.1) hD'eq
    simpa [GGKacDatum.shape, hlen] using hc
  have hshapeOrb : ggKacShapeLabel n o.lab ∈
      (↑(D.orbits.map (fun o => ggKacShapeLabel n o.lab)) :
        Multiset (LargeEvenLieTag × ℕ × ℕ)) :=
    Multiset.mem_coe.mpr (List.mem_map.mpr ⟨o, ho, rfl⟩)
  have hfst : (↑(D.orbits.map (fun o => ggKacShapeLabel n o.lab)) :
        Multiset (LargeEvenLieTag × ℕ × ℕ)) =
      ↑(D'.orbits.map (fun o => ggKacShapeLabel n₀ o.lab)) := by
    have h := congrArg Prod.fst hD'eq
    simpa [GGKacDatum.shape] using h.symm
  rw [hfst] at hshapeOrb
  obtain ⟨o', ho', heqo⟩ := List.mem_map.mp (Multiset.mem_coe.mp hshapeOrb)
  have hfin' := hfin D' hD'mem hlen' o' ho'
  rwa [heqo] at hfin'

private theorem ltqS1_len_one {L : Type*} [Group L] {δ : MulAut L} {D' : GGKacDatum}
    {J₀ : Subgroup L}
    (huniq : ∀ Q : Subgroup L, IsComponentOf Q (ggAutFixedSubgroup δ) → Q = J₀)
    (hfix : ggFixSub δ = ggAutFixedSubgroup δ)
    (f : {J : Subgroup L // IsComponentOf J (ggFixSub δ)} ≃
      {i : Fin D'.orbits.length // D'.orbits[i].qs = true})
    (hqs_all : ∀ i : Fin D'.orbits.length, D'.orbits[i].qs = true)
    (o : GGKacOrbit) (ho : o ∈ D'.orbits) : D'.orbits.length = 1 := by
  have hle : D'.orbits.length ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ D'.orbits.length := by omega
    let i : Fin D'.orbits.length := ⟨0, by omega⟩
    let j : Fin D'.orbits.length := ⟨1, by omega⟩
    have hne : i ≠ j := by
      intro hij
      have := congrArg Fin.val hij
      simp [i, j] at this
    have hfi : (f.symm ⟨i, hqs_all i⟩).1 = J₀ :=
      huniq _ (hfix ▸ (f.symm ⟨i, hqs_all i⟩).2)
    have hfj : (f.symm ⟨j, hqs_all j⟩).1 = J₀ :=
      huniq _ (hfix ▸ (f.symm ⟨j, hqs_all j⟩).2)
    have heq : (⟨i, hqs_all i⟩ : {i : Fin D'.orbits.length // D'.orbits[i].qs = true}) =
        ⟨j, hqs_all j⟩ := by
      apply f.symm.injective
      apply Subtype.ext
      exact hfi.trans hfj.symm
    exact hne (congrArg Subtype.val heq)
  have hpos : 0 < D'.orbits.length := List.length_pos_iff.mpr (List.ne_nil_of_mem ho)
  omega

private theorem ltqS1_conv_false2 {n : ℕ} (h3 : 3 ∣ 2 ^ n - 1) {o : GGKacOrbit}
    (hdvd : n ∣ o.lab.n)
    (hsh : ggKacShapeLabel n o.lab ∈
      ([(.D, 5, 1), (.A, 5, 1), (.D, 4, 1), (.triD4, 0, 1), (.A, 2, 3), (.E6, 0, 1)] :
        List (LargeEvenLieTag × ℕ × ℕ))) :
    GGB36JLabel ⟨.E6, 0, n⟩ o.lab ∨ o.lab = ⟨.E6, 0, n⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hsh
  rcases hsh with h | h | h | h | h | h
  · left; rw [ltqS1_eq_of_shape h (by decide) hdvd]; simp [GGB36JLabel, h3]
  · left; rw [ltqS1_eq_of_shape h (by decide) hdvd]; simp [GGB36JLabel, h3]
  · left; rw [ltqS1_eq_of_shape h (by decide) hdvd]; simp [GGB36JLabel, h3]
  · left; rw [ltqS1_eq_of_shape h (by decide) hdvd]; simp [GGB36JLabel, h3]
  · left; rw [ltqS1_eq_of_shape h (by decide) hdvd]; simp [GGB36JLabel, h3]
  · right; rw [ltqS1_eq_of_shape h (by decide) hdvd]; simp

private theorem ltqS1_conv_false1 {n : ℕ} (h3 : 3 ∣ 2 ^ n + 1) {o : GGKacOrbit}
    (hdvd : n ∣ o.lab.n)
    (hsh : ggKacShapeLabel n o.lab ∈
      ([(.A, 5, 1), (.twD, 4, 1), (.E6, 0, 1)] : List (LargeEvenLieTag × ℕ × ℕ))) :
    GGB36JLabel ⟨.E6, 0, n⟩ o.lab ∨ o.lab = ⟨.E6, 0, n⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hsh
  rcases hsh with h | h | h
  · left; rw [ltqS1_eq_of_shape h (by decide) hdvd]; simp [GGB36JLabel, h3]
  · left; rw [ltqS1_eq_of_shape h (by decide) hdvd]; simp [GGB36JLabel, h3]
  · right; rw [ltqS1_eq_of_shape h (by decide) hdvd]; simp

private theorem ltqS1_conv_true2 {n : ℕ} (h3 : 3 ∣ 2 ^ n - 1) {o : GGKacOrbit}
    (hdvd : n ∣ o.lab.n)
    (hsh : ggKacShapeLabel n o.lab ∈
      ([(.twA, 5, 1), (.twD, 4, 1), (.twE6, 0, 1)] : List (LargeEvenLieTag × ℕ × ℕ))) :
    GGB36JLabel ⟨.twE6, 0, n⟩ o.lab ∨ o.lab = ⟨.twE6, 0, n⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hsh
  rcases hsh with h | h | h
  · left; rw [ltqS1_eq_of_shape h (by decide) hdvd]; simp [GGB36JLabel, h3]
  · left; rw [ltqS1_eq_of_shape h (by decide) hdvd]; simp [GGB36JLabel, h3]
  · right; rw [ltqS1_eq_of_shape h (by decide) hdvd]; simp

private theorem ltqS1_conv_true1 {n : ℕ} (h3 : 3 ∣ 2 ^ n + 1) {o : GGKacOrbit}
    (hdvd : n ∣ o.lab.n)
    (hsh : ggKacShapeLabel n o.lab ∈
      ([(.twD, 5, 1), (.twA, 5, 1), (.D, 4, 1), (.triD4, 0, 1), (.twA, 2, 3), (.twE6, 0, 1)] :
        List (LargeEvenLieTag × ℕ × ℕ))) :
    GGB36JLabel ⟨.twE6, 0, n⟩ o.lab ∨ o.lab = ⟨.twE6, 0, n⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hsh
  rcases hsh with h | h | h | h | h | h
  · left; rw [ltqS1_eq_of_shape h (by decide) hdvd]; simp [GGB36JLabel, h3]
  · left; rw [ltqS1_eq_of_shape h (by decide) hdvd]; simp [GGB36JLabel, h3]
  · left; rw [ltqS1_eq_of_shape h (by decide) hdvd]; simp [GGB36JLabel, h3]
  · left; rw [ltqS1_eq_of_shape h (by decide) hdvd]; simp [GGB36JLabel, h3]
  · left; rw [ltqS1_eq_of_shape h (by decide) hdvd]; simp [GGB36JLabel, h3]
  · right; rw [ltqS1_eq_of_shape h (by decide) hdvd]; simp

theorem ggB36StepOne_of_K0REMult
    (h : GGK0CompREMult) : GGB36StepOne := by
  intro G _ _ p B Bs x L D J hcfg hInn hp labL hΛL htagL hLabL
  obtain ⟨hI, hBstar, hDJ⟩ := hcfg
  subst hp
  obtain ⟨y, hyB, hD⟩ := exists_closure_pair_of_stdSub hI hDJ
  have hst : LargeEvenStandardType 3 B x L := hI.2.2.2.2.2.2.2
  have hNL : B ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_largeEvenStandardType hst
  set δ : MulAut ↥L := L.normalizerMonoidHom ⟨y, hNL hyB⟩ with hδdef
  set J₀ : Subgroup ↥L := J.subgroupOf L with hJ₀def
  have hdat : GGTablePThreeDatum (ggAutsOf L B hNL) δ J₀ := by
    rw [hδdef, hJ₀def]
    exact ggTablePThree_datum hI hDJ hD hyB hNL
  obtain ⟨hcomm, lab', hlab', hraw⟩ := hdat.2.2.2
  have hHasLabel_lab' : GGHasLabel lab' (↥L ⧸ Subgroup.center ↥L) :=
    largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim (fun θ _ => ⟨θ⟩)) hraw
  have hrigid : GGLabelIso labL lab' :=
    ggLabelRigidInput_holds labL lab' (↥L ⧸ Subgroup.center ↥L) hΛL hlab' hLabL
      hHasLabel_lab'
  have hlab'_eq : lab' = labL := ltqS1_rig htagL lab' hlab' hrigid
  subst lab'
  have hRE : GGKacRE labL 3 := ltqS1_kacRE hΛL htagL
  have hmain := h 3 labL hΛL hRE _ hraw
  obtain ⟨R, hRgrp, I, F, hQR⟩ := largeEvenRawDatum_exists hmain
  obtain ⟨hQ, hP⟩ := hQR
  obtain ⟨hsimple, hna, htheta⟩ := hQ
  obtain ⟨θ, hSplit, hInd⟩ := htheta
  let ψ : ↥L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hψ : Function.Surjective ψ := by
    intro r
    obtain ⟨q, hq⟩ := θ.surjective r
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) q
    refine ⟨l, ?_⟩
    show θ (QuotientGroup.mk' (Subgroup.center ↥L) l) = r
    rw [hl]
    exact hq
  have hker_le : ψ.ker ≤ Subgroup.center ↥L := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have hl' : θ (QuotientGroup.mk' (Subgroup.center ↥L) l) = 1 := by
      simpa [ψ] using hl
    have hl'' : QuotientGroup.mk' (Subgroup.center ↥L) l = 1 :=
      θ.injective (by simpa using hl')
    exact (QuotientGroup.eq_one_iff l).mp hl''
  have hσpow : δ ^ 3 = 1 := hdat.1.1.1.2 δ hdat.1.1.2.1
  have hσne : δ ≠ 1 := hdat.1.1.2.2.1
  have hJ0comp : IsComponentOf J₀ (ggAutFixedSubgroup δ) := hdat.1.1.2.2.2.1
  have hfix : ggFixSub δ = ggAutFixedSubgroup δ := by
    ext l; simp [ggFixSub, ggAutFixedSubgroup]
  have hφ_apply : ∀ l : ↥L, ggInducedAut θ δ (ψ l) = ψ (δ l) := by
    intro l
    change ggInducedAut θ δ (θ (l : ↥L ⧸ Subgroup.center ↥L)) =
      θ ((δ l : ↥L) : ↥L ⧸ Subgroup.center ↥L)
    exact ggInducedAut_apply θ δ l
  have hφ_mem : ggInducedAut θ δ ∈ I := hInd δ hdat.1.1.2.1
  have hJ : IsComponentOf J₀ (ggFixSub δ) := by rw [hfix]; exact hJ0comp
  obtain ⟨D', hValid, ha, hb, hc, hf⟩ :=
    hP ↥L ψ hψ hker_le hcomm δ hσpow ⟨ggInducedAut θ δ, hφ_mem, hφ_apply⟩
  obtain ⟨f, hf⟩ := hf
  obtain ⟨o, ho, hqs, hdvd, hΛo, hlabel_J0⟩ := ha J₀ hJ
  have huniq : ∀ Q : Subgroup ↥L, IsComponentOf Q (ggAutFixedSubgroup δ) → Q = J₀ :=
    hdat.2.1
  have hself : o.lab ≠ labL := by
    intro hself
    have hlabelL : GGHasLabel labL (↥J₀ ⧸ Subgroup.center ↥J₀) := by
      rw [hself] at hlabel_J0
      exact hlabel_J0
    have hcardL := ltqS1_labOrd_eq_card hΛL hLabL
    have hcardJ := ltqS1_labOrd_eq_card hΛL hlabelL
    have hcard : Nat.card (↥L ⧸ Subgroup.center ↥L) ≤
        Nat.card (↥J₀ ⧸ Subgroup.center ↥J₀) := by
      rw [← hcardL, hcardJ]
    have hJtop : J₀ = ⊤ := ltqS1_eq_top_of_card_quotient_le J₀ hcomm hcard
    have hδ1 : δ = 1 := MulEquiv.ext (fun l => by
      have hl : l ∈ J₀ := by rw [hJtop]; trivial
      have hfixl : l ∈ ggAutFixedSubgroup δ := hJ0comp.1 hl
      simpa [ggAutFixedSubgroup] using hfixl)
    exact hσne hδ1
  have hlabL_eq : labL = ⟨labL.tag, 0, labL.n⟩ := ltqS1_label_eq hΛL htagL
  have hJLabel : GGB36JLabel labL o.lab := by
    obtain ⟨T, tw, hTtw, hD'mem⟩ := hValid
    rcases htagL with hE6 | hTw
    · have hgt : ggKacTypeOfLabel labL = some (.E6, false) := by rw [hlabL_eq, hE6]; rfl
      rw [hgt] at hTtw
      obtain ⟨rfl, rfl⟩ := hTtw
      have hlabL_e : labL = ⟨.E6, 0, labL.n⟩ := by rw [hlabL_eq, hE6]
      rcases ltqS1_three_dvd labL.n with h3 | h3
      · have hn2 : 2 ≤ labL.n := by
          have hn1' : 1 ≤ labL.n := hΛL.1
          rcases Nat.lt_or_ge labL.n 2 with hlt | hge
          · interval_cases labL.n
            norm_num at h3
          · exact hge
        have hqs_all : ∀ i : Fin D'.orbits.length, D'.orbits[i].qs = true :=
          fun i => ggKacTable_qs_of_two_le .E6 false 3 hn2 D' hD'mem (D'.orbits.get i) (List.get_mem D'.orbits i)
        have hlen : D'.orbits.length = 1 := ltqS1_len_one huniq hfix f hqs_all o ho
        have hshape := ggKacTable_shape .E6 false (p := 3) (n := labL.n) (n' := 2)
          (by norm_num) hΛL.1 (by norm_num) (Or.inl ⟨h3, by norm_num⟩)
        have hsh := ltqS1_extract hshape hD'mem hlen ho ltqS1_fin_false2
        rcases ltqS1_conv_false2 (n := labL.n) h3 hdvd hsh with h | h
        · rwa [← hlabL_e] at h
        · exact absurd (h.trans hlabL_e.symm) hself
      · by_cases hn1 : labL.n = 1
        · have hlab1 : labL = ⟨.E6, 0, 1⟩ := by rw [hlabL_e, hn1]
          have hD1 : D' ∈ ggKacTable .E6 false 3 1 := by
            rw [← hn1]; exact hD'mem
          rcases ltqS1_fin_false1 D' hD1 o ho hqs with h | h
          · rwa [← hlab1] at h
          · exact absurd (h.trans hlab1.symm) hself
        · have hn2 : 2 ≤ labL.n := by
            have hn1' : 1 ≤ labL.n := hΛL.1
            omega
          have hqs_all : ∀ i : Fin D'.orbits.length, D'.orbits[i].qs = true :=
            fun i => ggKacTable_qs_of_two_le .E6 false 3 hn2 D' hD'mem (D'.orbits.get i) (List.get_mem D'.orbits i)
          have hlen : D'.orbits.length = 1 := ltqS1_len_one huniq hfix f hqs_all o ho
          have hshape := ggKacTable_shape .E6 false (p := 3) (n := labL.n) (n' := 1)
            (by norm_num) hΛL.1 (by norm_num) (Or.inr ⟨h3, by norm_num⟩)
          have hsh := ltqS1_extract hshape hD'mem hlen ho ltqS1_fin_false1shape
          rcases ltqS1_conv_false1 (n := labL.n) h3 hdvd hsh with h | h
          · rwa [← hlabL_e] at h
          · exact absurd (h.trans hlabL_e.symm) hself
    · have hgt : ggKacTypeOfLabel labL = some (.E6, true) := by rw [hlabL_eq, hTw]; rfl
      rw [hgt] at hTtw
      obtain ⟨rfl, rfl⟩ := hTtw
      have hlabL_e : labL = ⟨.twE6, 0, labL.n⟩ := by rw [hlabL_eq, hTw]
      rcases ltqS1_three_dvd labL.n with h3 | h3
      · have hn2 : 2 ≤ labL.n := by
          have hn1' : 1 ≤ labL.n := hΛL.1
          rcases Nat.lt_or_ge labL.n 2 with hlt | hge
          · interval_cases labL.n
            norm_num at h3
          · exact hge
        have hqs_all : ∀ i : Fin D'.orbits.length, D'.orbits[i].qs = true :=
          fun i => ggKacTable_qs_of_two_le .E6 true 3 hn2 D' hD'mem (D'.orbits.get i) (List.get_mem D'.orbits i)
        have hlen : D'.orbits.length = 1 := ltqS1_len_one huniq hfix f hqs_all o ho
        have hshape := ggKacTable_shape .E6 true (p := 3) (n := labL.n) (n' := 2)
          (by norm_num) hΛL.1 (by norm_num) (Or.inl ⟨h3, by norm_num⟩)
        have hsh := ltqS1_extract hshape hD'mem hlen ho ltqS1_fin_true2
        rcases ltqS1_conv_true2 (n := labL.n) h3 hdvd hsh with h | h
        · rwa [← hlabL_e] at h
        · exact absurd (h.trans hlabL_e.symm) hself
      · by_cases hn1 : labL.n = 1
        · have hlab1 : labL = ⟨.twE6, 0, 1⟩ := by rw [hlabL_e, hn1]
          have hD1 : D' ∈ ggKacTable .E6 true 3 1 := by
            rw [← hn1]; exact hD'mem
          rcases ltqS1_fin_true1 D' hD1 o ho hqs with h | h
          · rwa [← hlab1] at h
          · exact absurd (h.trans hlab1.symm) hself
        · have hn2 : 2 ≤ labL.n := by
            have hn1' : 1 ≤ labL.n := hΛL.1
            omega
          have hqs_all : ∀ i : Fin D'.orbits.length, D'.orbits[i].qs = true :=
            fun i => ggKacTable_qs_of_two_le .E6 true 3 hn2 D' hD'mem (D'.orbits.get i) (List.get_mem D'.orbits i)
          have hlen : D'.orbits.length = 1 := ltqS1_len_one huniq hfix f hqs_all o ho
          have hshape := ggKacTable_shape .E6 true (p := 3) (n := labL.n) (n' := 1)
            (by norm_num) hΛL.1 (by norm_num) (Or.inr ⟨h3, by norm_num⟩)
          have hsh := ltqS1_extract hshape hD'mem hlen ho ltqS1_fin_true1shape
          rcases ltqS1_conv_true1 (n := labL.n) h3 hdvd hsh with h | h
          · rwa [← hlabL_e] at h
          · exact absurd (h.trans hlabL_e.symm) hself
  refine ⟨o.lab, hJLabel, hΛo, ?_⟩
  have hJL : J ≤ L := hDJ.1.2.2.2.2.2.1.1.trans inf_le_left
  exact ggHasLabel_of_mulEquiv
    (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJL) (Subgroup.map_center_eq _))
    hlabel_J0

end CFSG.StandardType

end

