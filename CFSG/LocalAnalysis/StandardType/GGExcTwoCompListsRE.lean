module

public import CFSG.LocalAnalysis.StandardType.GGExcTwoCompList

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

private local instance (priority := high) ltqReDecidableEqLargeEvenLabel : DecidableEq LargeEvenLabel :=
  fun a b =>
    match a, b with
    | ⟨ta, ra, na⟩, ⟨tb, rb, nb⟩ =>
      if h1 : ta = tb then
        if h2 : ra = rb then
          if h3 : na = nb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private local instance (priority := high) ltqReDecidableEqGGKacOrbit : DecidableEq GGKacOrbit :=
  fun a b =>
    match a, b with
    | ⟨la, qa⟩, ⟨lb, qb⟩ =>
      if h1 : la = lb then
        if h2 : qa = qb then isTrue (by cases h1; cases h2; rfl)
        else isFalse (by intro h; injection h with _ h2'; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _; exact h1 h1')

private local instance (priority := high) ltqReDecidableEqGGKacDatum : DecidableEq GGKacDatum :=
  fun a b =>
    match a, b with
    | ⟨oa, za, sa⟩, ⟨ob, zb, sb⟩ =>
      if h1 : oa = ob then
        if h2 : za = zb then
          if h3 : sa = sb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private theorem ltqRe_E6_false_table :
    ∀ D ∈ ggKacTable .E6 false 3 1, ∀ o ∈ D.orbits, o.qs = true →
      o.lab ∈ [⟨.A, 5, 1⟩, ⟨.twD, 4, 1⟩, ⟨.A, 2, 2⟩] ∨ o.lab = ⟨.E6, 0, 1⟩ := by
  decide +kernel

private theorem ltqRe_E6_true_table :
    ∀ D ∈ ggKacTable .E6 true 3 1, ∀ o ∈ D.orbits, o.qs = true →
      o.lab ∈ [⟨.twA, 5, 1⟩, ⟨.D, 4, 1⟩, ⟨.twD, 5, 1⟩, ⟨.triD4, 0, 1⟩, ⟨.twA, 4, 1⟩,
        ⟨.twA, 2, 3⟩] ∨ o.lab = ⟨.twE6, 0, 1⟩ := by
  decide +kernel

private theorem ltqRe_E7_false_table :
    ∀ D ∈ ggKacTable .E7 false 3 1, ∀ o ∈ D.orbits, o.qs = true →
      o.lab ∈ [⟨.D, 6, 1⟩, ⟨.twA, 5, 1⟩, ⟨.twA, 6, 1⟩, ⟨.twD, 5, 1⟩, ⟨.twE6, 0, 1⟩] ∨
        o.lab = ⟨.E7, 0, 1⟩ := by
  decide +kernel

private theorem ltqRe_E8_false_table :
    ∀ D ∈ ggKacTable .E8 false 3 1, ∀ o ∈ D.orbits, o.qs = true →
      o.lab ∈ [⟨.twE6, 0, 1⟩, ⟨.twA, 8, 1⟩, ⟨.E7, 0, 1⟩, ⟨.twD, 7, 1⟩] ∨
        o.lab = ⟨.E8, 0, 1⟩ := by
  decide +kernel

private theorem ltqRe_mem_E6_false {D : GGKacDatum} (h : GGKacValid ⟨.E6, 0, 1⟩ 3 D) :
    D ∈ ggKacTable .E6 false 3 1 := by
  obtain ⟨T, tw, h1, h2⟩ := h
  have h1' : ggKacTypeOfLabel (⟨.E6, 0, 1⟩ : LargeEvenLabel) = some (.E6, false) := by decide
  rw [h1'] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact h2

private theorem ltqRe_mem_twE6 {D : GGKacDatum} (h : GGKacValid ⟨.twE6, 0, 1⟩ 3 D) :
    D ∈ ggKacTable .E6 true 3 1 := by
  obtain ⟨T, tw, h1, h2⟩ := h
  have h1' : ggKacTypeOfLabel (⟨.twE6, 0, 1⟩ : LargeEvenLabel) = some (.E6, true) := by decide
  rw [h1'] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact h2

private theorem ltqRe_mem_E7 {D : GGKacDatum} (h : GGKacValid ⟨.E7, 0, 1⟩ 3 D) :
    D ∈ ggKacTable .E7 false 3 1 := by
  obtain ⟨T, tw, h1, h2⟩ := h
  have h1' : ggKacTypeOfLabel (⟨.E7, 0, 1⟩ : LargeEvenLabel) = some (.E7, false) := by decide
  rw [h1'] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact h2

private theorem ltqRe_mem_E8 {D : GGKacDatum} (h : GGKacValid ⟨.E8, 0, 1⟩ 3 D) :
    D ∈ ggKacTable .E8 false 3 1 := by
  obtain ⟨T, tw, h1, h2⟩ := h
  have h1' : ggKacTypeOfLabel (⟨.E8, 0, 1⟩ : LargeEvenLabel) = some (.E8, false) := by decide
  rw [h1'] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact h2

private theorem ltqRe_card_E6 :
    LargeEvenLabelAll ⟨.E6, 0, 1⟩ fun R _ _ _ => Nat.card R = ordE6 (2 ^ 1) := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  exact ⟨K, i1, i2, hK, hq,
    CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_E6
      (untwistedChevalleyModel_largeEven .E6 hK)⟩

private theorem ltqRe_card_twE6 :
    LargeEvenLabelAll ⟨.twE6, 0, 1⟩ fun R _ _ _ => Nat.card R = ordTwistedE6 (2 ^ 1) := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  exact ⟨K, i1, i2, hK, hq,
    CFSG.Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_E6_two (f := 1) le_rfl
      (twistedChevalleyModel_largeEven .E6 hK)⟩

private theorem ltqRe_card_E7 :
    LargeEvenLabelAll ⟨.E7, 0, 1⟩ fun R _ _ _ => Nat.card R = ordE7 (2 ^ 1) := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  exact ⟨K, i1, i2, hK, hq,
    CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_E7
      (untwistedChevalleyModel_largeEven .E7 hK)⟩

private theorem ltqRe_card_E8 :
    LargeEvenLabelAll ⟨.E8, 0, 1⟩ fun R _ _ _ => Nat.card R = ordE8 (2 ^ 1) := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  exact ⟨K, i1, i2, hK, hq,
    CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_E8
      (untwistedChevalleyModel_largeEven .E8 hK)⟩

private theorem ltqRe_eq_top_of_central
    {G R : Type} [Group G] [Finite G] [Group R] [Finite R]
    (hperf : commutator G = ⊤) (ψ : G →* R) (hψ : Function.Surjective ψ)
    (hk : ψ.ker ≤ Subgroup.center G) (J : Subgroup G)
    (hcard : Nat.card R ≤ Nat.card (↥J ⧸ Subgroup.center ↥J)) : J = ⊤ := by
  let f : ↥J →* R := ψ.comp J.subtype
  have hfker : f.ker ≤ Subgroup.center ↥J := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hx1 : ψ (x : G) = 1 := MonoidHom.mem_ker.mp hx
    have hxZ : (x : G) ∈ Subgroup.center G := hk (MonoidHom.mem_ker.mpr hx1)
    exact Subgroup.mem_center_iff.mp hxZ (y : G)
  have hquot_le : Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ Nat.card f.range := by
    have h1 : Nat.card ↥J = Nat.card (↥J ⧸ Subgroup.center ↥J) *
        Nat.card (Subgroup.center ↥J) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J)
    have h2 : Nat.card f.ker * Nat.card f.range = Nat.card ↥J :=
      Subgroup.card_ker_mul_card_range f
    have hkcard : Nat.card f.ker ≤ Nat.card (Subgroup.center ↥J) :=
      Subgroup.card_le_of_le hfker
    have hpos : 0 < Nat.card (Subgroup.center ↥J) := Nat.card_pos
    have hmain : Nat.card (↥J ⧸ Subgroup.center ↥J) * Nat.card (Subgroup.center ↥J) ≤
        Nat.card f.range * Nat.card (Subgroup.center ↥J) := by
      calc Nat.card (↥J ⧸ Subgroup.center ↥J) * Nat.card (Subgroup.center ↥J)
          = Nat.card ↥J := h1.symm
        _ = Nat.card f.ker * Nat.card f.range := h2.symm
        _ ≤ Nat.card (Subgroup.center ↥J) * Nat.card f.range :=
              Nat.mul_le_mul_right _ hkcard
        _ = Nat.card f.range * Nat.card (Subgroup.center ↥J) := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_right hmain hpos
  have hfrange : f.range = ⊤ := Subgroup.eq_top_of_le_card f.range (hcard.trans hquot_le)
  have hfrange_eq : f.range = J.map ψ := by
    ext r
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : G), x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hmap : J.map ψ = ⊤ := by
    rw [← hfrange_eq, hfrange]
  have hJN : J ⊔ ψ.ker = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : ψ g ∈ J.map ψ := by rw [hmap]; exact Subgroup.mem_top _
    obtain ⟨j, hj, hjg⟩ := Subgroup.mem_map.mp hg
    have hker : j⁻¹ * g ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hjg, inv_mul_cancel]
    have hmul := Subgroup.mul_mem_sup hj hker
    rwa [mul_inv_cancel_left] at hmul
  have hJnorm : J.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    rw [eq_top_iff]
    intro g _
    have hle : J ⊔ ψ.ker ≤ Subgroup.normalizer (J : Set G) :=
      sup_le Subgroup.le_normalizer (hk.trans (Subgroup.center_le_normalizer (J : Set G)))
    exact hle (by rw [hJN]; exact Subgroup.mem_top g)
  have hker_comm : IsMulCommutative ↥ψ.ker := by
    refine IsMulCommutative.of_comm fun x y => ?_
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hk x.2) (y : G)).symm
  haveI : J.Normal := hJnorm
  have hcomm : commutator G ≤ J :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top (N := J) (H := ψ.ker) hJN hker_comm
  rw [hperf] at hcomm
  exact top_le_iff.mp hcomm

private theorem ltqRe_lambda2_E6 : LargeEvenInLambda2 ⟨.E6, 0, 1⟩ := by
  simp [LargeEvenInLambda2]

private theorem ltqRe_lambda2_twE6 : LargeEvenInLambda2 ⟨.twE6, 0, 1⟩ := by
  simp [LargeEvenInLambda2]

private theorem ltqRe_lambda2_E7 : LargeEvenInLambda2 ⟨.E7, 0, 1⟩ := by
  simp [LargeEvenInLambda2]

private theorem ltqRe_lambda2_E8 : LargeEvenInLambda2 ⟨.E8, 0, 1⟩ := by
  simp [LargeEvenInLambda2]

private theorem ltqRe_re_E6 : GGKacRE ⟨.E6, 0, 1⟩ 3 := by
  unfold GGKacRE
  refine ⟨by norm_num, by norm_num, by norm_num, by simp⟩

private theorem ltqRe_re_twE6 : GGKacRE ⟨.twE6, 0, 1⟩ 3 := by
  unfold GGKacRE
  refine ⟨by norm_num, by norm_num, by norm_num, by simp⟩

private theorem ltqRe_re_E7 : GGKacRE ⟨.E7, 0, 1⟩ 3 := by
  unfold GGKacRE
  refine ⟨by norm_num, by norm_num, by norm_num, by simp⟩

private theorem ltqRe_re_E8 : GGKacRE ⟨.E8, 0, 1⟩ 3 := by
  unfold GGKacRE
  refine ⟨by norm_num, by norm_num, by norm_num, by simp⟩

private theorem ltqRe_assembly {lab : LargeEvenLabel} {S : LargeEvenLabel → Prop} {N : ℕ}
    (hΛ : LargeEvenInLambda2 lab) (hRE : GGKacRE lab 3)
    (hord : LargeEvenLabelAll lab fun R _ _ _ => Nat.card R = N) (hN : N ≠ 0)
    (htab : ∀ D : GGKacDatum, GGKacValid lab 3 D → ∀ o ∈ D.orbits, o.qs = true →
      S o.lab ∨ o.lab = lab)
    (h : GGK0CompRE) : GGCompList lab 3 S := by
  intro Q hQ
  have h1 := hord Q hQ
  have h2 := h 3 lab hΛ hRE _ h1
  refine largeEvenRawDatum_mono ?_ h2
  rintro R _ I F ⟨⟨hQR, hR⟩, hP⟩
  refine ⟨hQR, ?_⟩
  intro L' _ _ ψ hψ hk hc e he hne hφ J hJ
  obtain ⟨D, hV, ha, -, -⟩ := hP L' ψ hψ hk hc e he hφ
  obtain ⟨o, ho, hqs, -, -, hlab⟩ := ha J hJ
  rcases htab D hV o ho hqs with hmem | hself
  · exact ⟨o.lab, hmem, hlab⟩
  · exfalso
    rw [hself] at hlab
    haveI : Finite R := Nat.finite_of_card_ne_zero (by rw [hR]; exact hN)
    have hJcard : Nat.card (↥J ⧸ Subgroup.center ↥J) = N := by
      obtain ⟨R', _, _, _, hR'⟩ := largeEvenRawDatum_exists
        (hord (fun R' _ _ _ => Nonempty (↥J ⧸ Subgroup.center ↥J ≃* R')) hlab)
      obtain ⟨⟨e'⟩, hcard'⟩ := hR'
      rw [Nat.card_congr e'.toEquiv, hcard']
    have hJtop : J = ⊤ := ltqRe_eq_top_of_central hc ψ hψ hk J (by rw [hJcard, hR])
    apply hne
    ext l
    have hl : l ∈ J := by rw [hJtop]; trivial
    exact hJ.1 hl

theorem ggE6TwoThreeComp_of_K0RE
    (h : GGK0CompRE) : GGE6TwoThreeComp :=
  ltqRe_assembly (lab := ⟨.E6, 0, 1⟩)
    (S := fun l : LargeEvenLabel => l ∈ ([⟨.A, 5, 1⟩, ⟨.twD, 4, 1⟩, ⟨.A, 2, 2⟩] : List LargeEvenLabel))
    ltqRe_lambda2_E6 ltqRe_re_E6 ltqRe_card_E6 (by decide +kernel)
    (fun D hV o ho hqs => ltqRe_E6_false_table D (ltqRe_mem_E6_false hV) o ho hqs) h

theorem ggTwE6TwoThreeComp_of_K0RE
    (h : GGK0CompRE) : GGTwE6TwoThreeComp :=
  ltqRe_assembly (lab := ⟨.twE6, 0, 1⟩)
    (S := fun l : LargeEvenLabel => l ∈ ([⟨.twA, 5, 1⟩, ⟨.D, 4, 1⟩, ⟨.twD, 5, 1⟩, ⟨.triD4, 0, 1⟩,
      ⟨.twA, 4, 1⟩, ⟨.twA, 2, 3⟩] : List LargeEvenLabel))
    ltqRe_lambda2_twE6 ltqRe_re_twE6 ltqRe_card_twE6 (by decide +kernel)
    (fun D hV o ho hqs => ltqRe_E6_true_table D (ltqRe_mem_twE6 hV) o ho hqs) h

theorem ggE7TwoThreeComp_of_K0RE
    (h : GGK0CompRE) : GGE7TwoThreeComp :=
  ltqRe_assembly (lab := ⟨.E7, 0, 1⟩)
    (S := fun l : LargeEvenLabel => l ∈ ([⟨.D, 6, 1⟩, ⟨.twA, 5, 1⟩, ⟨.twA, 6, 1⟩, ⟨.twD, 5, 1⟩,
      ⟨.twE6, 0, 1⟩] : List LargeEvenLabel))
    ltqRe_lambda2_E7 ltqRe_re_E7 ltqRe_card_E7 (by decide +kernel)
    (fun D hV o ho hqs => ltqRe_E7_false_table D (ltqRe_mem_E7 hV) o ho hqs) h

theorem ggE8TwoThreeComp_of_K0RE
    (h : GGK0CompRE) : GGE8TwoThreeComp :=
  ltqRe_assembly (lab := ⟨.E8, 0, 1⟩)
    (S := fun l : LargeEvenLabel => l ∈ ([⟨.twE6, 0, 1⟩, ⟨.twA, 8, 1⟩, ⟨.E7, 0, 1⟩, ⟨.twD, 7, 1⟩] : List LargeEvenLabel))
    ltqRe_lambda2_E8 ltqRe_re_E8 ltqRe_card_E8 (by decide +kernel)
    (fun D hV o ho hqs => ltqRe_E8_false_table D (ltqRe_mem_E8 hV) o ho hqs) h

end CFSG.StandardType

end
