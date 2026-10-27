module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CBA3AA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

private theorem s16h_sl4_cba3_exists_ne_one_fixed_of_pgroup {A : Type*} [Group A] [Finite A]
    {p : ℕ} [hp : Fact p.Prime] (hA : IsPGroup p A) (hA1 : 1 < Nat.card A)
    {Y : Subgroup (MulAut A)} (hY : IsPGroup p Y) :
    ∃ a : A, a ≠ 1 ∧ ∀ y ∈ Y, (y : MulAut A) a = a := by
  classical
  have hmod := hY.card_modEq_card_fixedPoints A
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    omega
  have hpA : Nat.card A ≡ 0 [MOD p] := by
    rw [hn, Nat.modEq_zero_iff_dvd]
    exact dvd_pow_self p hn0
  have hfix : Nat.card (MulAction.fixedPoints Y A) ≡ 0 [MOD p] := hmod.symm.trans hpA
  have h1 : (1 : A) ∈ MulAction.fixedPoints Y A := fun y => map_one (y : MulAut A)
  have hcard : 1 < Nat.card (MulAction.fixedPoints Y A) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints Y A) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨1, h1⟩⟩, inferInstance⟩
    have hdvd := Nat.modEq_zero_iff_dvd.mp hfix
    have hle := Nat.le_of_dvd hpos hdvd
    have := hp.out.two_le
    omega
  have hnt := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨⟨a, ha⟩, ha1⟩ := exists_ne (⟨1, h1⟩ : MulAction.fixedPoints Y A)
  exact ⟨a, fun h0 => ha1 (Subtype.ext h0), fun y hy => ha ⟨y, hy⟩⟩

theorem s16h_sl4_cba3_E9_of_fixed
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (hZ0 : wSub ⊥ V h.hyp151.isElemAbelian L ⊓
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x =
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) :
    ∃ w : Vtil ⊥ V h.hyp151.isElemAbelian, w ≠ 1 ∧
      (∀ τ ∈ barSub ⊥ V h.hyp151.isElemAbelian D.T, τ w = w) ∧
      ∃ E : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)),
        E ≤ Mbar D.M ⊥ V h.hyp151.isElemAbelian ∧ IsElemAbelian 3 E ∧
          9 ≤ Nat.card ↥E ∧ ∀ e ∈ E, e w = w := by
  have hV := h.hyp151.isElemAbelian
  obtain ⟨E, hEM, hEab, hEcard, hEfix⟩ :=
    s16h_sl4_cba3_three_fixes_v1 D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ
      hbad hrow hZ4 hxM hxn hZ0
  let V₁ : Subgroup G := v1Sub D.M ⊥ V hV L
  have hV1le : V₁ ≤ V := s15_Infra_v1Sub_le h.hyp151.hyp125 hV
  have hV1ne : V₁ ≠ ⊥ := by
    obtain ⟨q, hqne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZ
    have hqW : (q : Vtil ⊥ V hV) ∈ wTil ⊥ V hV L := (Subgroup.mem_inf.1 q.2).1
    have hqfix : (q : Vtil ⊥ V hV) ∈ fixV (lBar ⊥ V hV L) :=
      (Subgroup.mem_inf.1 q.2).2
    have hqbar_ne : (q : Vtil ⊥ V hV) ≠ 1 := fun hq => hqne (Subtype.ext hq)
    have hqimg : (q : Vtil ⊥ V hV) ∈ imgTil ⊥ V hV (wSub ⊥ V hV L) := by
      unfold wSub
      rw [imgTil_preTil]
      exact hqW
    obtain ⟨y, hyw, hyq⟩ := (mem_imgTil ⊥ V hV (wSub ⊥ V hV L) _).1 hqimg
    have hycent : y.val ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hlM : l ∈ D.M := h.hyp151.le hl
      have hlst : l ∈ stabTil ⊥ V :=
        le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
          h.hyp151.hyp125.pairFacts.le_normalizer₀ hlM
      have hφ : actTil ⊥ V hV ⟨l, hlst⟩ ∈ lBar ⊥ V hV L :=
        actTil_mem_barSub ⊥ V hV hl hlst
      have hfixl : actTil ⊥ V hV ⟨l, hlst⟩ (q : Vtil ⊥ V hV) =
          (q : Vtil ⊥ V hV) := mem_fixV.mp hqfix _ hφ
      have h1 : mkTil ⊥ V hV (actStab ⊥ V hV ⟨l, hlst⟩ y) = mkTil ⊥ V hV y := by
        rw [← actTil_mk, hyq, hfixl]
      rw [mkTil_eq_iff, Subgroup.mem_bot, actStab_apply_val] at h1
      have h2 : l * y.val * l⁻¹ = y.val := mul_inv_eq_one.mp h1
      calc l * y.val = (l * y.val * l⁻¹) * l := by group
        _ = y.val * l := by rw [h2]
    have hyZ : y.val ∈ wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G) := ⟨hyw, hycent⟩
    have hyV1 : y.val ∈ V₁ := by
      change y.val ∈ v1Sub D.M ⊥ V hV L
      rw [v1Sub_of_eq_bot D.M ⊥ V hV L rfl]
      refine le_iSup (fun m : D.M => conjSubgroup (wSub ⊥ V hV L ⊓
        Subgroup.centralizer (L : Set G)) (m : G)) 1 ?_
      have h1 : ((1 : D.M) : G) = 1 := rfl
      rw [h1, conjSubgroup_one]
      exact hyZ
    have hyne : y.val ≠ 1 := by
      intro hy1
      apply hqbar_ne
      rw [← hyq]
      have : y = 1 := IntMod.val_injective (show y.val = (1 : IntMod V hV).val by simpa using hy1)
      rw [this, map_one]
    intro hbot
    exact hyne (Subgroup.mem_bot.1 (hbot ▸ hyV1))
  have hV1p : IsPGroup 2 ↥V₁ :=
    isPGroup_two_of_sq_eq_one fun v => Subtype.ext (hV.2 v.val (hV1le v.2))
  have hV1gt : 1 < Nat.card ↥V₁ := by
    obtain ⟨v, hvne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hV1ne
    exact Finite.one_lt_card_iff_nontrivial.mpr ⟨v, 1, hvne⟩
  let N : Subgroup G := Subgroup.normalizer (V₁ : Set G)
  have hTN : D.T ≤ N :=
    D.sylowM.le.trans (s15_Infra_le_normalizer_v1Sub h.hyp151.hyp125 hV)
  let Y : Subgroup (MulAut ↥V₁) :=
    (D.T.subgroupOf N).map (Subgroup.normalizerMonoidHom (H := V₁))
  have hYp : IsPGroup 2 Y := (D.sylowM.isPGroup.comap_subtype).map _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha1, hafix⟩ := s16h_sl4_cba3_exists_ne_one_fixed_of_pgroup hV1p hV1gt hYp
  let v : G := (a : G)
  have hvV : v ∈ V := hV1le a.2
  let w : Vtil ⊥ V hV := mkTil ⊥ V hV (IntMod.mk hV ⟨v, hvV⟩)
  have hw1 : w ≠ 1 := by
    intro hw
    have hx1 : (IntMod.mk hV ⟨v, hvV⟩ : IntMod V hV) = 1 := by
      have h := (mkTil_eq_iff ⊥ V hV _ 1).1 hw
      rw [Subgroup.mem_bot] at h
      exact IntMod.val_injective (by simpa using h)
    have hv1 : v = 1 := congrArg IntMod.val hx1
    exact ha1 (Subtype.ext hv1)
  have hwT : ∀ τ ∈ barSub ⊥ V hV D.T, τ w = w := by
    intro τ hτ
    obtain ⟨g, hgD, hgτ⟩ := (mem_barSub ⊥ V hV D.T τ).1 hτ
    have hgN : (g : G) ∈ N := hTN hgD
    have hyt : Subgroup.normalizerMonoidHom (H := V₁) ⟨(g : G), hgN⟩ ∈ Y :=
      ⟨⟨(g : G), hgN⟩, (Subgroup.mem_subgroupOf).2 hgD, rfl⟩
    have hfixa : Subgroup.normalizerMonoidHom (H := V₁) ⟨(g : G), hgN⟩ a = a :=
      hafix (⟨Subgroup.normalizerMonoidHom (H := V₁) ⟨(g : G), hgN⟩, hyt⟩ : Y) hyt
    have hconj : (g : G) * (a : G) * (g : G)⁻¹ = (a : G) := by
      have h := congrArg (fun z : ↥V₁ => (z : G)) hfixa
      rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
    rw [← hgτ]
    show actTil ⊥ V hV g (mkTil ⊥ V hV (IntMod.mk hV ⟨v, hvV⟩)) =
      mkTil ⊥ V hV (IntMod.mk hV ⟨v, hvV⟩)
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot]
    show (g : G) * v * (g : G)⁻¹ * v⁻¹ = 1
    rw [show v = (a : G) from rfl, hconj]
    group
  refine ⟨w, hw1, hwT, E, hEM, hEab, hEcard, ?_⟩
  intro e he
  exact hEfix e he w ⟨IntMod.mk hV ⟨v, hvV⟩, a.2, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
