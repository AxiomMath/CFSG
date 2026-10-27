module

public import CFSG.ClassicalGroups.Orthogonal.OmegaFourMinusEightVectorFix
public import CFSG.GroupTheory.RankOneSmallIndex
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenA7FourFixers
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.RankThree.PartOne.MB3.Triple
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem4SixA
public import CFSG.RankThree.GF2n.Smith81.OrthE1KFSmall
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightRowCtx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
  {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem omegaMinusFourEight_point_fixer_aux {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {U Z : Subgroup W}
    (K : Type) [Field K] [Finite K] [CharP K 2] {b c : K}
    (hKcard : Nat.card K = 2 ^ 3) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hR : (CFSG.Quasithin.FFModel.nat
      (StatedOmega (StatedQuadMinus 2 K b c))).Realizes H U Z)
    (hW : ∀ w : W, w ^ 2 = 1) (hZfix : Z ≤ fixV H) {u : W} (hu : u ∈ U) :
    ∃ a : MulAut W, a ∈ H ∧ orderOf a = 3 ∧ a u = u := by
  obtain ⟨a, haH, haord, haZ⟩ :=
    CFSG.ClassicalGroups.Orthogonal.exists_orderOf_three_fix_mod_of_realizes
      hKcard hirr hR u hu
  have ha3 : a ^ 3 = 1 := by
    rw [← haord]
    exact pow_orderOf_eq_one a
  have hfixZ : ∀ z ∈ Z, a z = z := by
    intro z hz
    exact mem_fixV.mp (hZfix hz) a haH
  exact ⟨a, haH, haord, s16g_apply_eq_of_odd hW (by decide : Odd 3) ha3 hfixZ haZ⟩

theorem omegaMinusFourEight_point_fixer {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hW : ∀ w : W, w ^ 2 = 1) (hZfix : Z ≤ fixV H)
    (hrow : NatOmegaMinus H U Z 4 3) {u : W} (hu : u ∈ U) :
    ∃ a : MulAut W, a ∈ H ∧ orderOf a = 3 ∧ a u = u := by
  obtain ⟨-, K, hKf, hKfin, b, c, hKcard, hirr, hR⟩ := hrow
  have hChar : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  exact @omegaMinusFourEight_point_fixer_aux W _ H U Z K hKf hKfin hChar b c
    hKcard hirr hR hW hZfix u hu

theorem omegaMinusFourEight_lBar_point_fixer
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : s16h_H5RowO4 (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3)
    (w : Vtil V₀ V hV) :
    ∃ a : MulAut (Vtil V₀ V hV), a ∈ lBar V₀ V hV L ∧ orderOf a = 3 ∧ a w = w := by
  obtain ⟨-, hNat⟩ := hrow
  have hspan : commSub ⊤ (lBar V₀ V hV L) ⊔ fixV (lBar V₀ V hV L) = ⊤ :=
    s168e3_commSub_lBar_sup_fixV_eq_top c
  obtain ⟨u, hu, z, hz, rfl⟩ := Subgroup.mem_sup.mp (by rw [hspan]; exact Subgroup.mem_top w)
  obtain ⟨a, haH, haord, hau⟩ :=
    omegaMinusFourEight_point_fixer (s15_Infra_vtil_sq_eq_one V₀ V hV) inf_le_right hNat hu
  refine ⟨a, haH, haord, ?_⟩
  rw [map_mul, hau, mem_fixV.mp hz a haH]

private theorem omegaMinusFourEight_center_eq_bot_aux
    {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {U Z : Subgroup W}
    (K : Type) [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hR : (CFSG.Quasithin.FFModel.nat
      (StatedOmega (StatedQuadMinus 2 K b c))).Realizes H U Z) :
    Subgroup.center ↥H = ⊥ := by
  obtain ⟨π, hπ⟩ := hR
  have hπinj : Function.Injective π :=
    CFSG.Quasithin.FFModel.RealizesVia.injective_of_faithful_on
      (CFSG.Quasithin.FFModel.nat_faithful
        (StatedOmega (StatedQuadMinus 2 K b c))) hπ
  let e : ↥(StatedOmega (StatedQuadMinus 2 K b c)) ≃* ↥H :=
    MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩
  have hmap := Subgroup.map_center_eq e
  rw [CFSG.RankThree.GF2n.Smith81.Smith23E1.kfs_center_minus hirr, Subgroup.map_bot] at hmap
  exact hmap.symm

theorem omegaMinusFourEight_center_eq_bot
    {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hrow : NatOmegaMinus H U Z 4 3) : Subgroup.center ↥H = ⊥ := by
  obtain ⟨-, K, hKf, hKfin, b, c, hKcard, hirr, hR⟩ := hrow
  have hChar : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  exact @omegaMinusFourEight_center_eq_bot_aux W _ H U Z K hKf hKfin hChar b c hirr hR


theorem omegaMinusFourEight_exists_e27_stabilizer
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : s15 D.M V₀ V hV L = 3)
    (hrow : s16h_H5RowO4 (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3)
    (v : Vtil V₀ V hV) :
    ∃ E : Subgroup (MulAut (Vtil V₀ V hV)),
      E ≤ Mbar D.M V₀ V hV ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧
        ∀ e ∈ E, e v = v := by
  classical
  let H : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  let A : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  let S : Set (Subgroup (MulAut (Vtil V₀ V hV))) :=
    {X | ∃ g ∈ A, X = H.map (MulAut.conj g).toMonoidHom}
  have hS3 : S.ncard = 3 := hs
  obtain ⟨H0, H1, H2, h01, h02, h12, hSeq⟩ := Set.ncard_eq_three.mp hS3
  have hH0 : H0 ∈ S := by rw [hSeq]; simp
  have hH1 : H1 ∈ S := by rw [hSeq]; simp
  have hH2 : H2 ∈ S := by rw [hSeq]; simp
  obtain ⟨g0, hg0A, hH0eq⟩ := hH0
  obtain ⟨g1, hg1A, hH1eq⟩ := hH1
  obtain ⟨g2, hg2A, hH2eq⟩ := hH2
  have hHleA : H ≤ A := fun x hx => by
    have := hcomp.1 hx
    simpa [H, A] using this
  have hcomp0 : IsComponentOf H0 A := by
    rw [hH0eq]
    exact CFSG.LargeExtraspecial.S5.isComponentOf_map_conj (A := H) (K := A) hcomp hg0A
  have hcomp1 : IsComponentOf H1 A := by
    rw [hH1eq]
    exact CFSG.LargeExtraspecial.S5.isComponentOf_map_conj (A := H) (K := A) hcomp hg1A
  have hcomp2 : IsComponentOf H2 A := by
    rw [hH2eq]
    exact CFSG.LargeExtraspecial.S5.isComponentOf_map_conj (A := H) (K := A) hcomp hg2A
  have hcenterH : Subgroup.center ↥H = ⊥ := by
    have hrowA : NatOmegaMinus H (commSub ⊤ H)
        (commSub ⊤ H ⊓ fixV H) 4 3 := by
      simpa [H] using hrow.2
    exact omegaMinusFourEight_center_eq_bot hrowA
  have hcenterEq : ∀ (g : MulAut (Vtil V₀ V hV)) (K : Subgroup (MulAut (Vtil V₀ V hV))),
      K = H.map (MulAut.conj g).toMonoidHom → Subgroup.center ↥K = ⊥ := by
    intro g K hK
    subst hK
    let e : ↥H ≃* ↥(H.map (MulAut.conj g).toMonoidHom) :=
      H.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    have hmap := Subgroup.map_center_eq e
    rw [hcenterH, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hcenter0 : Subgroup.center ↥H0 = ⊥ := hcenterEq g0 H0 hH0eq
  have hcenter1 : Subgroup.center ↥H1 = ⊥ := hcenterEq g1 H1 hH1eq
  have hcenter2 : Subgroup.center ↥H2 = ⊥ := hcenterEq g2 H2 hH2eq
  obtain ⟨b0, hb0H, hb0ord, hb0act⟩ :=
    omegaMinusFourEight_lBar_point_fixer c hrow (g0⁻¹ v)
  obtain ⟨b1, hb1H, hb1ord, hb1act⟩ :=
    omegaMinusFourEight_lBar_point_fixer c hrow (g1⁻¹ v)
  obtain ⟨b2, hb2H, hb2ord, hb2act⟩ :=
    omegaMinusFourEight_lBar_point_fixer c hrow (g2⁻¹ v)
  let a0 : MulAut (Vtil V₀ V hV) := g0 * b0 * g0⁻¹
  let a1 : MulAut (Vtil V₀ V hV) := g1 * b1 * g1⁻¹
  let a2 : MulAut (Vtil V₀ V hV) := g2 * b2 * g2⁻¹
  have ha0H : a0 ∈ H0 := by
    rw [hH0eq]
    refine Subgroup.mem_map.mpr ⟨b0, hb0H, ?_⟩
    change MulAut.conj g0 b0 = a0
    rw [MulAut.conj_apply]
  have ha1H : a1 ∈ H1 := by
    rw [hH1eq]
    refine Subgroup.mem_map.mpr ⟨b1, hb1H, ?_⟩
    change MulAut.conj g1 b1 = a1
    rw [MulAut.conj_apply]
  have ha2H : a2 ∈ H2 := by
    rw [hH2eq]
    refine Subgroup.mem_map.mpr ⟨b2, hb2H, ?_⟩
    change MulAut.conj g2 b2 = a2
    rw [MulAut.conj_apply]
  have ha0A : a0 ∈ A := hcomp0.1 ha0H
  have ha1A : a1 ∈ A := hcomp1.1 ha1H
  have ha2A : a2 ∈ A := hcomp2.1 ha2H
  have ha0ord : orderOf a0 = 3 := by
    have h := orderOf_injective (MulAut.conj g0).toMonoidHom (MulAut.conj g0).injective b0
    change orderOf (MulAut.conj g0 b0) = orderOf b0 at h
    rw [MulAut.conj_apply, hb0ord] at h
    simpa only [a0] using h
  have ha1ord : orderOf a1 = 3 := by
    have h := orderOf_injective (MulAut.conj g1).toMonoidHom (MulAut.conj g1).injective b1
    change orderOf (MulAut.conj g1 b1) = orderOf b1 at h
    rw [MulAut.conj_apply, hb1ord] at h
    simpa only [a1] using h
  have ha2ord : orderOf a2 = 3 := by
    have h := orderOf_injective (MulAut.conj g2).toMonoidHom (MulAut.conj g2).injective b2
    change orderOf (MulAut.conj g2 b2) = orderOf b2 at h
    rw [MulAut.conj_apply, hb2ord] at h
    simpa only [a2] using h
  have ha0fix : a0 v = v := by
    calc a0 v = g0 (b0 (g0⁻¹ v)) := by simp only [a0, MulAut.mul_apply]
      _ = g0 (g0⁻¹ v) := by rw [hb0act]
      _ = v := by simp
  have ha1fix : a1 v = v := by
    calc a1 v = g1 (b1 (g1⁻¹ v)) := by simp only [a1, MulAut.mul_apply]
      _ = g1 (g1⁻¹ v) := by rw [hb1act]
      _ = v := by simp
  have ha2fix : a2 v = v := by
    calc a2 v = g2 (b2 (g2⁻¹ v)) := by simp only [a2, MulAut.mul_apply]
      _ = g2 (g2⁻¹ v) := by rw [hb2act]
      _ = v := by simp
  have hcomm01 : ∀ x ∈ H0, ∀ y ∈ H1, x * y = y * x :=
    fun x hx y hy => CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hcomp0 hcomp1 h01 hx hy
  have hcomm02 : ∀ x ∈ H0, ∀ y ∈ H2, x * y = y * x :=
    fun x hx y hy => CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hcomp0 hcomp2 h02 hx hy
  have hcomm12 : ∀ x ∈ H1, ∀ y ∈ H2, x * y = y * x :=
    fun x hx y hy => CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hcomp1 hcomp2 h12 hx hy
  have hab01 : Commute a0 a1 := (hcomm01 a0 ha0H a1 ha1H)
  have hab02 : Commute a0 a2 := (hcomm02 a0 ha0H a2 ha2H)
  have hab12 : Commute a1 a2 := (hcomm12 a1 ha1H a2 ha2H)
  have hind : ∀ x ∈ Subgroup.zpowers a0, ∀ y ∈ Subgroup.zpowers a1,
      ∀ z ∈ Subgroup.zpowers a2, x * y * z = 1 → x = 1 ∧ y = 1 ∧ z = 1 := by
    intro x hx y hy z hz hprod
    have hcent := CFSG.RankThree.PartOne.MB3.central_of_prod_eq_one
      (K₀ := H0) (K₁ := H1) (K₂ := H2) (y₀ := x) (y₁ := y) (y₂ := z) (w := 1)
      hcomm01 hcomm02 hcomm12 (Subgroup.zpowers_le.mpr ha0H hx) (Subgroup.zpowers_le.mpr ha1H hy) (Subgroup.zpowers_le.mpr ha2H hz) (by intro k _; simp) (by intro k _; simp)
      (by intro k _; simp) (by simpa using hprod)
    have hxcenter : (⟨x, Subgroup.zpowers_le.mpr ha0H hx⟩ : ↥H0) ∈ Subgroup.center ↥H0 := by
      rw [Subgroup.mem_center_iff]
      intro h
      exact Subtype.ext (hcent.1 (h : MulAut _) h.2).symm
    have hycenter : (⟨y, Subgroup.zpowers_le.mpr ha1H hy⟩ : ↥H1) ∈ Subgroup.center ↥H1 := by
      rw [Subgroup.mem_center_iff]
      intro h
      exact Subtype.ext (hcent.2.1 (h : MulAut _) h.2).symm
    have hzcenter : (⟨z, Subgroup.zpowers_le.mpr ha2H hz⟩ : ↥H2) ∈ Subgroup.center ↥H2 := by
      rw [Subgroup.mem_center_iff]
      intro h
      exact Subtype.ext (hcent.2.2 (h : MulAut _) h.2).symm
    rw [hcenter0] at hxcenter
    rw [hcenter1] at hycenter
    rw [hcenter2] at hzcenter
    exact ⟨by simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hxcenter),
      by simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hycenter),
      by simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hzcenter)⟩
  let X : Subgroup (MulAut (Vtil V₀ V hV)) :=
    A ⊓ MulAction.stabilizer (MulAut (Vtil V₀ V hV)) v
  let a0' : ↥X := ⟨a0, ⟨ha0A, MulAction.mem_stabilizer_iff.mpr ha0fix⟩⟩
  let a1' : ↥X := ⟨a1, ⟨ha1A, MulAction.mem_stabilizer_iff.mpr ha1fix⟩⟩
  let a2' : ↥X := ⟨a2, ⟨ha2A, MulAction.mem_stabilizer_iff.mpr ha2fix⟩⟩
  have ha0'ord : orderOf a0' = 3 := by
    change orderOf (⟨a0, _⟩ : ↥X) = 3
    exact (Subgroup.orderOf_mk a0 _).trans ha0ord
  have ha1'ord : orderOf a1' = 3 := by
    change orderOf (⟨a1, _⟩ : ↥X) = 3
    exact (Subgroup.orderOf_mk a1 _).trans ha1ord
  have ha2'ord : orderOf a2' = 3 := by
    change orderOf (⟨a2, _⟩ : ↥X) = 3
    exact (Subgroup.orderOf_mk a2 _).trans ha2ord
  have hab01' : Commute a0' a1' := by
    apply Subtype.ext
    exact hab01.eq
  have hab02' : Commute a0' a2' := by
    apply Subtype.ext
    exact hab02.eq
  have hab12' : Commute a1' a2' := by
    apply Subtype.ext
    exact hab12.eq
  have hind' : ∀ x ∈ Subgroup.zpowers a0', ∀ y ∈ Subgroup.zpowers a1',
      ∀ z ∈ Subgroup.zpowers a2', x * y * z = 1 → x = 1 ∧ y = 1 ∧ z = 1 := by
    intro x hx y hy z hz hprod
    have hx' : (x : MulAut (Vtil V₀ V hV)) ∈ Subgroup.zpowers a0 := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [Subgroup.coe_zpow]⟩
    have hy' : (y : MulAut (Vtil V₀ V hV)) ∈ Subgroup.zpowers a1 := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [Subgroup.coe_zpow]⟩
    have hz' : (z : MulAut (Vtil V₀ V hV)) ∈ Subgroup.zpowers a2 := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [Subgroup.coe_zpow]⟩
    have hprod' : (x : MulAut (Vtil V₀ V hV)) * (y : MulAut (Vtil V₀ V hV)) *
        (z : MulAut (Vtil V₀ V hV)) = 1 := by
      have := congrArg Subtype.val hprod
      simpa using this
    obtain ⟨hx1, hy1, hz1⟩ := hind _ hx' _ hy' _ hz' hprod'
    exact ⟨Subtype.ext hx1, Subtype.ext hy1, Subtype.ext hz1⟩
  obtain ⟨E', hE'el, hE'card⟩ :=
    CFSG.Quasithin.H13.exists_elemAbelian27_of_elements624
      (x := a0') (y := a1') (z := a2') ha0'ord ha1'ord ha2'ord hab01' hab02' hab12' hind'
  let E : Subgroup (MulAut (Vtil V₀ V hV)) := E'.map X.subtype
  have hEsub : E ≤ A := by
    intro e he
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp he
    exact x.2.1
  have hEel : IsElemAbelian 3 E := hE'el.map X.subtype
  have hEcard : Nat.card E = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective X.subtype_injective, hE'card]
  refine ⟨E, hEsub, hEel, hEcard, ?_⟩
  intro e he
  obtain ⟨x, hxE', rfl⟩ := Subgroup.mem_map.mp he
  exact MulAction.mem_stabilizer_iff.mp x.2.2


@[instance_reducible] private def s16om8ConjAction
    {G : Type} [Group G] {M : Subgroup G} (H : Subgroup M) : MulAction ↥H G :=
  MulAction.compHom (α := G)
    (ConjAct.toConjAct.toMonoidHom.comp (M.subtype.comp H.subtype))

attribute [local instance] s16om8ConjAction

theorem s168e3_O1a_of_omegaMinus_four_eight_of_s_eq_three
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (_hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1)
    (hs : s15 D.M V₀ V hV L = 3)
    (hrow : s16h_H5RowO4 (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3) :
    s15O1a D V := by
  classical
  have hms : D.M ≤ stabTil V₀ V :=
    c.setting.hyp151.hyp125.pairFacts.le_normalizer
      |> fun hM => le_stabTil hM c.setting.hyp151.hyp125.pairFacts.le_normalizer₀
  let ψ : ↥D.M →* MulAut (Vtil V₀ V hV) := barHom V₀ V hV hms
  intro v hv hv1
  let vbar : Vtil V₀ V hV := mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩)
  obtain ⟨E, hEA, hEel, hEcard, hEfix⟩ :=
    omegaMinusFourEight_exists_e27_stabilizer c hcomp hs hrow vbar
  let H : Subgroup ↥D.M := E.comap ψ
  have hψH : ∀ h : ↥H, ψ (h : ↥D.M) ∈ E := fun h => h.2
  let f : ↥H →* ↥E :=
    (ψ.comp H.subtype).codRestrict E hψH
  have hfsurj : Function.Surjective f := by
    intro e
    have heA : (e : MulAut (Vtil V₀ V hV)) ∈ ψ.range := by
      change (e : MulAut (Vtil V₀ V hV)) ∈ (barHom V₀ V hV hms).range
      rw [range_barHom V₀ V hV hms]
      exact hEA e.2
    obtain ⟨m, hm⟩ := heA
    refine ⟨⟨m, ?_⟩, ?_⟩
    · change ψ m ∈ E
      rw [hm]
      exact e.2
    · apply Subtype.ext
      exact hm
  let S : Subgroup ↥H := MulAction.stabilizer ↥H v
  have horb_sub : MulAction.orbit ↥H v ⊆ ((fun z : G => v * z) '' (V₀ : Set G)) := by
    rintro x ⟨h, rfl⟩
    have hvbar : ψ (h : ↥D.M) vbar = vbar := hEfix (ψ (h : ↥D.M)) (hψH h)
    have hfix : (((h : ↥H) : ↥D.M) : G) * v * ((((h : ↥H) : ↥D.M) : G))⁻¹ * v⁻¹ ∈ V₀ :=
      (barHom_fix_iff V₀ V hV hms (h : ↥D.M) (IntMod.mk hV ⟨v, hv⟩)).mp hvbar
    refine ⟨(((h : ↥H) : ↥D.M) : G) * v * ((((h : ↥H) : ↥D.M) : G))⁻¹ * v⁻¹, hfix, ?_⟩
    have hnorm : (((h : ↥H) : ↥D.M) : G) ∈ Subgroup.normalizer (V : Set G) :=
      c.setting.hyp151.hyp125.pairFacts.le_normalizer ((h : ↥H) : ↥D.M).2
    have hmem : (((h : ↥H) : ↥D.M) : G) * v * ((((h : ↥H) : ↥D.M) : G))⁻¹ ∈ V := by
      have h := (Subgroup.mem_normalizer_iff.mp hnorm v)
      exact h.mp hv
    have hcommV : v * ((((h : ↥H) : ↥D.M) : G) * v * ((((h : ↥H) : ↥D.M) : G))⁻¹) =
        ((((h : ↥H) : ↥D.M) : G) * v * ((((h : ↥H) : ↥D.M) : G))⁻¹) * v := by
      have hc := hV.1.is_comm.comm (⟨v, hv⟩ : ↥V) (⟨_, hmem⟩ : ↥V)
      exact congrArg Subtype.val hc
    calc v * ((((h : ↥H) : ↥D.M) : G) * v * ((((h : ↥H) : ↥D.M) : G))⁻¹ * v⁻¹)
        = (v * ((((h : ↥H) : ↥D.M) : G) * v * ((((h : ↥H) : ↥D.M) : G))⁻¹)) * v⁻¹ := by
            group
      _ = (((((h : ↥H) : ↥D.M) : G) * v * ((((h : ↥H) : ↥D.M) : G))⁻¹) * v) * v⁻¹ := by
            rw [hcommV]
      _ = (((h : ↥H) : ↥D.M) : G) * v * ((((h : ↥H) : ↥D.M) : G))⁻¹ := by group
  have hindex_le : S.index ≤ Nat.card V₀ := by
    rw [show S.index = (MulAction.orbit ↥H v).ncard from
      MulAction.index_stabilizer ↥H v]
    calc (MulAction.orbit ↥H v).ncard
        ≤ (((fun z : G => v * z) '' (V₀ : Set G))).ncard := Set.ncard_le_ncard horb_sub
      _ = Nat.card V₀ :=
          (Set.ncard_image_of_injective (f := fun z : G => v * z) (V₀ : Set G)
            (fun a b hab => mul_left_cancel hab)).trans
            (Nat.card_coe_set_eq (V₀ : Set G)).symm
  have hcardV0 : Nat.card V₀ ≤ 4 := c23_card_v0_le_four D c.setting.hyp16
  have hindex : S.index < 3 ^ 2 := by
    omega
  have hEtop : CFSG.Open.IsElemAbelian 3 (⊤ : Subgroup ↥E) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x _ => ?_⟩
    · exact Subtype.ext (hEel.1.is_comm.comm (a : ↥E) (b : ↥E))
    · exact Subtype.ext (hEel.2 (x : ↥E) (x : ↥E).2)
  have hsmall := CFSG.one_lt_pRank_of_small_index_of_elemAbelian_quotient
    Nat.prime_three (by norm_num) hEtop f hfsurj
    (by rw [hEcard]) S hindex
  let ιH : ↥H →* G := D.M.subtype.comp H.subtype
  have hιHinj : Function.Injective ιH := by
    intro a b h
    apply H.subtype_injective
    apply D.M.subtype_injective
    exact h
  have hSmap_le : S.map ιH ≤ D.M ⊓ Subgroup.centralizer ({v} : Set G) := by
    intro x hx
    obtain ⟨s, hsS, rfl⟩ := Subgroup.mem_map.mp hx
    have hsfix : s • v = v := hsS
    have hsv : (((s : ↥H) : ↥D.M) : G) * v * ((((s : ↥H) : ↥D.M) : G))⁻¹ = v := hsfix
    refine ⟨((s : ↥H) : ↥D.M).2, ?_⟩
    change (((s : ↥H) : ↥D.M) : G) ∈ Subgroup.centralizer ({v} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (((s : ↥H) : ↥D.M) : G) * v
        = (((((s : ↥H) : ↥D.M) : G) * v * ((((s : ↥H) : ↥D.M) : G))⁻¹) *
            (((s : ↥H) : ↥D.M) : G)) := by group
      _ = v * (((s : ↥H) : ↥D.M) : G) := by rw [hsv]
  have hsmall_p : 1 < CFSG.pRank 3 S := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank 3 S]
    exact hsmall
  have hpSmap_p : 1 < CFSG.pRank 3 (S.map ιH) := by
    rw [← CFSG.pRank_congr_of_mulEquiv (Subgroup.equivMapOfInjective S ιH hιHinj) 3]
    exact hsmall_p
  have hpSmap : 1 < CFSG.Open.pRank 3 (S.map ιH) := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 3 (S.map ιH)]
    exact hpSmap_p
  exact lt_of_lt_of_le hpSmap
    (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hSmap_le)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
