module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenDefs
public import CFSG.GroupTheory.RegularActionIndexTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Lin2 (ActsRegularlyOn nonIdentity)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16c1614_actTil_bot_eq_one_iff {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (g : stabTil (⊥ : Subgroup G) V) :
    actTil ⊥ V hV g = 1 ↔ (g : G) ∈ centralizer (V : Set G) := by
  rw [actTil_eq_one_iff, Subgroup.mem_centralizer_iff]
  refine forall₂_congr fun v _ => ?_
  rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul, eq_comm]

private theorem s16c1614_actTil_bot_injective {V X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hX : X ≤ stabTil (⊥ : Subgroup G) V)
    (hdis : X ⊓ Subgroup.centralizer (V : Set G) = ⊥) :
    Function.Injective ((actTil (⊥ : Subgroup G) V hV).comp (Subgroup.inclusion hX)) := by
  intro x y hxy
  have hmem : ((x : G) * (y : G)⁻¹) ∈ X := X.mul_mem x.2 (X.inv_mem y.2)
  have h1 : actTil (⊥ : Subgroup G) V hV ⟨(x : G) * (y : G)⁻¹, hX hmem⟩ = 1 := by
    have hmul : (⟨(x : G) * (y : G)⁻¹, hX hmem⟩ : stabTil (⊥ : Subgroup G) V) =
        Subgroup.inclusion hX x * (Subgroup.inclusion hX y)⁻¹ := Subtype.ext rfl
    rw [hmul, map_mul, map_inv]
    rw [show actTil (⊥ : Subgroup G) V hV (Subgroup.inclusion hX x) =
      actTil (⊥ : Subgroup G) V hV (Subgroup.inclusion hX y) from hxy, mul_inv_cancel]
  have hcent : ((x : G) * (y : G)⁻¹) ∈ Subgroup.centralizer (V : Set G) :=
    (s16c1614_actTil_bot_eq_one_iff hV _).1 h1
  have hbot : ((x : G) * (y : G)⁻¹) ∈ (⊥ : Subgroup G) := by
    have hinf : ((x : G) * (y : G)⁻¹) ∈ X ⊓ Subgroup.centralizer (V : Set G) :=
      Subgroup.mem_inf.2 ⟨hmem, hcent⟩
    rwa [hdis] at hinf
  exact Subtype.ext (mul_inv_eq_one.1 (Subgroup.mem_bot.1 hbot))

private theorem s16c1614_orderOf_actTil_bot_eq {V X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hX : X ≤ stabTil (⊥ : Subgroup G) V)
    (hdis : X ⊓ Subgroup.centralizer (V : Set G) = ⊥) (x : X) :
    orderOf (actTil (⊥ : Subgroup G) V hV (Subgroup.inclusion hX x)) = orderOf x :=
  orderOf_injective ((actTil (⊥ : Subgroup G) V hV).comp (Subgroup.inclusion hX))
    (s16c1614_actTil_bot_injective hV hX hdis) x

private theorem s16c1614_mkTil_bot_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil (⊥ : Subgroup G) V hV) := by
  intro x y hxy
  rw [mkTil_eq_iff] at hxy
  rw [Subgroup.mem_bot] at hxy
  exact IntMod.val_injective (hV := hV) (mul_inv_eq_one.1 hxy)

private theorem s16c1614_commutator_le_of_le_stabTil {V X : Subgroup G}
    (hX : X ≤ stabTil (⊥ : Subgroup G) V) : ⁅V, X⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv xx hxx
  have hmem : xx * v⁻¹ * xx⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp
    (stabTil_le_normalizer (⊥ : Subgroup G) V (hX hxx)) v⁻¹).1 (V.inv_mem hv)
  have h1 : ⁅v, xx⁆ = v * (xx * v⁻¹ * xx⁻¹) := by rw [commutatorElement_def]; group
  rw [h1]; exact V.mul_mem hv hmem

private theorem s16c1614_inf_centralizer_eq_bot_of_regular_action {V X : Subgroup G}
    (hcommV : ⁅V, X⁆ ≤ V) (hcomm_ne : ⁅V, X⁆ ≠ ⊥)
    (hreg : ActsRegularlyOn X (nonIdentity ⁅V, X⁆)) :
    X ⊓ Subgroup.centralizer (V : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro x hx
  obtain ⟨hxX, hxV⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨⟨z, hzmem⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hcomm_ne
  have hzV : z ∈ V := hcommV hzmem
  have hzfix : x⁻¹ * z * x = z := by
    have h1 := (Subgroup.mem_centralizer_iff.1 hxV) z hzV
    simp only [mul_assoc]
    rw [h1, inv_mul_cancel_left]
  exact Subgroup.mem_bot.2 (hreg.2.2 z ⟨hzmem, fun h => hz1 (Subtype.ext h)⟩ x hxX hzfix)

private theorem s16c1614_barSub_eq_zpowers_of_gen {V X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXstab : X ≤ stabTil (⊥ : Subgroup G) V) {x : ↥X} (hxgen : Subgroup.zpowers x = ⊤) :
    barSub (⊥ : Subgroup G) V hV X =
      Subgroup.zpowers (actTil (⊥ : Subgroup G) V hV (Subgroup.inclusion hXstab x)) := by
  let F : ↥X →* MulAut (Vtil (⊥ : Subgroup G) V hV) :=
    (actTil (⊥ : Subgroup G) V hV).comp (Subgroup.inclusion hXstab)
  have hbar : barSub (⊥ : Subgroup G) V hV X = (⊤ : Subgroup ↥X).map F := by
    rw [barSub]
    have hsub : (⊤ : Subgroup ↥X).map (Subgroup.inclusion hXstab) =
        X.subgroupOf (stabTil (⊥ : Subgroup G) V) := by
      ext g
      rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      exact ⟨fun ⟨y, _, hy'⟩ => hy' ▸ y.2, fun hg => ⟨⟨g, hg⟩, Subgroup.mem_top _, rfl⟩⟩
    rw [← hsub, Subgroup.map_map]
  rw [hbar, ← hxgen, MonoidHom.map_zpowers]
  rfl

private theorem s16c1614_mkTil_commutator_mem_commSub {V X : Subgroup G}
    (hV : IsElemAbelian 2 V) (hX : X ≤ stabTil (⊥ : Subgroup G) V) {v x : G} (hv : v ∈ V)
    (hx : x ∈ X) :
    mkTil (⊥ : Subgroup G) V hV (IntMod.mk hV ⟨⁅v, x⁆,
        s16c1614_commutator_le_of_le_stabTil hX
          (Subgroup.commutator_mem_commutator hv hx)⟩) ∈
      commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV))
        (barSub (⊥ : Subgroup G) V hV X) := by
  classical
  have hcommV : ⁅V, X⁆ ≤ V := s16c1614_commutator_le_of_le_stabTil hX
  have hsq : ∀ w : Vtil (⊥ : Subgroup G) V hV, w⁻¹ = w := by
    intro w
    obtain ⟨y, rfl⟩ := mkTil_surjective (⊥ : Subgroup G) V hV w
    have h2 : (mkTil (⊥ : Subgroup G) V hV y) ^ 2 = 1 := by
      rw [← map_pow, IntMod.sq_eq_one y, map_one]
    rw [pow_two] at h2
    exact inv_eq_of_mul_eq_one_right h2
  have hmul : ∀ a b : Vtil (⊥ : Subgroup G) V hV, a * b = b * a := fun a b =>
    mul_comm a b
  set xb : MulAut (Vtil (⊥ : Subgroup G) V hV) := actTil (⊥ : Subgroup G) V hV ⟨x, hX hx⟩
    with hxb
  set a : Vtil (⊥ : Subgroup G) V hV := mkTil (⊥ : Subgroup G) V hV (IntMod.mk hV ⟨v, hv⟩)
    with ha
  have hmem2 : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp
    (stabTil_le_normalizer (⊥ : Subgroup G) V (hX hx)) v).1 hv
  have hmem3 : x * v⁻¹ * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp
    (stabTil_le_normalizer (⊥ : Subgroup G) V (hX hx)) v⁻¹).1 (V.inv_mem hv)
  have hb : xb a = mkTil (⊥ : Subgroup G) V hV (IntMod.mk hV ⟨x * v * x⁻¹, hmem2⟩) := by
    rw [hxb, ha, actTil_mk]
    rw [show (actStab (⊥ : Subgroup G) V hV ⟨x, hX hx⟩) (IntMod.mk hV ⟨v, hv⟩) =
        IntMod.mk hV ⟨x * v * x⁻¹, hmem2⟩ from by
      apply IntMod.val_injective
      rw [actStab_apply_val]
      rfl]
  have hc : mkTil (⊥ : Subgroup G) V hV (IntMod.mk hV ⟨x * v⁻¹ * x⁻¹, hmem3⟩) = xb a⁻¹ := by
    rw [hxb, ha, ← map_inv, actTil_mk]
    rw [show (actStab (⊥ : Subgroup G) V hV ⟨x, hX hx⟩) (IntMod.mk hV ⟨v, hv⟩)⁻¹ =
        IntMod.mk hV ⟨x * v⁻¹ * x⁻¹, hmem3⟩ from by
      rw [map_inv]
      congr 1
      apply IntMod.val_injective
      rw [IntMod.val_inv, actStab_apply_val]
      group
      rfl]
  have h1 : ⁅v, x⁆ = v * (x * v⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
  have hval : v * (x * v⁻¹ * x⁻¹) ∈ V := V.mul_mem hv hmem3
  have h2 : mkTil (⊥ : Subgroup G) V hV (IntMod.mk hV ⟨⁅v, x⁆, hcommV
      (Subgroup.commutator_mem_commutator hv hx)⟩) = xb a * a⁻¹ := by
    have h3 : IntMod.mk hV ⟨⁅v, x⁆, hcommV
        (Subgroup.commutator_mem_commutator hv hx)⟩ =
        IntMod.mk hV ⟨v * (x * v⁻¹ * x⁻¹), hval⟩ := Subtype.ext h1
    rw [h3]
    have h4 : IntMod.mk hV ⟨v * (x * v⁻¹ * x⁻¹), hval⟩ =
        IntMod.mk hV ⟨v, hv⟩ * IntMod.mk hV ⟨x * v⁻¹ * x⁻¹, hmem3⟩ := rfl
    rw [h4, map_mul, hc]
    simp only [hsq]
    change a * xb a = xb a * a
    exact hmul a (xb a)
  rw [h2]
  exact Subgroup.subset_closure ⟨xb, actTil_mem_barSub (⊥ : Subgroup G) V hV hx (hX hx),
    a, Subgroup.mem_top _, rfl⟩

private theorem s16c1614_imgTil_commutator_eq_commSub {V X : Subgroup G}
    (hV : IsElemAbelian 2 V) (hX : X ≤ stabTil (⊥ : Subgroup G) V) :
    imgTil (⊥ : Subgroup G) V hV ⁅V, X⁆ =
      commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV)) (barSub (⊥ : Subgroup G) V hV X) := by
  classical
  have hcommV : ⁅V, X⁆ ≤ V := s16c1614_commutator_le_of_le_stabTil hX
  have hgen : ∀ {v x : G} (hv : v ∈ V) (hx : x ∈ X),
      mkTil (⊥ : Subgroup G) V hV (IntMod.mk hV ⟨⁅v, x⁆,
          s16c1614_commutator_le_of_le_stabTil hX
            (Subgroup.commutator_mem_commutator hv hx)⟩) ∈
      commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV)) (barSub (⊥ : Subgroup G) V hV X) :=
    fun hv hx => s16c1614_mkTil_commutator_mem_commSub hV hX hv hx
  apply le_antisymm
  · rw [imgTil, Subgroup.map_le_iff_le_comap]
    intro w hw
    rw [Subgroup.mem_comap]
    have hmain : ∀ (a : G) (ha : a ∈ ⁅V, X⁆), mkTil (⊥ : Subgroup G) V hV
        (IntMod.mk hV ⟨a, hcommV ha⟩) ∈
        commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV))
          (barSub (⊥ : Subgroup G) V hV X) := by
      intro a ha
      induction ha using Subgroup.closure_induction with
      | mem a ha =>
        obtain ⟨v, hv, x, hx, rfl⟩ := ha
        exact hgen hv hx
      | one =>
        rw [show IntMod.mk hV ⟨1, hcommV (one_mem _)⟩ = 1 from Subtype.ext rfl, map_one]
        exact one_mem _
      | mul a b ha hb iha ihb =>
        rw [show IntMod.mk hV ⟨a * b, hcommV (mul_mem ha hb)⟩ =
          IntMod.mk hV ⟨a, hcommV ha⟩ * IntMod.mk hV ⟨b, hcommV hb⟩ from Subtype.ext rfl,
          map_mul]
        exact mul_mem iha ihb
      | inv a ha iha =>
        rw [show IntMod.mk hV ⟨a⁻¹, hcommV (inv_mem ha)⟩ =
          (IntMod.mk hV ⟨a, hcommV ha⟩)⁻¹ from Subtype.ext rfl, map_inv]
        exact inv_mem iha
    have hw' : IntMod.mk hV ⟨w.val, hcommV hw⟩ = w := IntMod.val_injective rfl
    have hres := hmain w.val hw
    rwa [hw'] at hres
  · rw [commSub, Subgroup.closure_le]
    rintro c ⟨xb, hxb, w, -, rfl⟩
    change xb w * w⁻¹ ∈ imgTil (⊥ : Subgroup G) V hV ⁅V, X⁆
    rw [mem_imgTil]
    obtain ⟨x, hxX, hxb_eq⟩ := (mem_barSub (⊥ : Subgroup G) V hV X xb).1 hxb
    obtain ⟨y, rfl⟩ := mkTil_surjective (⊥ : Subgroup G) V hV w
    subst hxb_eq
    obtain ⟨v, rfl⟩ : ∃ v : V, IntMod.mk hV v = y :=
      ⟨⟨y.val, y.val_mem⟩, IntMod.val_injective rfl⟩
    have hmem2 : (x : G) * (v : G) * (x : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp
      (stabTil_le_normalizer (⊥ : Subgroup G) V (hX hxX)) (v : G)).1 v.2
    have hmem3 : (x : G) * (v : G) * (x : G)⁻¹ * (v : G)⁻¹ ∈ V :=
      V.mul_mem hmem2 (V.inv_mem v.2)
    have hcomm : ⁅(x : G), (v : G)⁆ ∈ ⁅V, X⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hxX v.2
    refine ⟨IntMod.mk hV ⟨(x : G) * (v : G) * (x : G)⁻¹ * (v : G)⁻¹, hmem3⟩, hcomm, ?_⟩
    have h1 : (actStab (⊥ : Subgroup G) V hV x) (IntMod.mk hV v) =
        IntMod.mk hV ⟨(x : G) * (v : G) * (x : G)⁻¹, hmem2⟩ := by
      apply IntMod.val_injective
      rw [actStab_apply_val]
      rfl
    rw [actTil_mk, h1, ← map_inv, ← map_mul]
    rfl

theorem s16c1614_cartanBar_of_cartan (D : Data G) {V U X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil (⊥ : Subgroup G) V) {n : ℕ} (hXM : X ≤ D.M) (hcyc : IsCyclic ↥X)
    (hcard : Nat.card X = 2 ^ n - 1) (hCV : V ⊓ centralizer (X : Set G) = U) (hUV : U ≠ V)
    (hreg : ActsRegularlyOn X (nonIdentity ⁅V, X⁆)) :
    ∃ x : MulAut (Vtil (⊥ : Subgroup G) V hV), CartanBar1614 D V hV n x := by
  classical
  have hXstab : X ≤ stabTil (⊥ : Subgroup G) V := hXM.trans hMs
  have hcommV : ⁅V, X⁆ ≤ V := s16c1614_commutator_le_of_le_stabTil hXstab
  have hcomm_ne : ⁅V, X⁆ ≠ ⊥ := by
    intro hbot
    have h1 : V ≤ Subgroup.centralizer (X : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
    have h2 : V ≤ U := by rw [← hCV]; exact le_inf le_rfl h1
    exact hUV (le_antisymm (hCV ▸ inf_le_left) h2)
  have hXdis : X ⊓ Subgroup.centralizer (V : Set G) = ⊥ :=
    s16c1614_inf_centralizer_eq_bot_of_regular_action hcommV hcomm_ne hreg
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hg' : Subgroup.zpowers g = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact hg y
  have hgord : orderOf g = Nat.card X :=
    orderOf_eq_card_of_forall_mem_zpowers (fun y => by rw [hg']; exact Subgroup.mem_top y)
  set xbar : MulAut (Vtil (⊥ : Subgroup G) V hV) :=
    actTil (⊥ : Subgroup G) V hV ⟨(g : G), hXstab g.2⟩ with hxb
  have hxbarM : xbar ∈ Mbar D.M (⊥ : Subgroup G) V hV :=
    actTil_mem_barSub (⊥ : Subgroup G) V hV (hXM g.2) (hMs (hXM g.2))
  have hxbarord : orderOf xbar = 2 ^ n - 1 := by
    have h1 := s16c1614_orderOf_actTil_bot_eq hV hXstab hXdis g
    rw [hxb]
    exact h1.trans (hgord.trans hcard)
  have hbarX : barSub (⊥ : Subgroup G) V hV X = Subgroup.zpowers xbar := by
    rw [hxb]
    convert s16c1614_barSub_eq_zpowers_of_gen hV hXstab hg' using 2
    exact congrArg (actTil (⊥ : Subgroup G) V hV) (Subtype.ext rfl)
  have himg : imgTil (⊥ : Subgroup G) V hV ⁅V, X⁆ =
      commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV)) (Subgroup.zpowers xbar) := by
    rw [s16c1614_imgTil_commutator_eq_commSub hV hXstab, hbarX]
  have hcardbar : Nat.card ↥(commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV))
      (Subgroup.zpowers xbar)) = 2 ^ n := by
    rw [← himg]
    have hinj : Function.Injective (mkTil (⊥ : Subgroup G) V hV) :=
      s16c1614_mkTil_bot_injective hV
    have hcardimg : Nat.card ↥(imgTil (⊥ : Subgroup G) V hV ⁅V, X⁆) =
        Nat.card ↥⁅V, X⁆ := by
      have h1 : Nat.card ↥(imgTil (⊥ : Subgroup G) V hV ⁅V, X⁆) =
          Nat.card ↥(intSub V hV ⁅V, X⁆) :=
        Nat.card_congr (Subgroup.equivMapOfInjective (intSub V hV ⁅V, X⁆)
          (mkTil (⊥ : Subgroup G) V hV) hinj).symm.toEquiv
      rw [h1]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcommV).toEquiv
    rw [hcardimg, CFSG.GroupTheory.natCard_commutator_eq_card_add_one hreg hcomm_ne, hcard]
    exact Nat.sub_add_cancel Nat.one_le_two_pow
  refine ⟨xbar, hxbarM, hxbarord, hcardbar, ?_⟩
  intro w hw w' hw' hw1 hw'1
  rw [← himg] at hw hw'
  rw [mem_imgTil] at hw hw'
  obtain ⟨a, ha, haeq⟩ := hw
  obtain ⟨a', ha', ha'eq⟩ := hw'
  have ha1 : a.val ≠ 1 := by
    intro h1
    apply hw1
    have haeq1 : a = 1 := Subtype.ext h1
    rw [← haeq, haeq1, map_one]
  have ha'1 : a'.val ≠ 1 := by
    intro h1
    apply hw'1
    have ha'eq1 : a' = 1 := Subtype.ext h1
    rw [← ha'eq, ha'eq1, map_one]
  obtain ⟨b, hbX, hbconj⟩ := hreg.2.1 a.val ⟨ha, ha1⟩ a'.val ⟨ha', ha'1⟩
  obtain ⟨k, hk⟩ : ∃ k : ℤ, g ^ k = (⟨b⁻¹, X.inv_mem hbX⟩ : ↥X) := by
    have hmem : (⟨b⁻¹, X.inv_mem hbX⟩ : ↥X) ∈ Subgroup.zpowers g := by
      rw [hg']; exact Subgroup.mem_top _
    rwa [Subgroup.mem_zpowers_iff] at hmem
  refine ⟨xbar ^ k, Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩, ?_⟩
  have hxbar_k : xbar ^ k =
      actTil (⊥ : Subgroup G) V hV ⟨b⁻¹, hXstab (X.inv_mem hbX)⟩ := by
    have hxb' : xbar = actTil (⊥ : Subgroup G) V hV (Subgroup.inclusion hXstab g) := hxb
    rw [hxb', ← map_zpow, ← map_zpow, hk]
    rfl
  rw [← haeq, ← ha'eq, hxbar_k, actTil_mk]
  congr 1
  apply IntMod.val_injective (hV := hV)
  rw [actStab_apply_val, inv_inv, hbconj]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
