module

public import CFSG.GroupTheory.RegularActionIndexTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ModuleBridges
public import CFSG.LocalAnalysis.WeakClosure81.ElevenFourBPair
public import CFSG.LocalAnalysis.WeakClosure81.ElevenTen
public import CFSG.LocalAnalysis.WeakClosure81.ElevenFour
public import CFSG.Quasithin.Background.SmithD37Fac
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem2
public import CFSG.Assembly.OpenBridges

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.QuasithinUnique.Lin2 (ActsRegularlyOn nonIdentity)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort (setting11_of_inCalV1)
open CFSG.GroupTheory
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def K_HJData : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) → rk W = 12 →
    ∀ (Y L : Subgroup (MulAut W)),
      L ≤ Y → (L.subgroupOf Y).Normal → IsSpor ↥L .J2 → IsIrrOn L ⊤ ⊥ →
      (Nat.card Y ∣ 6 * Nat.card L) ∧
        (∀ x : MulAut W, x ∈ Y → orderOf x = 7 → fixV (Subgroup.zpowers x) = ⊥) ∧
        (∀ x : MulAut W, x ∈ Y → orderOf x = 3 →
          4 ≤ rk (commSub (⊤ : Subgroup W) (Subgroup.zpowers x)))

theorem inCalWStar_of_hyp125 (D : Data G) {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h0 : V₀ = ⊥) : InCalWStar D.M D.T V := by
  rcases hV.1 with ⟨hW, -⟩ | ⟨hV0, -, -⟩
  · exact hW
  · rw [h0] at hV0
    exact absurd rfl hV0.1.1

theorem inCalV1_of_hyp125 (D : Data G) {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h0 : V₀ = ⊥) : InCalV1 D.M D.T V :=
  (inCalWStar_of_hyp125 D hV h0).1.1

theorem setting11_of_hyp125 (D : Data G) {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h0 : V₀ = ⊥) :
    Setting11 D.M V (D.T ⊓ Subgroup.centralizer (V : Set G)) :=
  setting11_of_inCalV1 D (inCalV1_of_hyp125 D hV h0)

theorem one_lt_rMV_of_mBar_eq_four {M V Q : Subgroup G}
    (hset : Setting11 M V Q) (hm : mBar M ⊥ V hset.isElemAbelian = 4) :
    1 < rMV M V := by
  have h116 := eleven_six_B hset
  rw [hm] at h116
  by_contra hcon
  push Not at hcon
  have h2 : 2 * rMV M V ≤ 2 * (1 : ℕ∞) := by gcongr
  rw [mul_one] at h2
  have h42 : (4 : ℕ∞) ≤ 2 := le_trans h116 h2
  norm_num at h42

theorem six_le_mQuot_bot (D : Data G) {V₀ V : Subgroup G} {L : Subgroup G}
    (h25 : R17_25At D V₀ V) (c : Ctx17_29 D V₀ V L) :
    (6 : ℕ∞) ≤ E3.mQuot V (⊥ : Subgroup G) := by
  have hV := c.ctx.hyp125.isElemAbelian
  have h12 : rk (Vtil V₀ V hV) = 12 := (h25 L c.ctx).2.1
  rw [c.v0] at h12
  have hmt : E3.mQuot V (⊥ : Subgroup G) = rk (Vtil ⊥ V hV) := by
    rw [E3.mQuot, Subgroup.relIndex_bot_left, rk,
      card_Vtil_eq (⊥ : Subgroup G) V hV bot_le, Subgroup.card_bot, one_mul]
  rw [hmt, h12]
  norm_num

theorem actTil_bot_injective {V X : Subgroup G} (hV : IsElemAbelian 2 V)
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
    (TwelveTwentyThree.actTil_bot_eq_one_iff V hV _).1 h1
  have hbot : ((x : G) * (y : G)⁻¹) ∈ (⊥ : Subgroup G) := by
    have hinf : ((x : G) * (y : G)⁻¹) ∈ X ⊓ Subgroup.centralizer (V : Set G) :=
      Subgroup.mem_inf.2 ⟨hmem, hcent⟩
    rwa [hdis] at hinf
  exact Subtype.ext (mul_inv_eq_one.1 (Subgroup.mem_bot.1 hbot))

theorem card_barSub_bot_eq {V X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hX : X ≤ stabTil (⊥ : Subgroup G) V)
    (hdis : X ⊓ Subgroup.centralizer (V : Set G) = ⊥) :
    Nat.card (barSub (⊥ : Subgroup G) V hV X) = Nat.card X := by
  classical
  let F : X →* MulAut (Vtil (⊥ : Subgroup G) V hV) :=
    (actTil (⊥ : Subgroup G) V hV).comp (Subgroup.inclusion hX)
  have hF : Function.Injective F := actTil_bot_injective hV hX hdis
  have hsub : (⊤ : Subgroup ↥X).map (Subgroup.inclusion hX) =
      X.subgroupOf (stabTil (⊥ : Subgroup G) V) := by
    ext g
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact ⟨fun ⟨x, _, hx'⟩ => hx' ▸ x.2, fun hg => ⟨⟨g, hg⟩, Subgroup.mem_top _, rfl⟩⟩
  have hbar : barSub (⊥ : Subgroup G) V hV X = (⊤ : Subgroup ↥X).map F := by
    rw [barSub, ← hsub, Subgroup.map_map]
  rw [hbar, Subgroup.card_map_of_injective hF, Subgroup.card_top]

theorem orderOf_actTil_bot_eq {V X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hX : X ≤ stabTil (⊥ : Subgroup G) V)
    (hdis : X ⊓ Subgroup.centralizer (V : Set G) = ⊥) (x : X) :
    orderOf (actTil (⊥ : Subgroup G) V hV (Subgroup.inclusion hX x)) = orderOf x :=
  orderOf_injective ((actTil (⊥ : Subgroup G) V hV).comp (Subgroup.inclusion hX))
    (actTil_bot_injective hV hX hdis) x

theorem rk_commSub_actTil_bot_eq {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {x : G} (hx : x ∈ stabTil (⊥ : Subgroup G) V) :
    rk (commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV))
        (Subgroup.zpowers (actTil (⊥ : Subgroup G) V hV ⟨x, hx⟩))) =
      E3.mQuot V (V ⊓ Subgroup.centralizer ({x} : Set G)) := by
  classical
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := by
    have h := hx
    rw [stabTil] at h
    exact (Subgroup.mem_inf.1 h).1
  set ψ := TwelveShort.mkTilEquiv V hV with hψ
  have hcongr : actTil (⊥ : Subgroup G) V hV ⟨x, hx⟩ =
      MulAut.congr ψ (convI hV ⟨x, hxN⟩) := TwelveShort.actTil_bot_eq_congr V hV ⟨x, hx⟩
  have hzp : Subgroup.zpowers (actTil (⊥ : Subgroup G) V hV ⟨x, hx⟩) =
      Subgroup.zpowers (MulAut.congr ψ (convI hV ⟨x, hxN⟩)) := by
    rw [hcongr]
  have hcomm : commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV))
      (Subgroup.zpowers (MulAut.congr ψ (convI hV ⟨x, hxN⟩))) =
      (commSub (⊤ : Subgroup (IntMod V hV))
        (Subgroup.zpowers (convI hV ⟨x, hxN⟩))).map ψ.toMonoidHom := by
    have h := CFSG.Quasithin.SmithD37.commSub_map_congr ψ
      (Subgroup.zpowers (convI hV ⟨x, hxN⟩)) (⊤ : Subgroup (IntMod V hV))
    simpa [Subgroup.map_top] using h
  have hcard : rk ((commSub (⊤ : Subgroup (IntMod V hV))
      (Subgroup.zpowers (convI hV ⟨x, hxN⟩))).map ψ.toMonoidHom) =
      rk (commSub (⊤ : Subgroup (IntMod V hV))
        (Subgroup.zpowers (convI hV ⟨x, hxN⟩))) := by
    unfold rk
    exact congrArg (padicValNat 2)
      (Nat.card_congr (Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).symm.toEquiv)
  rw [hzp, hcomm, hcard, ← commV_eq_commSub, ← rkIdx_fixV_zpowers]
  have hcard := CFSG.Quasithin.H13.Sec1212.card_fixV_zpowers_convI hV ⟨x, hxN⟩
  have hcardSub : Nat.card ↥((V ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf V) =
      Nat.card ↥(V ⊓ Subgroup.centralizer ({x} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : V ⊓ Subgroup.centralizer ({x} : Set G) ≤ V)).toEquiv
  have h3 : rk (fixV (Subgroup.zpowers (convI hV ⟨x, hxN⟩))) =
      rk ((V ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf V) := by
    unfold rk
    rw [hcard, hcardSub]
  have h1 := rk_add_rkIdx (fixV (Subgroup.zpowers (convI hV ⟨x, hxN⟩)))
  have h2 := rk_add_rkIdx ((V ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf V)
  have h4 : rk (IntMod V hV) = rk V := rfl
  rw [E3.mQuot_eq_rkIdx]
  omega

theorem imgTil_le_fixV_actTil {V U : Subgroup G} (hV : IsElemAbelian 2 V)
    {x : G} (hx : x ∈ stabTil (⊥ : Subgroup G) V)
    (hxU : ∀ u ∈ U, x * u * x⁻¹ = u) :
    imgTil (⊥ : Subgroup G) V hV U ≤
      fixV (Subgroup.zpowers (actTil (⊥ : Subgroup G) V hV ⟨x, hx⟩)) := by
  intro q hq
  rw [mem_imgTil] at hq
  obtain ⟨w, hwU, rfl⟩ := hq
  have hxw : actTil (⊥ : Subgroup G) V hV ⟨x, hx⟩ (mkTil (⊥ : Subgroup G) V hV w) =
      mkTil (⊥ : Subgroup G) V hV w := by
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot]
    rw [hxU w.val hwU, mul_inv_cancel]
  rw [mem_fixV]
  intro y hy
  rw [Subgroup.mem_zpowers_iff] at hy
  obtain ⟨k, rfl⟩ := hy
  induction k using Int.induction_on with
  | zero => rfl
  | succ n ih => rw [zpow_add_one, MulAut.mul_apply, hxw, ih]
  | pred n ih =>
    rw [zpow_sub_one, MulAut.mul_apply]
    calc (actTil (⊥ : Subgroup G) V hV ⟨x, hx⟩ ^ (-(n : ℤ)))
          ((actTil (⊥ : Subgroup G) V hV ⟨x, hx⟩)⁻¹ (mkTil (⊥ : Subgroup G) V hV w))
        = (actTil (⊥ : Subgroup G) V hV ⟨x, hx⟩ ^ (-(n : ℤ)))
          ((actTil (⊥ : Subgroup G) V hV ⟨x, hx⟩)⁻¹
            ((actTil (⊥ : Subgroup G) V hV ⟨x, hx⟩) (mkTil (⊥ : Subgroup G) V hV w))) := by
          rw [hxw]
      _ = mkTil (⊥ : Subgroup G) V hV w := by rw [MulAut.inv_apply_self, ih]

theorem commutator_le_of_le_stabTil {V X : Subgroup G}
    (hX : X ≤ stabTil (⊥ : Subgroup G) V) : ⁅V, X⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv xx hxx
  have hmem : xx * v⁻¹ * xx⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp
    (stabTil_le_normalizer (⊥ : Subgroup G) V (hX hxx)) v⁻¹).1 (V.inv_mem hv)
  have h1 : ⁅v, xx⁆ = v * (xx * v⁻¹ * xx⁻¹) := by rw [commutatorElement_def]; group
  rw [h1]; exact V.mul_mem hv hmem

theorem inf_centralizer_eq_bot_of_regular_action {V X : Subgroup G}
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

theorem barSub_eq_zpowers_of_gen {V X : Subgroup G} (hV : IsElemAbelian 2 V)
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

theorem mkTil_commutator_mem_commSub {V X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hX : X ≤ stabTil (⊥ : Subgroup G) V) {v x : G} (hv : v ∈ V) (hx : x ∈ X) :
    mkTil (⊥ : Subgroup G) V hV (IntMod.mk hV ⟨⁅v, x⁆, commutator_le_of_le_stabTil hX
        (Subgroup.commutator_mem_commutator hv hx)⟩) ∈
      commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV)) (barSub (⊥ : Subgroup G) V hV X) := by
  classical
  have hcommV : ⁅V, X⁆ ≤ V := commutator_le_of_le_stabTil hX
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

theorem imgTil_commutator_eq_commSub {V X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hX : X ≤ stabTil (⊥ : Subgroup G) V) :
    imgTil (⊥ : Subgroup G) V hV ⁅V, X⁆ =
      commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV)) (barSub (⊥ : Subgroup G) V hV X) := by
  classical
  have hcommV : ⁅V, X⁆ ≤ V := commutator_le_of_le_stabTil hX
  have hgen : ∀ {v x : G} (hv : v ∈ V) (hx : x ∈ X),
      mkTil (⊥ : Subgroup G) V hV (IntMod.mk hV ⟨⁅v, x⁆, commutator_le_of_le_stabTil hX
        (Subgroup.commutator_mem_commutator hv hx)⟩) ∈
      commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV)) (barSub (⊥ : Subgroup G) V hV X) :=
    fun hv hx => mkTil_commutator_mem_commSub hV hX hv hx
  apply le_antisymm
  · rw [imgTil, Subgroup.map_le_iff_le_comap]
    intro w hw
    rw [Subgroup.mem_comap]
    have hmain : ∀ (a : G) (ha : a ∈ ⁅V, X⁆), mkTil (⊥ : Subgroup G) V hV
        (IntMod.mk hV ⟨a, hcommV ha⟩) ∈
        commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV)) (barSub (⊥ : Subgroup G) V hV X) := by
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
    obtain ⟨v, rfl⟩ : ∃ v : V, IntMod.mk hV v = y := ⟨⟨y.val, y.val_mem⟩, IntMod.val_injective rfl⟩
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

private theorem rk_imgTil_eq_twelve_sub {V U : Subgroup G} (hV : IsElemAbelian 2 V)
    (h12 : rk (Vtil (⊥ : Subgroup G) V hV) = 12) :
    rk (imgTil (⊥ : Subgroup G) V hV U) = 12 - E3.mQuot V U := by
  have himgcard : Nat.card ↥(imgTil (⊥ : Subgroup G) V hV U) =
      Nat.card ↥(U.subgroupOf V) := by
    have hinj : Function.Injective (mkTil (⊥ : Subgroup G) V hV) :=
      (TwelveShort.mkTilEquiv V hV).injective
    exact Nat.card_congr (Subgroup.equivMapOfInjective (intSub V hV U)
      (mkTil (⊥ : Subgroup G) V hV) hinj).symm.toEquiv
  have h1 := rk_add_rkIdx (U.subgroupOf V)
  have h2 : rk (IntMod V hV) = 12 := by
    rw [← h12]
    exact congrArg (padicValNat 2)
      (Nat.card_congr (TwelveShort.mkTilEquiv V hV).toEquiv)
  have h3 : rkIdx (U.subgroupOf V) = E3.mQuot V U := (E3.mQuot_eq_rkIdx V U).symm
  have h4 : rk (imgTil (⊥ : Subgroup G) V hV U) = rk (U.subgroupOf V) := by
    unfold rk
    rw [himgcard]
  have h5 : rk (U.subgroupOf V) + E3.mQuot V U = 12 := by
    have h2' : rk ↥V = 12 := h2
    rw [h3, h2'] at h1
    exact h1
  rw [h4]
  exact Nat.eq_sub_of_add_eq h5
private theorem false_of_involution_fixV (D : Data G) {V L U : Subgroup G}
    (c : Ctx17_29 D ⊥ V L)
    (h291 : R17_29_1At D ⊥ V) (h292 : R17_29_2At D ⊥ V) (h25 : R17_25At D ⊥ V)
    (hUV : U ≤ V) (hCU : ¬ Subgroup.centralizer (U : Set G) ≤ D.M)
    (hrU : (E3.mQuot V U : ℕ∞) = rMV D.M V) (hr6 : rMV D.M V < 6)
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil (⊥ : Subgroup G) V)
    (t : MulAut (Vtil (⊥ : Subgroup G) V hV)) (htM : t ∈ Mbar D.M (⊥ : Subgroup G) V hV)
    (htord : orderOf t = 2)
    (hrk6 : rk (commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV))
      (Subgroup.zpowers t)) < 6)
    (hUt : imgTil (⊥ : Subgroup G) V hV U ≤ fixV (Subgroup.zpowers t)) : False := by
  classical
  have hLM : L ≤ D.M := CFSG.Open.IsSubnormal.le c.ctx.mem_calC.1
  obtain ⟨v₁, v₂, hP⟩ := h291 L c
  have hCv₂ : Subgroup.centralizer ({(v₂ : G)} : Set G) ≤ D.M := hP.2.2.2.2.2.2.2.2.2
  obtain ⟨hrk4, hhyp⟩ := h292 L c v₂ ⟨v₁, hP⟩ t htM htord hrk6
  have h12 : rk (Vtil (⊥ : Subgroup G) V hV) = 12 := (h25 L c.ctx).2.1
  have hWrk : rk (fixV (Subgroup.zpowers t)) = 8 := by
    have h1 := rk_add_rkIdx (fixV (Subgroup.zpowers t))
    have h2 : rkIdx (fixV (Subgroup.zpowers t)) = 4 := by
      rw [rkIdx_fixV_zpowers, commV_eq_commSub]
      exact hrk4
    omega
  have hWne : fixV (Subgroup.zpowers t) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hWrk
    simp [rk] at hWrk
  have hArk : rk (imgTil (⊥ : Subgroup G) V hV U) = 12 - E3.mQuot V U :=
    rk_imgTil_eq_twelve_sub hV h12
  have hrU6 : E3.mQuot V U < 6 := by
    have h : (E3.mQuot V U : ℕ∞) < 6 := by rw [hrU]; exact hr6
    exact_mod_cast h
  have hVtil2 := s15_Infra_vtil_sq_eq_one (⊥ : Subgroup G) V hV
  let Wf : Subgroup (Vtil (⊥ : Subgroup G) V hV) := fixV (Subgroup.zpowers t)
  let A' : Subgroup ↥Wf := (imgTil (⊥ : Subgroup G) V hV U).subgroupOf Wf
  have hA'rk : rk A' = rk (imgTil (⊥ : Subgroup G) V hV U) := by
    unfold rk
    exact congrArg (padicValNat 2) (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hUt).toEquiv)
  have hWfne : (⊤ : Subgroup ↥Wf) ≠ ⊥ := by
    intro hbot
    apply hWne
    rw [eq_bot_iff]
    intro v hv
    have h1 : (⟨v, hv⟩ : ↥Wf) ∈ (⊤ : Subgroup ↥Wf) := Subgroup.mem_top _
    rw [hbot] at h1
    have h2 : (⟨v, hv⟩ : ↥Wf) = 1 := Subgroup.mem_bot.1 h1
    simpa using congrArg Subtype.val h2
  obtain ⟨H', hH'le, hH'rel⟩ :=
    exists_relIndex_two_le_of_rk (W := ↥Wf) (A := A')
      (fun w => Subtype.ext (hVtil2 (w : Vtil (⊥ : Subgroup G) V hV)))
      hWfne (by
        have hm5 : E3.mQuot V U ≤ 5 := Nat.le_of_lt_succ (by simpa using hrU6)
        have h7 : 7 ≤ rk A' := by
          rw [hA'rk, hArk]
          exact Nat.le_trans (by norm_num : 7 ≤ 12 - 5) (Nat.sub_le_sub_left hm5 12)
        rw [hWrk]
        exact Nat.succ_le_succ h7)
  have hHle : H'.map Wf.subtype ≤ imgTil (⊥ : Subgroup G) V hV U := by
    intro v hv
    rw [Subgroup.mem_map] at hv
    obtain ⟨a, haH', rfl⟩ := hv
    exact Subgroup.mem_subgroupOf.1 (hH'le haH')
  have hHrel : (H'.map Wf.subtype).relIndex Wf = 2 := by
    have h1 := Subgroup.relIndex_map_map_of_injective (f := Wf.subtype) H' ⊤ Wf.subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype] at h1
    rw [h1, hH'rel]
  obtain ⟨l, hlL, w, hwl, hwH⟩ := hhyp (H'.map Wf.subtype) (hHle.trans hUt) hHrel
  have hwA : mkTil (⊥ : Subgroup G) V hV (IntMod.mk hV w) ∈ imgTil (⊥ : Subgroup G) V hV U :=
    hHle hwH
  rw [mem_imgTil] at hwA
  obtain ⟨y, hyU, hyeq⟩ := hwA
  have hyw : y = IntMod.mk hV w := (TwelveShort.mkTilEquiv V hV).injective hyeq
  have hwU : (w : G) ∈ U := by
    have h := hyU
    rwa [hyw] at h
  have hCw : Subgroup.centralizer ({(w : G)} : Set G) ≤ D.M := by
    have hw_eq : (w : G) = (l⁻¹)⁻¹ * (v₂ : G) * l⁻¹ := by
      rw [hwl]
      group
    have hcent : Subgroup.centralizer ({(w : G)} : Set G) =
        conjSubgroup (Subgroup.centralizer ({(v₂ : G)} : Set G)) l⁻¹ := by
      rw [CFSG.LocalAnalysis.WeakClosure81.conjSubgroup_centralizer_singleton (v₂ : G) l⁻¹,
        hw_eq]
    rw [hcent]
    refine (CFSG.Quasithin.E3.conjSubgroup_mono_left l⁻¹ hCv₂).trans ?_
    rw [conjSubgroup_eq_iff_mem_normalizer.2
      (Subgroup.le_normalizer (hLM (L.inv_mem hlL)))]
  exact hCU ((Subgroup.centralizer_le (Set.singleton_subset_iff.2 hwU)).trans hCw)

theorem twoElement_mem_centralizer_of_minimizer (D : Data G) {V L U : Subgroup G}
    (c : Ctx17_29 D ⊥ V L)
    (h291 : R17_29_1At D ⊥ V) (h292 : R17_29_2At D ⊥ V)
    (h25 : R17_25At D ⊥ V)
    (hUV : U ≤ V) (hCU : ¬ Subgroup.centralizer (U : Set G) ≤ D.M)
    (hrU : (E3.mQuot V U : ℕ∞) = rMV D.M V) (hr6 : rMV D.M V < 6)
    {x : G} (hxM : x ∈ D.M) (hxU : x ∈ Subgroup.centralizer (U : Set G))
    (hx2 : ∃ k : ℕ, orderOf x = 2 ^ k) :
    x ∈ Subgroup.centralizer (V : Set G) := by
  classical
  by_contra hxV
  have hV : IsElemAbelian 2 V := c.ctx.hyp125.isElemAbelian
  have hM : D.M ≤ Subgroup.normalizer (V : Set G) := c.ctx.hyp125.pairFacts.le_normalizer
  have hMs : D.M ≤ stabTil (⊥ : Subgroup G) V :=
    le_stabTil hM (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hLM : L ≤ D.M := CFSG.Open.IsSubnormal.le c.ctx.mem_calC.1
  obtain ⟨v₁, v₂, hP⟩ := h291 L c
  have hCv₂ : Subgroup.centralizer ({(v₂ : G)} : Set G) ≤ D.M := hP.2.2.2.2.2.2.2.2.2
  set φ : MulAut (Vtil (⊥ : Subgroup G) V hV) := actTil (⊥ : Subgroup G) V hV ⟨x, hMs hxM⟩
    with hφdef
  have hφ1 : φ ≠ 1 := fun h =>
    hxV ((TwelveTwentyThree.actTil_bot_eq_one_iff V hV _).1 h)
  obtain ⟨k, hk⟩ := hx2
  have hxk : x ^ 2 ^ k = 1 := by rw [← hk, pow_orderOf_eq_one]
  have hφk : φ ^ (2 ^ k) = 1 := by
    have h1 : (⟨x, hMs hxM⟩ : stabTil (⊥ : Subgroup G) V) ^ (2 ^ k) = 1 :=
      Subtype.ext (by simpa using hxk)
    rw [hφdef, ← map_pow, h1, map_one]
  have hdvd : orderOf φ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hφk
  obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj0 : j ≠ 0 := by
    intro h0
    exact hφ1 (orderOf_eq_one_iff.mp (by rw [hj, h0, pow_zero]))
  obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  set t : MulAut (Vtil (⊥ : Subgroup G) V hV) := φ ^ (2 ^ j') with htdef
  have htord : orderOf t = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [htdef, ← pow_mul, ← pow_succ, ← hj, pow_orderOf_eq_one]
    · intro h1
      have h1' : φ ^ (2 ^ j') = 1 := by rw [← htdef]; exact h1
      have hdvd' : orderOf φ ∣ 2 ^ j' := orderOf_dvd_of_pow_eq_one h1'
      rw [hj] at hdvd'
      have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 2 ≤ 2)).1 hdvd'
      omega
  have htM : t ∈ Mbar D.M ⊥ V hV := by
    have hφM : φ ∈ Mbar D.M ⊥ V hV :=
      actTil_mem_barSub (⊥ : Subgroup G) V hV hxM (hMs hxM)
    exact pow_mem hφM _
  have hxU' : ∀ u ∈ U, x * u * x⁻¹ = u := by
    intro u hu
    have h1 := (Subgroup.mem_centralizer_iff.1 hxU) u hu
    rw [h1.symm]
    group
  have hUφ : imgTil (⊥ : Subgroup G) V hV U ≤ fixV (Subgroup.zpowers φ) :=
    imgTil_le_fixV_actTil hV (hMs hxM) hxU'
  have hUt : imgTil (⊥ : Subgroup G) V hV U ≤ fixV (Subgroup.zpowers t) := by
    refine hUφ.trans ?_
    intro q hq
    rw [mem_fixV] at hq ⊢
    intro y hy
    exact hq y ((Subgroup.zpowers_le.2 (pow_mem (Subgroup.mem_zpowers φ) (2 ^ j'))) hy)
  have hrkφ : rk (commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV))
      (Subgroup.zpowers φ)) = E3.mQuot V (V ⊓ Subgroup.centralizer ({x} : Set G)) := by
    rw [hφdef]
    exact rk_commSub_actTil_bot_eq hV (hMs hxM)
  have hleU : U ≤ V ⊓ Subgroup.centralizer ({x} : Set G) := by
    refine le_inf hUV ?_
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (Subgroup.mem_centralizer_iff.1 hxU u hu).symm
  have hmU : E3.mQuot V (V ⊓ Subgroup.centralizer ({x} : Set G)) ≤ E3.mQuot V U :=
    E3.mQuot_mono hleU
  have hrk_le : rk (commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV))
      (Subgroup.zpowers t)) ≤
      rk (commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV)) (Subgroup.zpowers φ)) :=
    rk_mono (commSub_mono le_rfl
      (Subgroup.zpowers_le.2 (pow_mem (Subgroup.mem_zpowers φ) (2 ^ j'))))
  have hrk6 : rk (commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV))
      (Subgroup.zpowers t)) < 6 := by
    have h1 : (rk (commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV))
        (Subgroup.zpowers t)) : ℕ∞) < 6 := by
      calc (rk (commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV))
            (Subgroup.zpowers t)) : ℕ∞)
          ≤ (rk (commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV))
            (Subgroup.zpowers φ)) : ℕ∞) := by exact_mod_cast hrk_le
        _ = (E3.mQuot V (V ⊓ Subgroup.centralizer ({x} : Set G)) : ℕ∞) := by rw [hrkφ]
        _ ≤ (E3.mQuot V U : ℕ∞) := by exact_mod_cast hmU
        _ = rMV D.M V := hrU
        _ < 6 := hr6
    exact_mod_cast h1
  exact false_of_involution_fixV D c h291 h292 h25 hUV hCU hrU hr6 hV hMs t htM htord hrk6 hUt

theorem barSub_ne_bot_of_isIrrOn {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hirr : IsIrrOn (barSub (⊥ : Subgroup G) V hV L) ⊤ ⊥)
    (h12 : rk (Vtil (⊥ : Subgroup G) V hV) = 12) :
    barSub (⊥ : Subgroup G) V hV L ≠ ⊥ := by
  classical
  intro hbot
  have hW2 := s15_Infra_vtil_sq_eq_one (⊥ : Subgroup G) V hV
  haveI : Nontrivial (Vtil (⊥ : Subgroup G) V hV) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    rw [CFSG.Quasithin.card_eq_two_pow_of_isPGroup (CFSG.Quasithin.isPGroup_two_of_sq_eq_one hW2), h12]
    norm_num
  obtain ⟨q, hq⟩ := exists_ne (1 : Vtil (⊥ : Subgroup G) V hV)
  let J : Subgroup (Vtil (⊥ : Subgroup G) V hV) := Subgroup.zpowers q
  have hJstable : StableUnder (barSub (⊥ : Subgroup G) V hV L) J := by
    rw [hbot]
    intro x hx
    have hx1 : x = 1 := Subgroup.mem_bot.1 hx
    intro u hu
    simpa [hx1] using hu
  have hJne : J ≠ ⊥ := by
    intro h
    have hmem : q ∈ (⊥ : Subgroup (Vtil (⊥ : Subgroup G) V hV)) :=
      h ▸ Subgroup.mem_zpowers q
    exact hq (Subgroup.mem_bot.1 hmem)
  have hJnetop : J ≠ ⊤ := by
    intro h
    have hcard : Nat.card (Vtil (⊥ : Subgroup G) V hV) = Nat.card J := by
      rw [h]
      simp
    have hord : orderOf q ∣ 2 := orderOf_dvd_of_pow_eq_one (hW2 q)
    have hcardJ : Nat.card J = orderOf q := Nat.card_zpowers q
    have hle : Nat.card (Vtil (⊥ : Subgroup G) V hV) ≤ 2 := by
      rw [hcard, hcardJ]
      exact Nat.le_of_dvd (by norm_num) hord
    have hbig : Nat.card (Vtil (⊥ : Subgroup G) V hV) = 2 ^ 12 := by
      rw [CFSG.Quasithin.card_eq_two_pow_of_isPGroup (CFSG.Quasithin.isPGroup_two_of_sq_eq_one hW2), h12]
    omega
  rcases hirr.2.2.2 J hJstable bot_le le_top with h | h
  · exact hJne h
  · exact hJnetop h

private theorem mem_barSub_of_order_five {D : Data G} {V L : Subgroup G}
    (hV : IsElemAbelian 2 V)
    [hN : ((barSub (⊥ : Subgroup G) V hV L).subgroupOf
      (Mbar D.M (⊥ : Subgroup G) V hV)).Normal]
    {φ : MulAut (Vtil (⊥ : Subgroup G) V hV)}
    (hφM : φ ∈ Mbar D.M (⊥ : Subgroup G) V hV) (hφord : orderOf φ = 5) (hφ1 : φ ≠ 1)
    (h5notdvd : ¬ 5 ∣ (barSub (⊥ : Subgroup G) V hV L).relIndex
      (Mbar D.M (⊥ : Subgroup G) V hV)) :
    φ ∈ barSub (⊥ : Subgroup G) V hV L := by
    by_contra hφnot
    let π : Mbar D.M (⊥ : Subgroup G) V hV →*
        (Mbar D.M (⊥ : Subgroup G) V hV) ⧸
          (barSub (⊥ : Subgroup G) V hV L).subgroupOf (Mbar D.M (⊥ : Subgroup G) V hV) :=
      QuotientGroup.mk' _
    have h1 : orderOf (π ⟨φ, hφM⟩) ∣ orderOf φ := by
      simpa using orderOf_map_dvd π (⟨φ, hφM⟩ : ↥(Mbar D.M (⊥ : Subgroup G) V hV))
    have h2 : orderOf (π ⟨φ, hφM⟩) ∣ Nat.card
        ((Mbar D.M (⊥ : Subgroup G) V hV) ⧸
          (barSub (⊥ : Subgroup G) V hV L).subgroupOf (Mbar D.M (⊥ : Subgroup G) V hV)) :=
      orderOf_dvd_natCard (π ⟨φ, hφM⟩)
    have h3 : Nat.card ((Mbar D.M (⊥ : Subgroup G) V hV) ⧸
          (barSub (⊥ : Subgroup G) V hV L).subgroupOf (Mbar D.M (⊥ : Subgroup G) V hV)) =
        (barSub (⊥ : Subgroup G) V hV L).relIndex (Mbar D.M (⊥ : Subgroup G) V hV) := rfl
    rw [h3] at h2
    have hcop : Nat.Coprime 5 ((barSub (⊥ : Subgroup G) V hV L).relIndex
        (Mbar D.M (⊥ : Subgroup G) V hV)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h5notdvd
    have hcop' : (orderOf (π ⟨φ, hφM⟩)).Coprime
        ((barSub (⊥ : Subgroup G) V hV L).relIndex (Mbar D.M (⊥ : Subgroup G) V hV)) :=
      hcop.coprime_dvd_left (hφord ▸ h1)
    have h4 : orderOf (π ⟨φ, hφM⟩) = 1 := hcop'.eq_one_of_dvd h2
    have h5 : π ⟨φ, hφM⟩ = 1 := orderOf_eq_one_iff.mp h4
    apply hφnot
    have h6 : (⟨φ, hφM⟩ : ↥(Mbar D.M (⊥ : Subgroup G) V hV)) ∈
        (barSub (⊥ : Subgroup G) V hV L).subgroupOf (Mbar D.M (⊥ : Subgroup G) V hV) :=
      (QuotientGroup.eq_one_iff _).1 h5
    exact Subgroup.mem_subgroupOf.1 h6

private theorem false_of_conj_v1_five {D : Data G} {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil (⊥ : Subgroup G) V)
    (hLM : L ≤ D.M) {x u l : G} {v₁ : ↥V} (hxV : x ∉ Subgroup.centralizer (V : Set G))
    (hxM : x ∈ D.M) (hx5 : orderOf x = 5) (hxUu : x * u * x⁻¹ = u)
    (hlu : l * u * l⁻¹ = (v₁ : G)) (hlL : l ∈ L)
    (hLbar_normal : ((barSub (⊥ : Subgroup G) V hV L).subgroupOf
      (Mbar D.M (⊥ : Subgroup G) V hV)).Normal)
    (h5notdvd : ¬ 5 ∣ (barSub (⊥ : Subgroup G) V hV L).relIndex
      (Mbar D.M (⊥ : Subgroup G) V hV))
    (hcent₁ : Nat.card ↥(centBarLB (⊥ : Subgroup G) V L hV v₁) = 2 ^ 7 * 3) : False := by
  classical
  have hu_eq : u = l⁻¹ * (v₁ : G) * l := by
    rw [← hlu]; group
  set φ : MulAut (Vtil (⊥ : Subgroup G) V hV) :=
    actTil (⊥ : Subgroup G) V hV ⟨x, hMs hxM⟩ with hφdef
  have hφ1 : φ ≠ 1 := by
    intro h
    exact hxV (by
      rw [hφdef] at h
      exact (TwelveTwentyThree.actTil_bot_eq_one_iff V hV _).1 h)
  have hφM : φ ∈ Mbar D.M (⊥ : Subgroup G) V hV := by
    rw [hφdef]
    exact actTil_mem_barSub (⊥ : Subgroup G) V hV hxM (hMs hxM)
  have hφord : orderOf φ = 5 := by
    have hdvd : orderOf φ ∣ 5 := by
      have hx5' : x ^ 5 = 1 := by rw [← hx5, pow_orderOf_eq_one]
      have hφ5 : φ ^ 5 = 1 := by
        have h1 : (⟨x, hMs hxM⟩ : stabTil (⊥ : Subgroup G) V) ^ 5 = 1 :=
          Subtype.ext (by simpa using hx5')
        rw [hφdef, ← map_pow, h1, map_one]
      exact orderOf_dvd_of_pow_eq_one hφ5
    rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h1 | h5
    · exact absurd (orderOf_eq_one_iff.mp h1) hφ1
    · exact h5
  have hφL : φ ∈ barSub (⊥ : Subgroup G) V hV L :=
    mem_barSub_of_order_five (D := D) hV (hN := hLbar_normal) hφM hφord hφ1 h5notdvd
  let lbar : MulAut (Vtil (⊥ : Subgroup G) V hV) :=
    actTil (⊥ : Subgroup G) V hV ⟨l, hMs (hLM hlL)⟩
  have hlbar_mem : lbar ∈ barSub (⊥ : Subgroup G) V hV L :=
    actTil_mem_barSub (⊥ : Subgroup G) V hV hlL (hMs (hLM hlL))
  have hybar_mem : lbar * φ * lbar⁻¹ ∈ barSub (⊥ : Subgroup G) V hV L :=
    (barSub (⊥ : Subgroup G) V hV L).mul_mem
      ((barSub (⊥ : Subgroup G) V hV L).mul_mem hlbar_mem hφL)
      ((barSub (⊥ : Subgroup G) V hV L).inv_mem hlbar_mem)
  have hybar_fix : (lbar * φ * lbar⁻¹)
      (mkTil (⊥ : Subgroup G) V hV (IntMod.mk hV v₁)) =
      mkTil (⊥ : Subgroup G) V hV (IntMod.mk hV v₁) := by
    have hconj : lbar * φ * lbar⁻¹ =
        actTil (⊥ : Subgroup G) V hV ⟨l * x * l⁻¹,
          hMs (D.M.mul_mem (D.M.mul_mem (hLM hlL) hxM) (D.M.inv_mem (hLM hlL)))⟩ := by
      rw [hφdef]
      have hsub : (⟨l * x * l⁻¹,
          hMs (D.M.mul_mem (D.M.mul_mem (hLM hlL) hxM) (D.M.inv_mem (hLM hlL)))⟩ :
          stabTil (⊥ : Subgroup G) V) =
          (⟨l, hMs (hLM hlL)⟩ : stabTil (⊥ : Subgroup G) V) *
            (⟨x, hMs hxM⟩ : stabTil (⊥ : Subgroup G) V) *
            (⟨l, hMs (hLM hlL)⟩ : stabTil (⊥ : Subgroup G) V)⁻¹ := Subtype.ext (by simp)
      rw [hsub, map_mul, map_mul, map_inv]
    rw [hconj, actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot]
    change (l * x * l⁻¹) * (v₁ : G) * (l * x * l⁻¹)⁻¹ * (v₁ : G)⁻¹ = 1
    have hfix : (l * x * l⁻¹) * (v₁ : G) * (l * x * l⁻¹)⁻¹ = (v₁ : G) := by
      calc (l * x * l⁻¹) * v₁ * (l * x * l⁻¹)⁻¹
          = l * (x * (l⁻¹ * v₁ * l) * x⁻¹) * l⁻¹ := by group
        _ = l * (x * u * x⁻¹) * l⁻¹ := by rw [← hu_eq]
        _ = l * u * l⁻¹ := by rw [hxUu]
        _ = (v₁ : G) := hlu
    rw [hfix]
    group
  have hybar_cent : lbar * φ * lbar⁻¹ ∈ centBarLB (⊥ : Subgroup G) V L hV v₁ := by
    refine Subgroup.mem_inf.2 ⟨?_, hybar_mem⟩
    rw [MulAction.mem_stabilizer_iff]
    exact hybar_fix
  have hord_ybar : orderOf (lbar * φ * lbar⁻¹) = 5 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj lbar) φ
    rw [hφord] at h
    simpa [MulAut.conj_apply] using h
  have h5dvd : 5 ∣ Nat.card ↥(centBarLB (⊥ : Subgroup G) V L hV v₁) := by
    have h := (centBarLB (⊥ : Subgroup G) V L hV v₁).orderOf_dvd_natCard hybar_cent
    rwa [hord_ybar] at h
  rw [hcent₁] at h5dvd
  norm_num at h5dvd

theorem fiveElement_mem_centralizer_of_minimizer (D : Data G) {V L U : Subgroup G}
    (c : Ctx17_29 D ⊥ V L)
    (h291 : R17_29_1At D ⊥ V) (h20 : R17_20At D ⊥ V) (h23 : R17_23At D ⊥ V)
    (h25 : R17_25At D ⊥ V)
    (hK : K_HJData)
    (hUV : U ≤ V) (hCU : ¬ Subgroup.centralizer (U : Set G) ≤ D.M)
    (hrU : (E3.mQuot V U : ℕ∞) = rMV D.M V) (hr6 : rMV D.M V < 6)
    {x : G} (hxM : x ∈ D.M) (hxU : x ∈ Subgroup.centralizer (U : Set G))
    (hx5 : orderOf x = 5) :
    x ∈ Subgroup.centralizer (V : Set G) := by
  classical
  by_contra hxV
  have hV : IsElemAbelian 2 V := c.ctx.hyp125.isElemAbelian
  have hM : D.M ≤ Subgroup.normalizer (V : Set G) := c.ctx.hyp125.pairFacts.le_normalizer
  have hMs : D.M ≤ stabTil (⊥ : Subgroup G) V :=
    le_stabTil hM (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hLM : L ≤ D.M := CFSG.Open.IsSubnormal.le c.ctx.mem_calC.1
  have hN : (L.subgroupOf D.M).Normal := (h20 L c.ctx).2.1
  obtain ⟨v₁, v₂, hP⟩ := h291 L c
  have hCv₂ : Subgroup.centralizer ({(v₂ : G)} : Set G) ≤ D.M := hP.2.2.2.2.2.2.2.2.2
  have hcent₁ : Nat.card ↥(centBarLB (⊥ : Subgroup G) V L hV v₁) = 2 ^ 7 * 3 :=
    hP.2.2.2.2.2.2.1
  have hW2 := s15_Infra_vtil_sq_eq_one (⊥ : Subgroup G) V hV
  have hirr : IsIrrOn (barSub (⊥ : Subgroup G) V hV L) ⊤ ⊥ := (h25 L c.ctx).1
  have h12 : rk (Vtil (⊥ : Subgroup G) V hV) = 12 := (h25 L c.ctx).2.1
  have hLbar1 : barSub (⊥ : Subgroup G) V hV L ≠ ⊥ :=
    barSub_ne_bot_of_isIrrOn hV hirr h12
  have hLbar_normal : ((barSub (⊥ : Subgroup G) V hV L).subgroupOf
      (Mbar D.M (⊥ : Subgroup G) V hV)).Normal :=
    PartTwo.barSub_subgroupOf_mbar_normal hV hLM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hN)
  have h2 : barSub (⊥ : Subgroup G) V hV (pCoreOf 2 L) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV c.ctx.mem_calC.1
      (PartTwo.barSub_pCoreOf_eq_bot_of_hyp125 c.ctx.hyp125)
  have hspBar : IsSpor ↥(barSub (⊥ : Subgroup G) V hV L) .J2 :=
    isSpor_barSub_of_isSpor_bar2_of_pcore hV (hLM.trans hMs) h2 hLbar1 (h23 L c.ctx)
  have hLbar_le : barSub (⊥ : Subgroup G) V hV L ≤ Mbar D.M (⊥ : Subgroup G) V hV :=
    barSub_mono (⊥ : Subgroup G) V hV hLM
  obtain ⟨hdvd, -, -⟩ := hK (Vtil (⊥ : Subgroup G) V hV) hW2 h12
    (Mbar D.M (⊥ : Subgroup G) V hV) (barSub (⊥ : Subgroup G) V hV L)
    hLbar_le hLbar_normal hspBar hirr
  have hrel_dvd : (barSub (⊥ : Subgroup G) V hV L).relIndex
      (Mbar D.M (⊥ : Subgroup G) V hV) ∣ 6 := by
    have hLbar_le : barSub (⊥ : Subgroup G) V hV L ≤ Mbar D.M (⊥ : Subgroup G) V hV :=
      barSub_mono (⊥ : Subgroup G) V hV hLM
    have h1 : (barSub (⊥ : Subgroup G) V hV L).relIndex
        (Mbar D.M (⊥ : Subgroup G) V hV) * Nat.card (barSub (⊥ : Subgroup G) V hV L) =
        Nat.card (Mbar D.M (⊥ : Subgroup G) V hV) := by
      have h := Subgroup.relIndex_mul_card (barSub (⊥ : Subgroup G) V hV L)
        (Mbar D.M (⊥ : Subgroup G) V hV)
      rwa [inf_eq_left.mpr hLbar_le] at h
    have h2 : (barSub (⊥ : Subgroup G) V hV L).relIndex
        (Mbar D.M (⊥ : Subgroup G) V hV) * Nat.card (barSub (⊥ : Subgroup G) V hV L) ∣
        6 * Nat.card (barSub (⊥ : Subgroup G) V hV L) := by
      rw [h1]; exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_right
      (Nat.card_pos (α := ↥(barSub (⊥ : Subgroup G) V hV L))) h2
  have h5notdvd : ¬ 5 ∣ (barSub (⊥ : Subgroup G) V hV L).relIndex
      (Mbar D.M (⊥ : Subgroup G) V hV) := by
    intro h5
    have h56 : 5 ∣ 6 := h5.trans hrel_dvd
    norm_num at h56
  have hrU6 : E3.mQuot V U < 6 := by
    have h : (E3.mQuot V U : ℕ∞) < 6 := by rw [hrU]; exact hr6
    exact_mod_cast h
  have hUbot : U ≠ ⊥ := by
    intro hbot
    have h6 : (6 : ℕ) ≤ E3.mQuot V (⊥ : Subgroup G) := by
      have h := six_le_mQuot_bot D h25 c
      exact_mod_cast h
    rw [hbot] at hrU6
    exact absurd hrU6 (not_lt.2 h6)
  obtain ⟨⟨u, huU⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hUbot
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have huV : u ∈ V := hUV huU
  have hxUu : x * u * x⁻¹ = u := by
    have h1 := (Subgroup.mem_centralizer_iff.1 hxU) u huU
    rw [← h1]
    group
  rcases hP.2.2.2.2.1 ⟨u, huV⟩ (by simpa using hu1') with ⟨l, hlL, hlu⟩ | ⟨l, hlL, hlu⟩
  · exact false_of_conj_v1_five hV hMs hLM hxV hxM hx5 hxUu hlu hlL hLbar_normal h5notdvd hcent₁
  ·
    have hu_eq : u = l⁻¹ * (v₂ : G) * l := by
      rw [← hlu]; group
    have hcent : Subgroup.centralizer ({(u : G)} : Set G) =
        conjSubgroup (Subgroup.centralizer ({(v₂ : G)} : Set G)) l := by
      rw [CFSG.LocalAnalysis.WeakClosure81.conjSubgroup_centralizer_singleton (v₂ : G) l, hu_eq]
    have hCu : Subgroup.centralizer ({(u : G)} : Set G) ≤ D.M := by
      rw [hcent]
      refine (CFSG.Quasithin.E3.conjSubgroup_mono_left l hCv₂).trans ?_
      rw [conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer (hLM hlL))]
    exact hCU ((Subgroup.centralizer_le (Set.singleton_subset_iff.2 huU)).trans hCu)

theorem mem_gammaEleven_of_minimizer (D : Data G) {V L U : Subgroup G}
    (c : Ctx17_29 D ⊥ V L)
    (h291 : R17_29_1At D ⊥ V) (h292 : R17_29_2At D ⊥ V) (h25 : R17_25At D ⊥ V)
    (hUV : U ≤ V) (hCU : ¬ Subgroup.centralizer (U : Set G) ≤ D.M)
    (hrU : (E3.mQuot V U : ℕ∞) = rMV D.M V) (hr6 : rMV D.M V < 6) :
    U ∈ gammaEleven D.M V := by
  have hrU6 : E3.mQuot V U < 6 := by
    have h : (E3.mQuot V U : ℕ∞) < 6 := by rw [hrU]; exact hr6
    exact_mod_cast h
  have hUbot : U ≠ ⊥ := by
    intro hbot
    have h6 : (6 : ℕ) ≤ E3.mQuot V (⊥ : Subgroup G) := by
      have h := six_le_mQuot_bot D h25 c
      exact_mod_cast h
    rw [hbot] at hrU6
    exact absurd hrU6 (not_lt.2 h6)
  refine ⟨hUV, hUbot, hCU, ?_⟩
  rw [Opp, CFSG.RankThree.PartOne.pElementSubgroup, Subgroup.closure_le]
  rintro x ⟨hxX, k, hk⟩
  exact twoElement_mem_centralizer_of_minimizer D c h291 h292 h25 hUV hCU hrU hr6
    (Subgroup.mem_inf.1 hxX).1 (Subgroup.mem_inf.1 hxX).2 ⟨k, hk⟩

theorem exists_cartan_of_minimizer (D : Data G)
    {V L U : Subgroup G} (c : Ctx17_29 D ⊥ V L)
    (h291 : R17_29_1At D ⊥ V) (h292 : R17_29_2At D ⊥ V) (h25 : R17_25At D ⊥ V)
    (hUV : U ≤ V) (hCU : ¬ Subgroup.centralizer (U : Set G) ≤ D.M)
    (hrU : (E3.mQuot V U : ℕ∞) = rMV D.M V) (hr6 : rMV D.M V < 6) :
    ∃ (n : ℕ) (X : Subgroup G), 1 < n ∧ n < 6 ∧ rMV D.M V = (n : ℕ∞) ∧
      IsCyclic ↥X ∧ Nat.card X = 2 ^ n - 1 ∧
      X ≤ D.M ⊓ Subgroup.centralizer (U : Set G) ∧
      V ⊓ Subgroup.centralizer (X : Set G) = U ∧
      ActsRegularlyOn X (nonIdentity ⁅V, X⁆) := by
  classical
  have hV : IsElemAbelian 2 V := c.ctx.hyp125.isElemAbelian
  have hset : Setting11 D.M V (D.T ⊓ Subgroup.centralizer (V : Set G)) :=
    setting11_of_hyp125 D c.ctx.hyp125 rfl
  have hm4 : mBar D.M (⊥ : Subgroup G) V hV = 4 := (h25 L c.ctx).2.2.1
  have hm : 1 < mBar D.M (⊥ : Subgroup G) V hset.isElemAbelian := by
    have hEq : hset.isElemAbelian = hV := Subsingleton.elim _ _
    rw [hEq, hm4]; norm_num
  have hr : 1 < rMV D.M V :=
    one_lt_rMV_of_mBar_eq_four hset (by
      have hEq : hset.isElemAbelian = hV := Subsingleton.elim _ _
      rw [hEq]; exact hm4)
  have hKproper : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G :=
    (CFSG.Assembly.kProper_inCatalog_iff_isKProper G).2 D.standing.kProper
  have hUΓ : U ∈ gammaEleven D.M V :=
    mem_gammaEleven_of_minimizer D c h291 h292 h25 hUV hCU hrU hr6
  have hUΔ : U ∈ deltaEleven D.M V := ⟨hUΓ, hrU⟩
  obtain ⟨K, hK⟩ := exists_mem_elevenBlocks (Q := D.T ⊓ Subgroup.centralizer (V : Set G))
    hset hKproper hUΓ
  obtain ⟨T, Y', hY', hmap, hKM⟩ := hK
  have hKblock : CFSG.CGT.PushingUp.IsBlockOfInX (Subgroup.centralizer (U : Set G)) K :=
    isBlockOfInX_of_mem_elevenBlocks ⟨T, Y', hY', hmap, hKM⟩
  obtain ⟨n, hn, hnat, hrMV, hCVK, huniq, hrel, ⟨X, hXhall⟩, hXstruct⟩ :=
    eleven_ten_of_one_lt hset hr hm hUΔ hKblock hKM
  refine ⟨n, X, hn, ?_, hrMV, (hXstruct X hXhall).1, (hXstruct X hXhall).2.1, ?_, ?_, ?_⟩
  · rw [hrMV] at hr6
    exact_mod_cast hr6
  ·
    refine le_inf (hXhall.1.trans inf_le_right) ?_
    exact (hXhall.1.trans inf_le_left).trans hKblock.1
  ·
    exact (hXstruct X hXhall).2.2.1
  ·
    exact (hXstruct X hXhall).2.2.2

private theorem cartan_kdata (D : Data G)
    {V L U X : Subgroup G} (hV : IsElemAbelian 2 V) (c : Ctx17_29 D ⊥ V L)
    (h20 : R17_20At D ⊥ V) (h23 : R17_23At D ⊥ V) (h25 : R17_25At D ⊥ V)
    (hK : K_HJData)
    (hXMU : X ≤ D.M ⊓ Subgroup.centralizer (U : Set G)) :
    (∀ x : MulAut (Vtil (⊥ : Subgroup G) V hV), x ∈ Mbar D.M (⊥ : Subgroup G) V hV →
      orderOf x = 3 → 4 ≤ rk (commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV))
        (Subgroup.zpowers x))) ∧
    (∀ x : MulAut (Vtil (⊥ : Subgroup G) V hV), x ∈ Mbar D.M (⊥ : Subgroup G) V hV →
      orderOf x = 7 → fixV (Subgroup.zpowers x) = ⊥) ∧
    (Nat.card (Mbar D.M (⊥ : Subgroup G) V hV) ∣ 6 * 604800) := by
  classical
  have hM : D.M ≤ Subgroup.normalizer (V : Set G) := c.ctx.hyp125.pairFacts.le_normalizer
  have hMs : D.M ≤ stabTil (⊥ : Subgroup G) V :=
    le_stabTil hM (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hLM : L ≤ D.M := CFSG.Open.IsSubnormal.le c.ctx.mem_calC.1
  have hirr : IsIrrOn (barSub (⊥ : Subgroup G) V hV L) ⊤ ⊥ := (h25 L c.ctx).1
  have h12 : rk (Vtil (⊥ : Subgroup G) V hV) = 12 := (h25 L c.ctx).2.1
  have hLbar1 : barSub (⊥ : Subgroup G) V hV L ≠ ⊥ :=
    barSub_ne_bot_of_isIrrOn hV hirr h12
  have hLbar_normal : ((barSub (⊥ : Subgroup G) V hV L).subgroupOf
      (Mbar D.M (⊥ : Subgroup G) V hV)).Normal :=
    PartTwo.barSub_subgroupOf_mbar_normal hV hLM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 (h20 L c.ctx).2.1)
  have h2 : barSub (⊥ : Subgroup G) V hV (pCoreOf 2 L) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV c.ctx.mem_calC.1
      (PartTwo.barSub_pCoreOf_eq_bot_of_hyp125 c.ctx.hyp125)
  have hspBar : IsSpor ↥(barSub (⊥ : Subgroup G) V hV L) .J2 :=
    isSpor_barSub_of_isSpor_bar2_of_pcore hV (hLM.trans hMs) h2 hLbar1 (h23 L c.ctx)
  have hW2 := s15_Infra_vtil_sq_eq_one (⊥ : Subgroup G) V hV
  have hLbar_le : barSub (⊥ : Subgroup G) V hV L ≤ Mbar D.M (⊥ : Subgroup G) V hV :=
    barSub_mono (⊥ : Subgroup G) V hV hLM
  obtain ⟨hdvd0, h7, h3⟩ := hK (Vtil (⊥ : Subgroup G) V hV) hW2 h12
    (Mbar D.M (⊥ : Subgroup G) V hV) (barSub (⊥ : Subgroup G) V hV L)
    hLbar_le hLbar_normal hspBar hirr
  have hLbarcard : Nat.card (barSub (⊥ : Subgroup G) V hV L) = 604800 := by
    obtain ⟨e⟩ := hspBar
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J2.card_J2
  refine ⟨h3, h7, ?_⟩
  rw [hLbarcard] at hdvd0
  exact hdvd0

private theorem cartan_contradiction_two (D : Data G) {V U X : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil (⊥ : Subgroup G) V)
    (hXMU : X ≤ D.M ⊓ Subgroup.centralizer (U : Set G))
    (hCV : V ⊓ Subgroup.centralizer (X : Set G) = U)
    (hreg : ActsRegularlyOn X (nonIdentity ⁅V, X⁆)) (hcomm_ne : ⁅V, X⁆ ≠ ⊥)
    (hcyc : IsCyclic ↥X) (hXcard : Nat.card X = 3)
    (h3elem : ∀ x : MulAut (Vtil (⊥ : Subgroup G) V hV), x ∈ Mbar D.M (⊥ : Subgroup G) V hV →
      orderOf x = 3 → 4 ≤ rk (commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV))
        (Subgroup.zpowers x))) :
    False := by
  classical
  have hXM : X ≤ D.M := hXMU.trans inf_le_left
  have hXstab : X ≤ stabTil (⊥ : Subgroup G) V := hXM.trans hMs
  have hcommV : ⁅V, X⁆ ≤ V := commutator_le_of_le_stabTil hXstab
  have hXdis : X ⊓ Subgroup.centralizer (V : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_regular_action hcommV hcomm_ne hreg
  have hcardX : Nat.card (barSub (⊥ : Subgroup G) V hV X) = Nat.card X :=
    card_barSub_bot_eq hV hXstab hXdis
  obtain ⟨x, hxgen⟩ := hcyc.exists_generator
  have hxgen' : Subgroup.zpowers x = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact hxgen y
  have hxord : orderOf x = Nat.card X :=
    orderOf_eq_card_of_forall_mem_zpowers (fun y => by rw [hxgen']; exact Subgroup.mem_top y)
  have hx3 : orderOf x = 3 := by rw [hxord, hXcard]
  set xbar : MulAut (Vtil (⊥ : Subgroup G) V hV) :=
    actTil (⊥ : Subgroup G) V hV ⟨(x : G), hXstab x.2⟩ with hxb
  have hxbarM : xbar ∈ Mbar D.M (⊥ : Subgroup G) V hV :=
    actTil_mem_barSub (⊥ : Subgroup G) V hV (hXM x.2) (hMs (hXM x.2))
  have hxbarord : orderOf xbar = 3 := by
    have h1 := orderOf_actTil_bot_eq hV hXstab hXdis x
    rw [hxb]
    exact h1.trans hx3
  have hbarX : barSub (⊥ : Subgroup G) V hV X = Subgroup.zpowers xbar := by
    rw [hxb]
    convert barSub_eq_zpowers_of_gen hV hXstab hxgen' using 2
    exact congrArg (actTil (⊥ : Subgroup G) V hV) (Subtype.ext rfl)
  have hrkcomm : rk (commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV))
      (barSub (⊥ : Subgroup G) V hV X)) = rk ↥⁅V, X⁆ := by
    rw [← imgTil_commutator_eq_commSub hV hXstab]
    have hinj : Function.Injective (mkTil (⊥ : Subgroup G) V hV) :=
      (TwelveShort.mkTilEquiv V hV).injective
    have hcard : Nat.card ↥(imgTil (⊥ : Subgroup G) V hV ⁅V, X⁆) = Nat.card ↥⁅V, X⁆ := by
      have h1 : Nat.card ↥(imgTil (⊥ : Subgroup G) V hV ⁅V, X⁆) =
          Nat.card ↥(intSub V hV ⁅V, X⁆) :=
        Nat.card_congr (Subgroup.equivMapOfInjective (intSub V hV ⁅V, X⁆)
          (mkTil (⊥ : Subgroup G) V hV) hinj).symm.toEquiv
      rw [h1]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcommV).toEquiv
    unfold rk
    rw [hcard]
  have h4 := h3elem xbar hxbarM hxbarord
  rw [← hbarX] at h4
  rw [hrkcomm] at h4
  have hcard : Nat.card ↥⁅V, X⁆ = 4 := by
    rw [natCard_commutator_eq_card_add_one hreg hcomm_ne, hXcard]
  have hrk2 : rk ↥⁅V, X⁆ = 2 := by
    unfold rk
    rw [hcard, show (4 : ℕ) = 2 ^ 2 from by norm_num, padicValNat.prime_pow]
  rw [hrk2] at h4
  omega

private theorem cartan_contradiction_three (D : Data G) {V U X : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil (⊥ : Subgroup G) V)
    (hXMU : X ≤ D.M ⊓ Subgroup.centralizer (U : Set G))
    (hCV : V ⊓ Subgroup.centralizer (X : Set G) = U)
    (hreg : ActsRegularlyOn X (nonIdentity ⁅V, X⁆)) (hcomm_ne : ⁅V, X⁆ ≠ ⊥)
    (hcyc : IsCyclic ↥X) (hXcard : Nat.card X = 7) (hUbot : U ≠ ⊥)
    (h7elem : ∀ x : MulAut (Vtil (⊥ : Subgroup G) V hV), x ∈ Mbar D.M (⊥ : Subgroup G) V hV →
      orderOf x = 7 → fixV (Subgroup.zpowers x) = ⊥) :
    False := by
  classical
  have hXM : X ≤ D.M := hXMU.trans inf_le_left
  have hXU : X ≤ Subgroup.centralizer (U : Set G) := hXMU.trans inf_le_right
  have hXstab : X ≤ stabTil (⊥ : Subgroup G) V := hXM.trans hMs
  have hcommV : ⁅V, X⁆ ≤ V := commutator_le_of_le_stabTil hXstab
  have hXdis : X ⊓ Subgroup.centralizer (V : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_regular_action hcommV hcomm_ne hreg
  obtain ⟨x, hxgen⟩ := hcyc.exists_generator
  have hxgen' : Subgroup.zpowers x = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact hxgen y
  have hxord : orderOf x = Nat.card X :=
    orderOf_eq_card_of_forall_mem_zpowers (fun y => by rw [hxgen']; exact Subgroup.mem_top y)
  have hx7 : orderOf x = 7 := by rw [hxord, hXcard]
  set xbar : MulAut (Vtil (⊥ : Subgroup G) V hV) :=
    actTil (⊥ : Subgroup G) V hV ⟨(x : G), hXstab x.2⟩ with hxb
  have hxbarM : xbar ∈ Mbar D.M (⊥ : Subgroup G) V hV :=
    actTil_mem_barSub (⊥ : Subgroup G) V hV (hXM x.2) (hMs (hXM x.2))
  have hxbarord : orderOf xbar = 7 := by
    have h1 := orderOf_actTil_bot_eq hV hXstab hXdis x
    rw [hxb]
    exact h1.trans hx7
  have hfix := h7elem xbar hxbarM hxbarord
  have hUfix : imgTil (⊥ : Subgroup G) V hV U ≤ fixV (Subgroup.zpowers xbar) := by
    have hbarX : barSub (⊥ : Subgroup G) V hV X = Subgroup.zpowers xbar := by
      rw [hxb]
      convert barSub_eq_zpowers_of_gen hV hXstab hxgen' using 2
      exact congrArg (actTil (⊥ : Subgroup G) V hV) (Subtype.ext rfl)
    exact imgTil_le_fixV_actTil hV (hXstab x.2) (fun u hu => by
      have h1 := (Subgroup.mem_centralizer_iff.1 (hXU x.2)) u hu
      rw [← h1]
      group)
  have hUV : U ≤ V := hCV ▸ inf_le_left
  have hUne : imgTil (⊥ : Subgroup G) V hV U ≠ ⊥ := by
    intro hbot
    obtain ⟨⟨u, huU⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hUbot
    have hmem : mkTil (⊥ : Subgroup G) V hV (IntMod.mk hV ⟨u, hUV huU⟩) ∈
        imgTil (⊥ : Subgroup G) V hV U :=
      (mem_imgTil (⊥ : Subgroup G) V hV U _).2 ⟨IntMod.mk hV ⟨u, hUV huU⟩, huU, rfl⟩
    rw [hbot] at hmem
    have h1 : IntMod.mk hV ⟨u, hUV huU⟩ = 1 :=
      (TwelveShort.mkTilEquiv V hV).injective (Subgroup.mem_bot.1 hmem)
    have h2 : u = 1 := congrArg (fun z : IntMod V hV => z.val) h1
    exact hu1 (Subtype.ext h2)
  rw [hfix] at hUfix
  exact hUne (le_bot_iff.1 hUfix)

private theorem cartan_contradiction_four (D : Data G) {V U X : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil (⊥ : Subgroup G) V)
    (hXMU : X ≤ D.M ⊓ Subgroup.centralizer (U : Set G))
    (hCV : V ⊓ Subgroup.centralizer (X : Set G) = U)
    (hreg : ActsRegularlyOn X (nonIdentity ⁅V, X⁆)) (hcomm_ne : ⁅V, X⁆ ≠ ⊥)
    (hcyc : IsCyclic ↥X) (hXcard : Nat.card X = 15)
    (h5central : ∀ y : G, y ∈ D.M → y ∈ Subgroup.centralizer (U : Set G) →
      orderOf y = 5 → y ∈ Subgroup.centralizer (V : Set G)) :
    False := by
  classical
  have hXM : X ≤ D.M := hXMU.trans inf_le_left
  have hXU : X ≤ Subgroup.centralizer (U : Set G) := hXMU.trans inf_le_right
  have hXstab : X ≤ stabTil (⊥ : Subgroup G) V := hXM.trans hMs
  have hcommV : ⁅V, X⁆ ≤ V := commutator_le_of_le_stabTil hXstab
  obtain ⟨x, hxgen⟩ := hcyc.exists_generator
  have hxgen' : Subgroup.zpowers x = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact hxgen y
  have hxord : orderOf x = Nat.card X :=
    orderOf_eq_card_of_forall_mem_zpowers (fun y => by rw [hxgen']; exact Subgroup.mem_top y)
  have hx15 : orderOf x = 15 := by rw [hxord, hXcard]
  have hxGord : orderOf (x : G) = 15 := by
    rw [Subgroup.orderOf_coe]
    exact hx15
  have h5G : orderOf ((x : G) ^ 3) = 5 := by
    rw [orderOf_pow, hxGord]
    norm_num
  have hx3U : ((x : G) ^ 3) ∈ X := by
    rw [← SubgroupClass.coe_pow]
    exact ((x : ↥X) ^ 3).2
  have hx3C : ((x : G) ^ 3) ∈ Subgroup.centralizer (U : Set G) := hXU hx3U
  have hx3V : ((x : G) ^ 3) ∈ Subgroup.centralizer (V : Set G) :=
    h5central ((x : G) ^ 3) (hXM hx3U) hx3C h5G
  obtain ⟨⟨z, hzmem⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hcomm_ne
  have hzV : z ∈ V := hcommV hzmem
  have hzfix : ((x : G) ^ 3)⁻¹ * z * ((x : G) ^ 3) = z := by
    have h1 := (Subgroup.mem_centralizer_iff.1 hx3V) z hzV
    simp only [mul_assoc]
    rw [h1, inv_mul_cancel_left]
  have hx3one : ((x : G) ^ 3) = 1 :=
    hreg.2.2 z ⟨hzmem, fun h => hz1 (Subtype.ext h)⟩ ((x : G) ^ 3) hx3U hzfix
  rw [hx3one, orderOf_one] at h5G
  norm_num at h5G

private theorem cartan_contradiction_five (D : Data G) {V U X : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil (⊥ : Subgroup G) V)
    (hXMU : X ≤ D.M ⊓ Subgroup.centralizer (U : Set G))
    (hCV : V ⊓ Subgroup.centralizer (X : Set G) = U)
    (hreg : ActsRegularlyOn X (nonIdentity ⁅V, X⁆)) (hcomm_ne : ⁅V, X⁆ ≠ ⊥)
    (hXcard : Nat.card X = 31)
    (hdvd : Nat.card (Mbar D.M (⊥ : Subgroup G) V hV) ∣ 6 * 604800) :
    False := by
  classical
  have hXM : X ≤ D.M := hXMU.trans inf_le_left
  have hXstab : X ≤ stabTil (⊥ : Subgroup G) V := hXM.trans hMs
  have hcommV : ⁅V, X⁆ ≤ V := commutator_le_of_le_stabTil hXstab
  have hXdis : X ⊓ Subgroup.centralizer (V : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_regular_action hcommV hcomm_ne hreg
  have hcardX : Nat.card (barSub (⊥ : Subgroup G) V hV X) = Nat.card X :=
    card_barSub_bot_eq hV hXstab hXdis
  have h31card : Nat.card X = 31 := hXcard
  have h31Xbar : 31 ∣ Nat.card (barSub (⊥ : Subgroup G) V hV X) := by
    rw [hcardX, h31card]
  have hXbar_le : barSub (⊥ : Subgroup G) V hV X ≤ Mbar D.M (⊥ : Subgroup G) V hV :=
    barSub_mono (⊥ : Subgroup G) V hV hXM
  have h31Mbar : 31 ∣ Nat.card (Mbar D.M (⊥ : Subgroup G) V hV) :=
    h31Xbar.trans (Subgroup.card_dvd_of_le hXbar_le)
  have h : 31 ∣ 6 * 604800 := h31Mbar.trans hdvd
  norm_num at h

theorem rMV_eq_top_of_forall (D : Data G) {V : Subgroup G}
    (hempty : ∀ U : Subgroup G, U ≤ V → Subgroup.centralizer (U : Set G) ≤ D.M) :
    rMV D.M V = ⊤ := by
  have hS : {U : Subgroup G | U ≤ V ∧ ¬ Subgroup.centralizer (U : Set G) ≤ D.M} = ∅ := by
    ext U
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => h.2 (hempty U h.1)
  unfold rMV
  rw [hS]
  simp

theorem exists_mQuot_eq_rMV (D : Data G) {V : Subgroup G}
    (hne : ∃ U : Subgroup G, U ≤ V ∧ ¬ Subgroup.centralizer (U : Set G) ≤ D.M) :
    ∃ U : Subgroup G, U ≤ V ∧ ¬ Subgroup.centralizer (U : Set G) ≤ D.M ∧
      (E3.mQuot V U : ℕ∞) = rMV D.M V := by
  classical
  set S : Set (Subgroup G) := {U | U ≤ V ∧ ¬ Subgroup.centralizer (U : Set G) ≤ D.M} with hSdef
  obtain ⟨U, hUS, hmin⟩ :=
    Set.exists_min_image S (fun U => (E3.mQuot V U : ℕ∞)) (Set.toFinite S) hne
  refine ⟨U, hUS.1, hUS.2, ?_⟩
  unfold rMV
  refine le_antisymm ?_ ?_
  · exact le_iInf₂ fun U' hU' => hmin U' hU'
  · exact iInf₂_le U hUS

theorem seventeen_thirty (D : Data G) (V₀ V : Subgroup G)
    (hK : K_HJData) (h20 : R17_20At D V₀ V) (h23 : R17_23At D V₀ V)
    (h25 : R17_25At D V₀ V) (h291 : R17_29_1At D V₀ V) (h292 : R17_29_2At D V₀ V) :
    R17_30At D V₀ V := by
  intro L c
  have hV₀ : V₀ = ⊥ := c.v0
  subst V₀
  by_contra h6
  rw [not_le] at h6
  have hV : IsElemAbelian 2 V := c.ctx.hyp125.isElemAbelian
  have hM : D.M ≤ Subgroup.normalizer (V : Set G) := c.ctx.hyp125.pairFacts.le_normalizer
  have hMs : D.M ≤ stabTil (⊥ : Subgroup G) V :=
    le_stabTil hM (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  by_cases hne : ∃ U : Subgroup G, U ≤ V ∧ ¬ Subgroup.centralizer (U : Set G) ≤ D.M
  · obtain ⟨U, hUV, hCU, hrU⟩ := exists_mQuot_eq_rMV D hne
    obtain ⟨n, X, hn, hn6, hrn, hcyc, hXcard, hXMU, hCV, hreg⟩ :=
      exists_cartan_of_minimizer D c h291 h292 h25 hUV hCU hrU h6
    obtain ⟨h3elem, h7elem, hdvd⟩ := cartan_kdata D hV c h20 h23 h25 hK hXMU
    have hUVne : U ≠ V := by
      intro h
      rw [h, E3.mQuot_self, hrn] at hrU
      have hn0 : n = 0 := by
        have : (n : ℕ∞) = 0 := hrU.symm
        exact_mod_cast this
      omega
    have hUbot : U ≠ ⊥ := by
      intro h
      have h6' : (6 : ℕ) ≤ n := by
        have hh : (6 : ℕ∞) ≤ (E3.mQuot V (⊥ : Subgroup G) : ℕ∞) := by
          have hh0 := six_le_mQuot_bot D h25 c
          exact_mod_cast hh0
        rw [h, hrn] at hrU
        exact_mod_cast (hrU ▸ hh)
      omega
    have hcomm_ne : ⁅V, X⁆ ≠ ⊥ := by
      intro hbot
      have h1 : V ≤ Subgroup.centralizer (X : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
      have h2 : V ≤ U := by rw [← hCV]; exact le_inf le_rfl h1
      exact hUVne (le_antisymm hUV h2)
    have h5central : ∀ y : G, y ∈ D.M → y ∈ Subgroup.centralizer (U : Set G) →
        orderOf y = 5 → y ∈ Subgroup.centralizer (V : Set G) :=
      fun y hyM hyU hy5 =>
        fiveElement_mem_centralizer_of_minimizer D c h291 h20 h23 h25 hK hUV hCU hrU h6
          hyM hyU hy5
    interval_cases n
    · exact cartan_contradiction_two D hV hMs hXMU hCV hreg hcomm_ne hcyc
        (by rw [hXcard]; norm_num) h3elem
    · exact cartan_contradiction_three D hV hMs hXMU hCV hreg hcomm_ne hcyc
        (by rw [hXcard]; norm_num) hUbot h7elem
    · exact cartan_contradiction_four D hV hMs hXMU hCV hreg hcomm_ne hcyc
        (by rw [hXcard]; norm_num) h5central
    · exact cartan_contradiction_five D hV hMs hXMU hCV hreg hcomm_ne
        (by rw [hXcard]; norm_num) hdvd
  · rw [rMV_eq_top_of_forall D (fun U hU => by
      by_contra hCU
      exact hne ⟨U, hU, hCU⟩)] at h6
    exact absurd h6 (by simp)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
