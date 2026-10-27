module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19P
public import CFSG.Quasithin.Background.G6Transvection
import all CFSG.Quasithin.Background.G6Transvection
public import CFSG.Quasithin.Background.B1MoreQuot
public import CFSG.Quasithin.Background.G6Basic

public section

namespace CFSG.Quasithin.H13

namespace L619

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G]

section Module

variable {W : Subgroup G} (hW : IsElemAbelian 2 W)

@[expose] def modVal : IntMod W hW →* G where
  toFun v := IntMod.val v
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def modSub (Z : Subgroup G) : Subgroup (IntMod W hW) := Z.comap (modVal hW)

theorem mem_modSub {Z : Subgroup G} {v : IntMod W hW} : v ∈ modSub hW Z ↔ v.val ∈ Z := Iff.rfl

abbrev normWZ (W Z : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (W : Set G) ⊓ Subgroup.normalizer (Z : Set G)

@[expose] noncomputable def actW (Z : Subgroup G) : ↥(normWZ W Z) →* MulAut (IntMod W hW) :=
  (convI hW).comp (Subgroup.inclusion inf_le_left)

theorem actW_val {Z : Subgroup G} (g : ↥(normWZ W Z)) (v : IntMod W hW) :
    (actW hW Z g v).val = g * v.val * (g : G)⁻¹ :=
  convI_apply_val hW _ v

theorem actW_mem_stabSub {Z : Subgroup G} (g : ↥(normWZ W Z)) :
    actW hW Z g ∈ stabSub (modSub hW Z) := by
  intro u
  rw [mem_modSub, mem_modSub, actW_val]
  exact (Subgroup.mem_normalizer_iff.mp g.2.2 u.val).symm

@[expose] noncomputable def actQ (Z : Subgroup G) :
    ↥(normWZ W Z) →* MulAut (IntMod W hW ⧸ modSub hW Z) :=
  (quotHom (modSub hW Z)).comp ((actW hW Z).codRestrict _ (actW_mem_stabSub hW))

@[expose] def mkW (Z : Subgroup G) {w : G} (hw : w ∈ W) : IntMod W hW ⧸ modSub hW Z :=
  QuotientGroup.mk (IntMod.mk hW ⟨w, hw⟩)

theorem mkW_surjective (Z : Subgroup G) (q : IntMod W hW ⧸ modSub hW Z) :
    ∃ w : G, ∃ hw : w ∈ W, mkW hW Z hw = q := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨v.val, v.val_mem, rfl⟩

theorem mkW_eq_mkW_iff {Z : Subgroup G} {a b : G} (ha : a ∈ W) (hb : b ∈ W) :
    mkW hW Z ha = mkW hW Z hb ↔ a * b⁻¹ ∈ Z := by
  unfold mkW
  rw [mk_eq_mk_iff, mem_modSub]
  rfl

theorem mkW_mul {Z : Subgroup G} {a b : G} (ha : a ∈ W) (hb : b ∈ W) :
    mkW hW Z ha * mkW hW Z hb = mkW hW Z (W.mul_mem ha hb) := rfl

theorem mkW_inv {Z : Subgroup G} {a : G} (ha : a ∈ W) :
    (mkW hW Z ha)⁻¹ = mkW hW Z (W.inv_mem ha) := rfl

theorem actQ_mkW {Z : Subgroup G} (g : ↥(normWZ W Z)) {w : G} (hw : w ∈ W) :
    actQ hW Z g (mkW hW Z hw) =
      mkW hW Z ((Subgroup.mem_normalizer_iff.mp g.2.1 w).mp hw) := by
  show QuotientGroup.mk (actW hW Z g (IntMod.mk hW ⟨w, hw⟩)) = _
  exact congrArg _ (IntMod.val_injective (actW_val hW g _))

theorem actQ_eq_one_iff {Z : Subgroup G} (g : ↥(normWZ W Z)) :
    actQ hW Z g = 1 ↔ ∀ w ∈ W, (g : G) * w * (g : G)⁻¹ * w⁻¹ ∈ Z := by
  constructor
  · intro h1 w hw
    have := congrArg (fun φ : MulAut (IntMod W hW ⧸ modSub hW Z) => φ (mkW hW Z hw)) h1
    simp only [actQ_mkW, MulAut.one_apply] at this
    exact (mkW_eq_mkW_iff hW _ _).mp this
  · intro h1
    refine MulEquiv.ext fun q => ?_
    obtain ⟨w, hw, rfl⟩ := mkW_surjective hW Z q
    rw [actQ_mkW, MulAut.one_apply]
    exact (mkW_eq_mkW_iff hW _ _).mpr (h1 w hw)

theorem sq_eq_one_quot (Z : Subgroup G) (q : IntMod W hW ⧸ modSub hW Z) : q ^ 2 = 1 := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
  rw [← QuotientGroup.mk_pow, IntMod.sq_eq_one]
  rfl

end Module

section Restrict

variable {W : Subgroup G} (hW : IsElemAbelian 2 W) (Z X : Subgroup G)

abbrev normWZX (W Z X : Subgroup G) : Subgroup G :=
  normWZ W Z ⊓ Subgroup.normalizer (X : Set G)

@[expose] noncomputable def imgQ : Subgroup (MulAut (IntMod W hW ⧸ modSub hW Z)) :=
  (X.subgroupOf (normWZ W Z)).map (actQ hW Z)

@[expose] noncomputable def V0 : Subgroup (IntMod W hW ⧸ modSub hW Z) := commV (imgQ hW Z X)

@[expose] noncomputable def actQX : ↥(normWZX W Z X) →* MulAut (IntMod W hW ⧸ modSub hW Z) :=
  (actQ hW Z).comp (Subgroup.inclusion inf_le_left)

theorem actQX_apply (g : ↥(normWZX W Z X)) :
    actQX hW Z X g = actQ hW Z ⟨g, g.2.1⟩ := rfl

theorem actQX_mem_imgQ {g : ↥(normWZX W Z X)} (hg : (g : G) ∈ X) :
    actQX hW Z X g ∈ imgQ hW Z X :=
  ⟨⟨g, g.2.1⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩

theorem actQX_conj_mem (g : ↥(normWZX W Z X)) {k : MulAut (IntMod W hW ⧸ modSub hW Z)}
    (hk : k ∈ imgQ hW Z X) : actQX hW Z X g * k * (actQX hW Z X g)⁻¹ ∈ imgQ hW Z X := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hk
  refine Subgroup.mem_map.mpr ⟨⟨g, g.2.1⟩ * x * ⟨g, g.2.1⟩⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp g.2.2 _).mp hx
  · rw [map_mul, map_mul, map_inv]
    rfl

theorem actQX_mem_stabSub (g : ↥(normWZX W Z X)) : actQX hW Z X g ∈ stabSub (V0 hW Z X) := by
  intro u
  constructor
  · intro hu
    have h1 := G6.apply_mem_commV (X := imgQ hW Z X) (k := actQX hW Z X g⁻¹)
      (fun x hx => actQX_conj_mem hW Z X g⁻¹ hx) hu
    have h2 : actQX hW Z X g⁻¹ (actQX hW Z X g u) = u := by
      rw [map_inv, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    rwa [h2] at h1
  · intro hu
    exact G6.apply_mem_commV (fun x hx => actQX_conj_mem hW Z X g hx) hu

@[expose] noncomputable def act0 : ↥(normWZX W Z X) →* MulAut ↥(V0 hW Z X) :=
  (resHom (V0 hW Z X)).comp ((actQX hW Z X).codRestrict _ (actQX_mem_stabSub hW Z X))

theorem act0_apply (g : ↥(normWZX W Z X)) (v : ↥(V0 hW Z X)) :
    ((act0 hW Z X g v : ↥(V0 hW Z X)) : IntMod W hW ⧸ modSub hW Z) = actQX hW Z X g v := rfl

@[expose] noncomputable def img0 : Subgroup (MulAut ↥(V0 hW Z X)) :=
  (X.subgroupOf (normWZX W Z X)).map (act0 hW Z X)

theorem act0_mem_img0 {g : ↥(normWZX W Z X)} (hg : (g : G) ∈ X) : act0 hW Z X g ∈ img0 hW Z X :=
  ⟨g, Subgroup.mem_subgroupOf.mpr hg, rfl⟩

theorem actQX_sq_eq_one {g : ↥(normWZX W Z X)} (hg : (g : G) ∈ X) (h1 : act0 hW Z X g = 1) :
    actQX hW Z X (g ^ 2) = 1 := by
  refine MulEquiv.ext fun q => ?_
  set v := actQX hW Z X g q * q⁻¹ with hv
  have hvV : v ∈ V0 hW Z X := G6.mem_commV_of_mem (actQX_mem_imgQ hW Z X hg) q
  have hfix : actQX hW Z X g v = v := by
    have := congrArg (fun φ : MulAut ↥(V0 hW Z X) => ((φ ⟨v, hvV⟩ : ↥(V0 hW Z X)) :
      IntMod W hW ⧸ modSub hW Z)) h1
    simpa [act0_apply] using this
  have hq : actQX hW Z X g q = v * q := by rw [hv, inv_mul_cancel_right]
  rw [map_pow, pow_two, MulAut.mul_apply, hq, map_mul, hfix, hq, ← mul_assoc, ← pow_two,
    sq_eq_one_quot, one_mul, MulAut.one_apply]

end Restrict

section Centre

variable [Finite G] {W : Subgroup G} (hW : IsElemAbelian 2 W) (Z : Subgroup G)

@[expose] def imgSub (C : Subgroup G) : Subgroup (IntMod W hW ⧸ modSub hW Z) :=
  (modSub hW C).map (QuotientGroup.mk' (modSub hW Z))

omit [Finite G] in
theorem mkW_mem_imgSub {C : Subgroup G} {w : G} (hw : w ∈ W) (hc : w ∈ C) :
    mkW hW Z hw ∈ imgSub hW Z C :=
  ⟨IntMod.mk hW ⟨w, hw⟩, hc, rfl⟩

omit [Finite G] in
theorem card_modSub {C : Subgroup G} (hC : C ≤ W) : Nat.card (modSub hW C) = Nat.card C :=
  Nat.card_congr
    { toFun := fun v => ⟨IntMod.val v.1, v.2⟩
      invFun := fun c => ⟨IntMod.mk hW ⟨c.1, hC c.2⟩, c.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

omit [Finite G] in
theorem card_imgSub_mul {C : Subgroup G} (hC : C ≤ W) :
    Nat.card (imgSub hW Z C) * Nat.card ↥(C ⊓ Z) = Nat.card C := by
  have h := B1More.card_map_mul_card_inf_ker (modSub hW C) (QuotientGroup.mk' (modSub hW Z))
  rw [QuotientGroup.ker_mk'] at h
  have e : modSub hW C ⊓ modSub hW Z = modSub hW (C ⊓ Z) := (Subgroup.comap_inf _ _ _).symm
  rw [e, card_modSub hW (inf_le_left.trans hC), card_modSub hW hC] at h
  exact h

omit [Finite G] in
theorem actQ_mul_inv_mem_imgSub {C : Subgroup G} (g : ↥(normWZ W Z))
    (hg : ∀ w ∈ W, (g : G) * w * (g : G)⁻¹ * w⁻¹ ∈ C) (q : IntMod W hW ⧸ modSub hW Z) :
    actQ hW Z g q * q⁻¹ ∈ imgSub hW Z C := by
  obtain ⟨w, hw, rfl⟩ := mkW_surjective hW Z q
  rw [actQ_mkW, mkW_inv, mkW_mul]
  exact mkW_mem_imgSub hW Z _ (hg w hw)

variable (X : Subgroup G)

theorem card_commV_zpowers_act0 {C : Subgroup G} (hcard : Nat.card (imgSub hW Z C) = 2)
    {g : ↥(normWZX W Z X)} (hg : ∀ w ∈ W, (g : G) * w * (g : G)⁻¹ * w⁻¹ ∈ C)
    (h1 : act0 hW Z X g ≠ 1) :
    Nat.card (commV (Subgroup.zpowers (act0 hW Z X g))) = 2 := by
  set d := act0 hW Z X g with hd
  set A : Subgroup ↥(V0 hW Z X) := (imgSub hW Z C).comap (V0 hW Z X).subtype with hA
  have hle : commV (Subgroup.zpowers d) ≤ A := by
    rw [Subgroup.zpowers_eq_closure]
    refine G6.commV_closure_le fun s hs v => ?_
    rw [Set.mem_singleton_iff] at hs
    subst hs
    show ((d v * v⁻¹ : ↥(V0 hW Z X)) : IntMod W hW ⧸ modSub hW Z) ∈ imgSub hW Z C
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hd, act0_apply, actQX_apply]
    exact actQ_mul_inv_mem_imgSub hW Z ⟨g, g.2.1⟩ hg _
  have hA2 : Nat.card A ≤ 2 := by
    rw [← hcard]
    refine Nat.card_le_card_of_injective (fun a => (⟨(a : ↥(V0 hW Z X)), a.2⟩ : imgSub hW Z C))
      fun a b hab => ?_
    exact Subtype.ext (Subtype.ext
      (congrArg (fun x : ↥(imgSub hW Z C) => (x : IntMod W hW ⧸ modSub hW Z)) hab))
  have hne : commV (Subgroup.zpowers d) ≠ ⊥ := by
    intro h0
    apply h1
    refine MulEquiv.ext fun v => ?_
    have := G6.mem_commV_of_mem (Subgroup.mem_zpowers d) v
    rw [h0, Subgroup.mem_bot, mul_inv_eq_one] at this
    exact this
  have hc1 : Nat.card (commV (Subgroup.zpowers d)) ≠ 1 := fun h =>
    hne (Subgroup.eq_bot_of_card_eq _ h)
  have hc0 : 0 < Nat.card (commV (Subgroup.zpowers d)) := Nat.card_pos
  have hc2 : Nat.card (commV (Subgroup.zpowers d)) ≤ 2 := (Subgroup.card_le_of_le hle).trans hA2
  omega

end Centre

end L619

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ} {y : G}

structure Z619 (T L V H : Subgroup G) (y z : G) : Prop where
  ne_one : z ≠ 1
  eq_inf : Subgroup.zpowers z = ch6ZS T L V ⊓ conjSub y (ch6ZS T L V)
  eq_comm : ⁅V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)),
    conjSub y V ⊓ Subgroup.normalizer (V : Set G)⁆ = Subgroup.zpowers z

structure IsY619 (T L V : Subgroup G) (z : G) (Y : Subgroup G) : Prop where
  I_le : ch619I T L V ≤ Y
  le_normalizer_W0 : Y ≤ Subgroup.normalizer (conjClosure V (ch619I T L V) : Set G)
  le_normalizer_ZS : Y ≤ Subgroup.normalizer (ch6ZS T L V : Set G)
  le_centralizer_z : Y ≤ Subgroup.centralizer ({z} : Set G)

namespace Z619

variable {z : G} (hz : Z619 T L V H y z)
include hz

omit [Finite G] in
theorem mem_ZS : z ∈ ch6ZS T L V := (hz.eq_inf ▸ Subgroup.mem_zpowers z).1

end Z619

namespace IsY619

variable {z : G} {Y : Subgroup G} (hY : IsY619 T L V z Y)
include hY

omit [Finite G] in
theorem le_normalizer_I : Y ≤ Subgroup.normalizer (ch619I T L V : Set G) :=
  L619.normalizer_I_of hY.le_normalizer_ZS

theorem le_normalizer_W : Y ≤ Subgroup.normalizer (ch619W T L V z : Set G) :=
  L619.normalizer_W_of hY.le_normalizer_W0 hY.le_normalizer_ZS hY.le_centralizer_z

theorem le_normalizer_K1 : Y ≤ Subgroup.normalizer (ch619K1 T L V z : Set G) :=
  L619.normalizer_K1_of hY.le_normalizer_W0 hY.le_normalizer_ZS hY.le_centralizer_z

theorem le_normWZ : Y ≤ L619.normWZ (ch619W T L V z) (ch6ZS T L V) :=
  le_inf hY.le_normalizer_W hY.le_normalizer_ZS

end IsY619

theorem isY619_sup (h : Hyp611Nat G T M L V n) {z : G} (hzS : z ∈ ch6ZS T L V) {d : G}
    (hd : d ∈ L ⊓ Subgroup.normalizer (ch6ZS T L V : Set G))
    (hTz : conjSub d⁻¹ T ≤ Subgroup.centralizer ({z} : Set G)) :
    IsY619 T L V z (ch619I T L V ⊔ conjSub d⁻¹ T) := by
  have hTV : conjSub d⁻¹ T ≤ Subgroup.normalizer (V : Set G) := by
    have h1 := conjSub_mono d⁻¹ h.toHyp611.T_le_normalizer
    rwa [← conjSub_normalizer, conjSub_eq_of_mem_normalizer'
      (Subgroup.inv_mem _ (h.toHyp611.L_le_normalizer hd.1))] at h1
  have hTZ : conjSub d⁻¹ T ≤ Subgroup.normalizer (ch6ZS T L V : Set G) := by
    have h1 := conjSub_mono d⁻¹ h.T_le_normalizer_ZS
    rwa [← conjSub_normalizer, conjSub_eq_of_mem_normalizer' (Subgroup.inv_mem _ hd.2)] at h1
  have hTI : conjSub d⁻¹ T ≤ Subgroup.normalizer (ch619I T L V : Set G) :=
    L619.normalizer_I_of hTZ
  refine ⟨le_sup_left, sup_le (le_normalizer_conjClosure _ _) fun t ht =>
      L619.mem_normalizer_conjClosure (hTV ht) (hTI ht),
    sup_le (Subgroup.centralizer_le_normalizer _) hTZ,
    sup_le (L619.centralizer_le_centralizer_singleton hzS) hTz⟩

namespace Cfg619

variable (h : Hyp6116 G T M L V n)
include h

theorem isElemAbelian_W (hab : IsMulCommutative ↥(conjClosure V (ch619I T L V))) (z : G) :
    IsElemAbelian 2 (ch619W T L V z) :=
  B2F.isElemAbelian_mono inf_le_left
    (L619.isElemAbelian_conjClosure h.toHyp611.isElemAbelian hab)

variable {H : Subgroup G} (c : Cfg619 T L V H n y)
include c

omit [Finite G] h in
theorem conjClosure_E_le_I {z : G} {Y : Subgroup G} (hY : IsY619 T L V z Y) :
    conjClosure (conjSub y V) Y ≤ ch619I T L V :=
  CFSG.Quasithin.conjClosure_le fun _ hg e he =>
    (Subgroup.mem_normalizer_iff.mp (hY.le_normalizer_I hg) e).mp (c.le_centralizer he)

omit h in
theorem conjClosure_E_le_normWZX {z : G} {Y : Subgroup G} (hY : IsY619 T L V z Y) :
    conjClosure (conjSub y V) Y ≤
      L619.normWZX (ch619W T L V z) (ch6ZS T L V) (conjClosure (conjSub y V) Y) :=
  le_inf ((c.conjClosure_E_le_I hY).trans (hY.I_le.trans hY.le_normWZ)) Subgroup.le_normalizer

omit h c in
theorem Y_le_normWZX {z : G} {Y : Subgroup G} (hY : IsY619 T L V z Y) :
    Y ≤ L619.normWZX (ch619W T L V z) (ch6ZS T L V) (conjClosure (conjSub y V) Y) :=
  le_inf hY.le_normWZ (le_normalizer_conjClosure _ _)

theorem act0_eq_one_iff (h432 : Stmt4_3_2) {z : G} (hz : Z619 T L V H y z) {Y : Subgroup G}
    (hY : IsY619 T L V z Y) (hW : IsElemAbelian 2 (ch619W T L V z))
    {x : ↥(L619.normWZX (ch619W T L V z) (ch6ZS T L V) (conjClosure (conjSub y V) Y))}
    (hx : (x : G) ∈ conjClosure (conjSub y V) Y) :
    L619.act0 hW (ch6ZS T L V) (conjClosure (conjSub y V) Y) x = 1 ↔
      (x : G) ∈ ch619K2 T L V z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxN⟩ := x
  change x ∈ conjClosure (conjSub y V) Y at hx
  change _ = 1 ↔ x ∈ ch619K2 T L V z
  set X := conjClosure (conjSub y V) Y with hX
  set N := L619.normWZX (ch619W T L V z) (ch6ZS T L V) X with hN
  have hXI : X ≤ ch619I T L V := c.conjClosure_E_le_I hY
  have hXN : X ≤ N := c.conjClosure_E_le_normWZX hY
  have hIX : ch619I T L V ≤ Subgroup.normalizer (X : Set G) :=
    hY.I_le.trans (le_normalizer_conjClosure _ _)
  have hIZ : ch619I T L V ≤ Subgroup.normalizer (ch6ZS T L V : Set G) :=
    Subgroup.centralizer_le_normalizer _
  constructor
  · intro h1
    let R : Subgroup G := ((L619.act0 hW (ch6ZS T L V) X).ker.map N.subtype) ⊓ X
    have hRX : R ≤ X := inf_le_right
    have hXR : X ≤ Subgroup.normalizer (R : Set G) := by
      intro g hg
      refine mem_normalizer_of_forall_conj_mem_of_le fun r hr => ?_
      obtain ⟨⟨r', hr', hrr⟩, hrX⟩ := hr
      refine ⟨⟨⟨g, hXN hg⟩ * r' * ⟨g, hXN hg⟩⁻¹, ?_, ?_⟩,
        X.mul_mem (X.mul_mem hg hrX) (X.inv_mem hg)⟩
      · rw [SetLike.mem_coe, MonoidHom.mem_ker] at hr' ⊢
        rw [map_mul, map_mul, map_inv, hr', mul_one, mul_inv_cancel]
      · rw [← hrr]
        rfl
    have h2 : ∀ r ∈ R, ∃ m : ℕ, r ^ 2 ^ m ∈ ch619K2 T L V z := by
      rintro r ⟨⟨r', hr', rfl⟩, hrX⟩
      refine ⟨1, ?_⟩
      have hsq := L619.actQX_sq_eq_one hW (ch6ZS T L V) X hrX (MonoidHom.mem_ker.mp hr')
      rw [L619.actQX_apply, L619.actQ_eq_one_iff] at hsq
      have hrI : (r' : G) ^ 2 ^ 1 ∈ ch619I T L V := (ch619I T L V).pow_mem (hXI hrX) _
      exact ⟨hrI, hIZ hrI, fun w hw => by simpa using hsq w hw⟩
    have hXK1 := c.commutator_conjClosure_K1_mem h hz.ne_one hz.eq_inf hz.eq_comm
      hY.le_normalizer_I hY.le_normalizer_K1
    have hR := le_K2_of_normal_of h h432 hz.mem_ZS hXI hIX hXK1 hRX hXR h2
    exact hR ⟨⟨⟨x, hxN⟩, h1, rfl⟩, hx⟩
  · intro hK
    have hQ : L619.actQ hW (ch6ZS T L V) ⟨x, hxN.1⟩ = 1 :=
      (L619.actQ_eq_one_iff hW _).mpr hK.2.2
    refine MulEquiv.ext fun v => Subtype.ext ?_
    rw [L619.act0_apply, L619.actQX_apply, hQ]
    rfl

theorem pCoreOf_img0_eq_bot (h432 : Stmt4_3_2) {z : G} (hz : Z619 T L V H y z)
    {Y : Subgroup G} (hY : IsY619 T L V z Y) (hW : IsElemAbelian 2 (ch619W T L V z)) :
    pCoreOf 2 (L619.img0 hW (ch6ZS T L V) (conjClosure (conjSub y V) Y)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := conjClosure (conjSub y V) Y with hX
  set N := L619.normWZX (ch619W T L V z) (ch6ZS T L V) X with hN
  set K := L619.img0 hW (ch6ZS T L V) X with hK
  set O := pCoreOf 2 K with hO
  have hXI : X ≤ ch619I T L V := c.conjClosure_E_le_I hY
  have hXN : X ≤ N := c.conjClosure_E_le_normWZX hY
  have hIX : ch619I T L V ≤ Subgroup.normalizer (X : Set G) :=
    hY.I_le.trans (le_normalizer_conjClosure _ _)
  have hKO : K ≤ Subgroup.normalizer (O : Set (MulAut ↥(L619.V0 hW (ch6ZS T L V) X))) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  let R : Subgroup G := ((O.comap (L619.act0 hW (ch6ZS T L V) X)).map N.subtype) ⊓ X
  have hRX : R ≤ X := inf_le_right
  have hXR : X ≤ Subgroup.normalizer (R : Set G) := by
    intro g hg
    refine mem_normalizer_of_forall_conj_mem_of_le fun r hr => ?_
    obtain ⟨⟨r', hr', hrr⟩, hrX⟩ := hr
    refine ⟨⟨⟨g, hXN hg⟩ * r' * ⟨g, hXN hg⟩⁻¹, ?_, ?_⟩,
      X.mul_mem (X.mul_mem hg hrX) (X.inv_mem hg)⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap] at hr' ⊢
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp
        (hKO (L619.act0_mem_img0 hW (ch6ZS T L V) X (g := ⟨g, hXN hg⟩) hg)) _).mp hr'
    · rw [← hrr]
      rfl
  have h2 : ∀ r ∈ R, ∃ m : ℕ, r ^ 2 ^ m ∈ ch619K2 T L V z := by
    rintro r ⟨⟨r', hr', rfl⟩, hrX⟩
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K))
      ⟨_, hr'⟩
    refine ⟨m, ?_⟩
    have h1 : L619.act0 hW (ch6ZS T L V) X (r' ^ 2 ^ m) = 1 := by
      rw [map_pow]
      have := pow_orderOf_eq_one (⟨_, hr'⟩ : ↥O)
      rw [hm] at this
      exact congrArg Subtype.val this
    have hmem : ((r' ^ 2 ^ m : ↥N) : G) ∈ X := X.pow_mem hrX _
    have := (c.act0_eq_one_iff h h432 hz hY hW hmem).mp h1
    simpa using this
  have hXK1 := c.commutator_conjClosure_K1_mem h hz.ne_one hz.eq_inf hz.eq_comm
    hY.le_normalizer_I hY.le_normalizer_K1
  have hR := le_K2_of_normal_of h h432 hz.mem_ZS hXI hIX hXK1 hRX hXR h2
  rw [eq_bot_iff]
  intro o ho
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp (CFSG.LieType.BorelTits.pCoreOf_le 2 K ho)
  rw [Subgroup.mem_subgroupOf] at hx
  have hxR : (x : G) ∈ R := ⟨⟨x, ho, rfl⟩, hx⟩
  exact (Subgroup.mem_bot).mpr ((c.act0_eq_one_iff h h432 hz hY hW hx).mpr (hR hxR))

theorem card_imgSub_conj_ZE {z : G} (hz : Z619 T L V H y z) {Y : Subgroup G}
    (hY : IsY619 T L V z Y) (hW : IsElemAbelian 2 (ch619W T L V z)) {g : G} (hg : g ∈ Y) :
    Nat.card (L619.imgSub hW (ch6ZS T L V) (conjSub g (conjSub y (ch6ZS T L V)))) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCW := c.conj_ZE_le_W h hz.ne_one hz.eq_inf hz.eq_comm (hY.le_normalizer_W hg)
  have h1 := L619.card_imgSub_mul hW (ch6ZS T L V) hCW
  have hC : Nat.card (conjSub g (conjSub y (ch6ZS T L V))) = 4 := by
    rw [card_conjSub', card_conjSub', h.toHyp611Nat.card_ZS, c.n_eq]
    norm_num
  have hinf := conj_ZE_inf_ZS hz.eq_inf (hY.le_normalizer_ZS hg) (hY.le_centralizer_z hg)
  have hz2 : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    have hzS := hz.mem_ZS
    have hsq : z ^ 2 = 1 := h.toHyp611.isElemAbelian.2 z hzS.1
    exact orderOf_eq_prime hsq hz.ne_one
  rw [hinf, hz2, hC] at h1
  omega

omit h c in
@[expose] def transv619 {z : G} (hW : IsElemAbelian 2 (ch619W T L V z)) (y : G) (Y : Subgroup G) :
    Set (MulAut ↥(L619.V0 hW (ch6ZS T L V) (conjClosure (conjSub y V) Y))) :=
  {d | ∃ g ∈ Y, ∃ e ∈ conjSub y V, ∃ hx : g * e * g⁻¹ ∈
      L619.normWZX (ch619W T L V z) (ch6ZS T L V) (conjClosure (conjSub y V) Y),
    d = L619.act0 hW (ch6ZS T L V) (conjClosure (conjSub y V) Y) ⟨g * e * g⁻¹, hx⟩ ∧ d ≠ 1}

omit h in
theorem closure_transv619 {z : G} {Y : Subgroup G} (hY : IsY619 T L V z Y)
    (hW : IsElemAbelian 2 (ch619W T L V z)) :
    Subgroup.closure (transv619 hW y Y) =
      L619.img0 hW (ch6ZS T L V) (conjClosure (conjSub y V) Y) := by
  set X := conjClosure (conjSub y V) Y with hX
  set N := L619.normWZX (ch619W T L V z) (ch6ZS T L V) X with hN
  have hXN : X ≤ N := c.conjClosure_E_le_normWZX hY
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro d ⟨g, hg, e, he, hx, rfl, -⟩
    exact L619.act0_mem_img0 hW _ X (CFSG.Quasithin.mem_conjClosure hg he)
  · intro k hk
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hk
    rw [Subgroup.mem_subgroupOf] at hx
    have hXle : X ≤ ((Subgroup.closure (transv619 hW y Y)).comap
        (L619.act0 hW (ch6ZS T L V) X)).map N.subtype := by
      refine CFSG.Quasithin.conjClosure_le fun g hg e he => ?_
      have hxN : g * e * g⁻¹ ∈ N := hXN (CFSG.Quasithin.mem_conjClosure hg he)
      refine ⟨⟨g * e * g⁻¹, hxN⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      by_cases h1 : L619.act0 hW (ch6ZS T L V) X ⟨g * e * g⁻¹, hxN⟩ = 1
      · rw [h1]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨g, hg, e, he, hxN, rfl, h1⟩
    obtain ⟨x', hx', hxx⟩ := hXle hx
    have : x' = x := Subtype.ext hxx
    rw [← this]
    exact hx'

theorem commV_img0_eq_top (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10)
    (hab : IsMulCommutative ↥(conjClosure V (ch619I T L V))) {z : G} (hz : Z619 T L V H y z)
    {Y : Subgroup G} (hY : IsY619 T L V z Y) (hW : IsElemAbelian 2 (ch619W T L V z)) :
    commV (L619.img0 hW (ch6ZS T L V) (conjClosure (conjSub y V) Y)) = ⊤ := by
  set X := conjClosure (conjSub y V) Y with hX
  set N := L619.normWZX (ch619W T L V z) (ch6ZS T L V) X with hN
  set K := L619.img0 hW (ch6ZS T L V) X with hK
  set Mq : Subgroup (IntMod (ch619W T L V z) hW ⧸ L619.modSub hW (ch6ZS T L V)) :=
    (commV K).map (L619.V0 hW (ch6ZS T L V) X).subtype with hMq
  have hXN : X ≤ N := c.conjClosure_E_le_normWZX hY
  have hgen : ∀ (g : G) (hg : g ∈ Y) (e : G) (he : e ∈ conjSub y V),
      L619.actQ hW (ch6ZS T L V) ⟨g * e * g⁻¹,
        (hXN (CFSG.Quasithin.mem_conjClosure hg he)).1⟩ ∈ centQuot Mq := by
    intro g hg e he
    have hxN : g * e * g⁻¹ ∈ N := hXN (CFSG.Quasithin.mem_conjClosure hg he)
    have hxX : g * e * g⁻¹ ∈ X := CFSG.Quasithin.mem_conjClosure hg he
    have hcomm : ∀ w ∈ ch619W T L V z, g * e * g⁻¹ * w * (g * e * g⁻¹)⁻¹ * w⁻¹ ∈
        conjSub g (conjSub y (ch6ZS T L V)) := fun w hw =>
      c.commutator_W_conj_mem h h6110 hab hz.ne_one hz.eq_inf hz.eq_comm
        (hY.le_normalizer_W hg) he hw
    have hcard := c.card_imgSub_conj_ZE h hz hY hW hg
    by_cases h1 : L619.act0 hW (ch6ZS T L V) X ⟨g * e * g⁻¹, hxN⟩ = 1
    · have hK2 := (c.act0_eq_one_iff h h432 hz hY hW (x := ⟨g * e * g⁻¹, hxN⟩) hxX).mp h1
      have hQ := (L619.actQ_eq_one_iff hW (Z := ch6ZS T L V) ⟨g * e * g⁻¹, hxN.1⟩).mpr hK2.2.2
      intro q
      rw [hQ, MulAut.one_apply, mul_inv_cancel]
      exact Subgroup.one_mem _
    · obtain ⟨v, hv⟩ : ∃ v, L619.act0 hW (ch6ZS T L V) X ⟨g * e * g⁻¹, hxN⟩ v ≠ v := by
        by_contra hcon
        push Not at hcon
        exact h1 (MulEquiv.ext hcon)
      set m₀ := L619.act0 hW (ch6ZS T L V) X ⟨g * e * g⁻¹, hxN⟩ v * v⁻¹ with hm₀
      have hm₀K : m₀ ∈ commV K := G6.mem_commV_of_mem (L619.act0_mem_img0 hW _ X hxX) v
      have hm₀M : (m₀ : IntMod (ch619W T L V z) hW ⧸ L619.modSub hW (ch6ZS T L V)) ∈ Mq :=
        ⟨m₀, hm₀K, rfl⟩
      have hm₀C : (m₀ : IntMod (ch619W T L V z) hW ⧸ L619.modSub hW (ch6ZS T L V)) ∈
          L619.imgSub hW (ch6ZS T L V) (conjSub g (conjSub y (ch6ZS T L V))) :=
        L619.actQ_mul_inv_mem_imgSub hW _ ⟨g * e * g⁻¹, hxN.1⟩ hcomm v
      have hm₀1 : (m₀ : IntMod (ch619W T L V z) hW ⧸ L619.modSub hW (ch6ZS T L V)) ≠ 1 := by
        intro h0
        apply hv
        have h0' : m₀ = 1 := Subtype.ext h0
        rw [hm₀, mul_inv_eq_one] at h0'
        exact h0'
      intro q
      have hqC := L619.actQ_mul_inv_mem_imgSub hW _ ⟨g * e * g⁻¹, hxN.1⟩ hcomm q
      by_cases hq1 : L619.actQ hW (ch6ZS T L V) ⟨g * e * g⁻¹, hxN.1⟩ q * q⁻¹ = 1
      · rw [hq1]
        exact Subgroup.one_mem _
      · by_cases hq2 : L619.actQ hW (ch6ZS T L V) ⟨g * e * g⁻¹, hxN.1⟩ q * q⁻¹ =
            (m₀ : IntMod (ch619W T L V z) hW ⧸ L619.modSub hW (ch6ZS T L V))
        · rw [hq2]
          exact hm₀M
        · exact (G6.false_of_card_two hcard hqC hm₀C hq1 hm₀1 hq2).elim
  have hle : L619.imgQ hW (ch6ZS T L V) X ≤ centQuot Mq := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hk
    rw [Subgroup.mem_subgroupOf] at hx
    have hXle : X ≤ ((centQuot Mq).comap (L619.actQ hW (ch6ZS T L V))).map
        (L619.normWZ (ch619W T L V z) (ch6ZS T L V)).subtype := by
      refine CFSG.Quasithin.conjClosure_le fun g hg e he => ?_
      exact ⟨_, hgen g hg e he, rfl⟩
    obtain ⟨x', hx', hxx⟩ := hXle hx
    have : x' = x := Subtype.ext hxx
    rw [← this]
    exact hx'
  have hV0 : L619.V0 hW (ch6ZS T L V) X ≤ Mq := G6.commV_le_iff.mpr fun k hk q => hle hk q
  rw [eq_top_iff]
  rintro v -
  obtain ⟨v', hv', hvv⟩ := hV0 v.2
  have : v' = v := Subtype.ext hvv
  rw [← this]
  exact hv'

end Cfg619

end CFSG.Quasithin.H13
