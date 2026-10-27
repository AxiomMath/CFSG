module

public import CFSG.LocalAnalysis.WeakClosure81.W16QTIPair
public import CFSG.LocalAnalysis.WeakClosure81.W16QTIAbs
public import CFSG.LocalAnalysis.WeakClosure81.W19ModE

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.QuasithinUnique.Setup.Campbell
open CFSG.SignalizerFunctorTheorem.Quadratic
open Subgroup

variable {G : Type} [Group G] [Finite G]

structure ModDataB {K : Subgroup G} {X : Type} [Group X] (φ : ↥K →* X) (B : Subgroup X)
    (E : Subgroup G) where
  W : Type
  [addCommGroup : AddCommGroup W]
  [module : Module (ZMod 2) W]
  [finite : Finite W]
  ρ : ↥B →* LGL 2 W
  ι : G → W
  ι_mul : ∀ e ∈ E, ∀ e' ∈ E, ι (e * e') = ι e + ι e'
  ι_surj : ∀ w : W, ∃ e ∈ E, ι e = w
  ι_eq_zero : ∀ e ∈ E, ι e = 0 → e = 1
  ρ_ι : ∀ (k : ↥K) (hk : φ k ∈ B), ∀ e ∈ E,
    ρ ⟨φ k, hk⟩ (ι e) = ι ((k : G) * e * (k : G)⁻¹)

attribute [instance] ModDataB.addCommGroup ModDataB.module ModDataB.finite

private theorem w16q_ι_one {K : Subgroup G} {X : Type} [Group X] {φ : ↥K →* X}
    {B : Subgroup X} {E : Subgroup G} (D : ModDataB φ B E) : D.ι 1 = 0 := by
  have h := D.ι_mul 1 E.one_mem 1 E.one_mem
  rw [mul_one] at h
  exact left_eq_add.mp h

private theorem w16q_ι_inv {K : Subgroup G} {X : Type} [Group X] {φ : ↥K →* X}
    {B : Subgroup X} {E : Subgroup G} (D : ModDataB φ B E) {e : G} (he : e ∈ E) :
    D.ι e⁻¹ = - D.ι e := by
  have h := D.ι_mul e he e⁻¹ (E.inv_mem he)
  rw [mul_inv_cancel, w16q_ι_one D] at h
  exact eq_neg_of_add_eq_zero_right h.symm

private theorem w16q_ι_injOn {K : Subgroup G} {X : Type} [Group X] {φ : ↥K →* X}
    {B : Subgroup X} {E : Subgroup G} (D : ModDataB φ B E) {e e' : G}
    (he : e ∈ E) (he' : e' ∈ E) (h : D.ι e = D.ι e') : e = e' := by
  have h1 : D.ι (e * e'⁻¹) = 0 := by
    rw [D.ι_mul e he e'⁻¹ (E.inv_mem he'), w16q_ι_inv D he', h, add_neg_cancel]
  have h2 := D.ι_eq_zero _ (E.mul_mem he (E.inv_mem he')) h1
  exact mul_inv_eq_one.mp h2

private theorem w16q_ι_mul_inv {K : Subgroup G} {X : Type} [Group X] {φ : ↥K →* X}
    {B : Subgroup X} {E : Subgroup G} (D : ModDataB φ B E) {p q : G} (hp : p ∈ E)
    (hq : q ∈ E) : D.ι (p * q⁻¹) = D.ι p - D.ι q := by
  have h1 : D.ι p = D.ι (p * q⁻¹) + D.ι q := by
    have h := D.ι_mul (p * q⁻¹) (E.mul_mem hp (E.inv_mem hq)) q hq
    rw [show p * q⁻¹ * q = p by group] at h
    exact h
  exact eq_sub_of_add_eq h1.symm

namespace DichCfg

variable {M V₀ V U S H : Subgroup G} {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}

private theorem w16q_iSub16_elemAbelian (d : DichCfg M V₀ V U S H φ) :
    IsElemAbelian 2 (iSub16 V H) :=
  Cex16.isElemAbelian_iSub16 d.cfg.one d.cfg.std d.cfg.cex d.cfg.min.fam16

private theorem w16q_conjPair_le_iSub16 (d : DichCfg M V₀ V U S H φ)
    (x y : ↥(conjClosure V H)) : conjPairSub V₀ x y ≤ iSub16 V H :=
  sup_le (conj_V₀_le_iSub16 d x) (conj_V₀_le_iSub16 d y)

private theorem w16q_conjPair_elemAbelian (d : DichCfg M V₀ V U S H φ)
    (x y : ↥(conjClosure V H)) : IsElemAbelian 2 (conjPairSub V₀ x y) :=
  (w16q_iSub16_elemAbelian d).mono (w16q_conjPair_le_iSub16 d x y)

private theorem w16q_conjV_elemAbelian (d : DichCfg M V₀ V U S H φ)
    (z : ↥(conjClosure V H)) : IsElemAbelian 2 (conjSubgroup V (z : G)) :=
  d.cfg.cex.hyp.h6.elemAbelian.map (MulAut.conj (z : G)⁻¹).toMonoidHom

private theorem w16q_yConj_elemAbelian (d : DichCfg M V₀ V U S H φ)
    (z : ↥(conjClosure V H)) : IsElemAbelian 2 (yConj V H φ z) :=
  d.isElemAbelian_barSub.map (MulAut.conj (φ z)⁻¹).toMonoidHom

private theorem w16q_exists_mul_of_mem_conjPairSub (d : DichCfg M V₀ V U S H φ)
    {x y : ↥(conjClosure V H)} {w : G} (hw : w ∈ conjPairSub V₀ x y) :
    ∃ w₁ ∈ conjSubgroup V₀ (x : G), ∃ w₂ ∈ conjSubgroup V₀ (y : G), w = w₁ * w₂ := by
  have hc : ∀ p ∈ conjSubgroup V₀ (x : G), ∀ q ∈ conjSubgroup V₀ (y : G),
      p * q = q * p := fun p hp q hq =>
    (w16q_iSub16_elemAbelian d).comm
      (w16q_conjPair_le_iSub16 d x y (Subgroup.mem_sup_left hp))
      (w16q_conjPair_le_iSub16 d x y (Subgroup.mem_sup_right hq))
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (conjSubgroup V₀ (x : G)) (conjSubgroup V₀ (y : G)) hc).2
  have hw' : w ∈ ((conjSubgroup V₀ (x : G) ⊔ conjSubgroup V₀ (y : G) : Subgroup G) : Set G) :=
    hw
  rw [hset] at hw'
  obtain ⟨w₁, hw₁, w₂, hw₂, hw_eq⟩ := Set.mem_mul.mp hw'
  exact ⟨w₁, hw₁, w₂, hw₂, hw_eq.symm⟩

private theorem w16q_conj_mem_conjPairSub_left (d : DichCfg M V₀ V U S H φ)
    {x y : ↥(conjClosure V H)} {u w : G} (hu : u ∈ conjSubgroup V (x : G))
    (hw : w ∈ conjPairSub V₀ x y) : u * w * u⁻¹ ∈ conjPairSub V₀ x y := by
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := w16q_exists_mul_of_mem_conjPairSub d hw
  have hw₁V : w₁ ∈ conjSubgroup V (x : G) :=
    conjSubgroup_mono d.cfg.cex.hyp.h6.le (x : G) hw₁
  have hfix₁ : u * w₁ * u⁻¹ = w₁ := by
    have hc := (w16q_conjV_elemAbelian d x).comm hu hw₁V
    rw [hc]
    group
  have hI₂ : w₂ ∈ iSub16 V H :=
    w16q_conjPair_le_iSub16 d x y (Subgroup.mem_sup_right hw₂)
  have hcm : u * w₂ * u⁻¹ * w₂⁻¹ ∈ conjSubgroup V₀ (x : G) :=
    comm_mem_conj_V₀ d x.2 hu hI₂
  have hstep : u * w₂ * u⁻¹ ∈ conjPairSub V₀ x y := by
    have h : u * w₂ * u⁻¹ = (u * w₂ * u⁻¹ * w₂⁻¹) * w₂ := by group
    rw [h]
    exact (conjPairSub V₀ x y).mul_mem (Subgroup.mem_sup_left hcm) (Subgroup.mem_sup_right hw₂)
  rw [show u * (w₁ * w₂) * u⁻¹ = (u * w₁ * u⁻¹) * (u * w₂ * u⁻¹) by group, hfix₁]
  exact (conjPairSub V₀ x y).mul_mem (Subgroup.mem_sup_left hw₁) hstep

private theorem w16q_conj_mem_conjPairSub_right (d : DichCfg M V₀ V U S H φ)
    {x y : ↥(conjClosure V H)} {u w : G} (hu : u ∈ conjSubgroup V (y : G))
    (hw : w ∈ conjPairSub V₀ x y) : u * w * u⁻¹ ∈ conjPairSub V₀ x y := by
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := w16q_exists_mul_of_mem_conjPairSub d hw
  have hw₂V : w₂ ∈ conjSubgroup V (y : G) :=
    conjSubgroup_mono d.cfg.cex.hyp.h6.le (y : G) hw₂
  have hfix₂ : u * w₂ * u⁻¹ = w₂ := by
    have hc := (w16q_conjV_elemAbelian d y).comm hu hw₂V
    rw [hc]
    group
  have hI₁ : w₁ ∈ iSub16 V H :=
    w16q_conjPair_le_iSub16 d x y (Subgroup.mem_sup_left hw₁)
  have hcm : u * w₁ * u⁻¹ * w₁⁻¹ ∈ conjSubgroup V₀ (y : G) :=
    comm_mem_conj_V₀ d y.2 hu hI₁
  have hstep : u * w₁ * u⁻¹ ∈ conjPairSub V₀ x y := by
    have h : u * w₁ * u⁻¹ = (u * w₁ * u⁻¹ * w₁⁻¹) * w₁ := by group
    rw [h]
    exact (conjPairSub V₀ x y).mul_mem (Subgroup.mem_sup_right hcm) (Subgroup.mem_sup_left hw₁)
  rw [show u * (w₁ * w₂) * u⁻¹ = (u * w₁ * u⁻¹) * (u * w₂ * u⁻¹) by group, hfix₂]
  exact (conjPairSub V₀ x y).mul_mem hstep (Subgroup.mem_sup_right hw₂)

private theorem w16q_exists_lift (d : DichCfg M V₀ V U S H φ)
    {z : ↥(conjClosure V H)} {a : X} (ha : a ∈ yConj V H φ z) :
    ∃ u : ↥(conjClosure V H), (u : G) ∈ conjSubgroup V (z : G) ∧ φ u = a := by
  have h : a ∈ SevenK.barSub (conjClosure V H) φ (conjSubgroup V (z : G)) := by
    rw [barSub_conjSubgroup φ V z]
    exact ha
  exact SevenK.mem_barSub.mp h

private theorem w16q_not_comm_swap (d : DichCfg M V₀ V U S H φ) {x y : ↥(conjClosure V H)}
    (h : ¬ ∀ a ∈ yConj V H φ x, ∀ b ∈ yConj V H φ y, a * b = b * a) :
    ¬ ∀ a ∈ yConj V H φ y, ∀ b ∈ yConj V H φ x, a * b = b * a := by
  intro h'
  exact h fun a ha b hb => (h' b hb a ha).symm

theorem mem_normalizer_conjPairSub (d : DichCfg M V₀ V U S H φ) (x y k : ↥(conjClosure V H))
    (hk : φ k ∈ yConj V H φ x ⊔ yConj V H φ y) :
    (k : G) ∈ normalizer ((conjPairSub V₀ x y : Subgroup G) : Set G) := by
  have hVxK : conjSubgroup V (x : G) ≤ conjClosure V H := by
    calc conjSubgroup V (x : G) ≤ conjSubgroup (conjClosure V H) (x : G) :=
          conjSubgroup_mono (le_conjClosure V H) (x : G)
      _ = conjClosure V H :=
          conjSubgroup_eq_iff_mem_normalizer.2 (le_normalizer (H := conjClosure V H) x.2)
  have hVyK : conjSubgroup V (y : G) ≤ conjClosure V H := by
    calc conjSubgroup V (y : G) ≤ conjSubgroup (conjClosure V H) (y : G) :=
          conjSubgroup_mono (le_conjClosure V H) (y : G)
      _ = conjClosure V H :=
          conjSubgroup_eq_iff_mem_normalizer.2 (le_normalizer (H := conjClosure V H) y.2)
  have hVx : conjSubgroup V (x : G) ≤ normalizer (conjPairSub V₀ x y : Set G) := fun u hu =>
    E1.mem_normalizer_of_conj_mem fun w hw => w16q_conj_mem_conjPairSub_left d hu hw
  have hVy : conjSubgroup V (y : G) ≤ normalizer (conjPairSub V₀ x y : Set G) := fun u hu =>
    E1.mem_normalizer_of_conj_mem fun w hw => w16q_conj_mem_conjPairSub_right d hu hw
  have hI : iSub16 V H ≤ normalizer (conjPairSub V₀ x y : Set G) := by
    intro i hi
    refine E1.mem_normalizer_of_conj_mem fun w hw => ?_
    have hwi : w ∈ iSub16 V H := w16q_conjPair_le_iSub16 d x y hw
    have heq : i * w * i⁻¹ = w := by
      have hc := (w16q_iSub16_elemAbelian d).comm hi hwi
      rw [hc]
      group
    rw [heq]
    exact hw
  have hA_norm : conjSubgroup V (x : G) ⊔ conjSubgroup V (y : G) ⊔ iSub16 V H ≤
      normalizer (conjPairSub V₀ x y : Set G) := sup_le (sup_le hVx hVy) hI
  have hkA : φ k ∈ SevenK.barSub (conjClosure V H) φ
      (conjSubgroup V (x : G) ⊔ conjSubgroup V (y : G)) := by
    rw [barSub_sup hVxK hVyK φ, barSub_conjSubgroup φ V x, barSub_conjSubgroup φ V y]
    exact hk
  have hkA' : φ k ∈ ((conjSubgroup V (x : G) ⊔ conjSubgroup V (y : G) ⊔ iSub16 V H).subgroupOf
      (conjClosure V H)).map φ := by
    have hle : SevenK.barSub (conjClosure V H) φ (conjSubgroup V (x : G) ⊔
        conjSubgroup V (y : G)) ≤ SevenK.barSub (conjClosure V H) φ
          (conjSubgroup V (x : G) ⊔ conjSubgroup V (y : G) ⊔ iSub16 V H) :=
      Subgroup.map_mono (Subgroup.subgroupOf_mono (conjClosure V H) le_sup_left)
    exact hle hkA
  exact hA_norm (d.mem_of_map_mem le_sup_right hkA')

theorem exists_modDataB (d : DichCfg M V₀ V U S H φ) (x y : ↥(conjClosure V H)) :
    Nonempty (ModDataB φ (yConj V H φ x ⊔ yConj V H φ y) (conjPairSub V₀ x y)) := by
  classical
  let B : Subgroup X := yConj V H φ x ⊔ yConj V H φ y
  let E : Subgroup G := conjPairSub V₀ x y
  let J : Subgroup G := (B.comap φ).map (conjClosure V H).subtype
  have hE_ea : IsElemAbelian 2 E := w16q_conjPair_elemAbelian d x y
  have hJ : J ≤ normalizer (E : Set G) := by
    rintro g ⟨k, hk, rfl⟩
    exact mem_normalizer_conjPairSub d x y k hk
  obtain ⟨Mo⟩ := exists_modDataE hE_ea hJ
  let e : ↥(B.comap φ) ≃* ↥J :=
    Subgroup.equivMapOfInjective (B.comap φ) (conjClosure V H).subtype
      (conjClosure V H).subtype_injective
  let φB : ↥(B.comap φ) →* ↥B :=
    (φ.comp (B.comap φ).subtype).codRestrict B fun x => Subgroup.mem_comap.mp x.2
  let f : ↥J →* ↥B := φB.comp e.symm.toMonoidHom
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨k, hk⟩ := d.bar.surjective b.1
    have hkB : k ∈ B.comap φ := Subgroup.mem_comap.mpr (by rw [hk]; exact b.2)
    refine ⟨e ⟨k, hkB⟩, ?_⟩
    show φB (e.symm (e ⟨k, hkB⟩)) = b
    rw [MulEquiv.symm_apply_apply]
    exact Subtype.ext hk
  have hker : ∀ j : ↥J, f j = 1 → Mo.ρ j = 1 := by
    intro j hj
    rw [Mo.ρ_eq_one_iff, Subgroup.mem_centralizer_iff]
    intro w hw
    let i : ↥(B.comap φ) := e.symm j
    have h1 : φ i.1 = 1 := by
      have h2 : φB i = 1 := hj
      exact congrArg Subtype.val h2
    have h3 : (i.1 : G) ∈ iSub16 V H := (d.bar.ker_iff i.1).mp h1
    have h4 : (j : G) = (i.1 : G) := by
      have h := Subgroup.coe_equivMapOfInjective_apply (B.comap φ) (conjClosure V H).subtype
        (conjClosure V H).subtype_injective i
      rw [show e i = j from MulEquiv.apply_symm_apply e j] at h
      simpa using h
    have hjI : (j : G) ∈ iSub16 V H := by rw [h4]; exact h3
    exact ((w16q_iSub16_elemAbelian d).comm hjI
      (w16q_conjPair_le_iSub16 d x y hw)).symm
  obtain ⟨ρ', hρ'⟩ := exists_rep_of_ker_le f hf Mo.ρ hker
  refine ⟨⟨Mo.W, ρ', Mo.ι, Mo.ι_mul, Mo.ι_surj, Mo.ι_eq_zero, ?_⟩⟩
  intro k hk w hw
  have hkJ : (k : G) ∈ J := Subgroup.mem_map.mpr ⟨k, Subgroup.mem_comap.mpr hk, rfl⟩
  let j : ↥J := ⟨(k : G), hkJ⟩
  have hfj : f j = ⟨φ k, hk⟩ := by
    apply Subtype.ext
    show φB (e.symm j) = φ k
    have hs : e.symm j = ⟨k, Subgroup.mem_comap.mpr hk⟩ := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [Subgroup.coe_equivMapOfInjective_apply]
      rfl
    rw [hs]
    rfl
  calc ρ' ⟨φ k, hk⟩ (Mo.ι w) = ρ' (f j) (Mo.ι w) := by rw [hfj]
    _ = Mo.ρ j (Mo.ι w) := by rw [hρ']
    _ = Mo.ι ((j : G) * w * (j : G)⁻¹) := Mo.ρ_ι j w hw
    _ = Mo.ι ((k : G) * w * (k : G)⁻¹) := rfl

theorem fixed_iff (d : DichCfg M V₀ V U S H φ) {x y : ↥(conjClosure V H)}
    (hxy : ¬ ∀ a ∈ yConj V H φ x, ∀ b ∈ yConj V H φ y, a * b = b * a)
    (D : ModDataB φ (yConj V H φ x ⊔ yConj V H φ y) (conjPairSub V₀ x y))
    {z : ↥(conjClosure V H)} (hz : z = x ∨ z = y) {a : X} (ha : a ∈ yConj V H φ z) (ha1 : a ≠ 1)
    (haB : a ∈ yConj V H φ x ⊔ yConj V H φ y) (w : D.W) :
    D.ρ ⟨a, haB⟩ w = w ↔ ∃ e ∈ conjSubgroup V₀ (z : G), D.ι e = w := by
  rcases hz with hzx | hzy
  · rw [hzx] at ha ⊢
    constructor
    swap
    · rintro ⟨e, he, rfl⟩
      obtain ⟨u, hu, rfl⟩ := w16q_exists_lift d ha
      have heV : e ∈ conjSubgroup V (x : G) :=
        conjSubgroup_mono d.cfg.cex.hyp.h6.le (x : G) he
      have hfix : (u : G) * e * (u : G)⁻¹ = e := by
        have hc := (w16q_conjV_elemAbelian d x).comm hu heV
        rw [hc]
        group
      rw [D.ρ_ι u haB e (Subgroup.mem_sup_left he), hfix]
    · intro hw
      obtain ⟨u, hu, rfl⟩ := w16q_exists_lift d ha
      obtain ⟨e, heE, rfl⟩ := D.ι_surj w
      have hfix' : D.ι ((u : G) * e * (u : G)⁻¹) = D.ι e := by
        rw [← D.ρ_ι u haB e heE]
        exact hw
      have humem : (u : G) * e * (u : G)⁻¹ ∈ conjPairSub V₀ x y :=
        (Subgroup.mem_normalizer_iff.mp (mem_normalizer_conjPairSub d x y u haB) e).1 heE
      have hconj : (u : G) * e * (u : G)⁻¹ = e := w16q_ι_injOn D humem heE hfix'
      obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := w16q_exists_mul_of_mem_conjPairSub d heE
      have he₁V : e₁ ∈ conjSubgroup V (x : G) :=
        conjSubgroup_mono d.cfg.cex.hyp.h6.le (x : G) he₁
      have hfix₁ : (u : G) * e₁ * (u : G)⁻¹ = e₁ := by
        have hc := (w16q_conjV_elemAbelian d x).comm hu he₁V
        rw [hc]
        group
      have hconj₂ : (u : G) * e₂ * (u : G)⁻¹ = e₂ := by
        have h : (u : G) * (e₁ * e₂) * (u : G)⁻¹ =
            ((u : G) * e₁ * (u : G)⁻¹) * ((u : G) * e₂ * (u : G)⁻¹) := by group
        rw [h, hfix₁] at hconj
        exact mul_left_cancel hconj
      have hcomm₂ : (u : G) * e₂ = e₂ * (u : G) := by
        have h : (u : G) * e₂ * (u : G)⁻¹ = e₂ := hconj₂
        rw [mul_inv_eq_iff_eq_mul] at h
        exact h
      have he₂1 : e₂ = 1 := eq_one_of_comm d hxy hu ha1 he₂ hcomm₂
      refine ⟨e₁, he₁, ?_⟩
      rw [he₂1, mul_one]
  · rw [hzy] at ha ⊢
    constructor
    swap
    · rintro ⟨e, he, rfl⟩
      obtain ⟨u, hu, rfl⟩ := w16q_exists_lift d ha
      have heV : e ∈ conjSubgroup V (y : G) :=
        conjSubgroup_mono d.cfg.cex.hyp.h6.le (y : G) he
      have hfix : (u : G) * e * (u : G)⁻¹ = e := by
        have hc := (w16q_conjV_elemAbelian d y).comm hu heV
        rw [hc]
        group
      rw [D.ρ_ι u haB e (Subgroup.mem_sup_right he), hfix]
    · intro hw
      obtain ⟨u, hu, rfl⟩ := w16q_exists_lift d ha
      obtain ⟨e, heE, rfl⟩ := D.ι_surj w
      have hfix' : D.ι ((u : G) * e * (u : G)⁻¹) = D.ι e := by
        rw [← D.ρ_ι u haB e heE]
        exact hw
      have humem : (u : G) * e * (u : G)⁻¹ ∈ conjPairSub V₀ x y :=
        (Subgroup.mem_normalizer_iff.mp (mem_normalizer_conjPairSub d x y u haB) e).1 heE
      have hconj : (u : G) * e * (u : G)⁻¹ = e := w16q_ι_injOn D humem heE hfix'
      obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := w16q_exists_mul_of_mem_conjPairSub d heE
      have he₂V : e₂ ∈ conjSubgroup V (y : G) :=
        conjSubgroup_mono d.cfg.cex.hyp.h6.le (y : G) he₂
      have hfix₂ : (u : G) * e₂ * (u : G)⁻¹ = e₂ := by
        have hc := (w16q_conjV_elemAbelian d y).comm hu he₂V
        rw [hc]
        group
      have hconj₁ : (u : G) * e₁ * (u : G)⁻¹ = e₁ := by
        have h : (u : G) * (e₁ * e₂) * (u : G)⁻¹ =
            ((u : G) * e₁ * (u : G)⁻¹) * ((u : G) * e₂ * (u : G)⁻¹) := by group
        rw [h, hfix₂] at hconj
        exact mul_right_cancel hconj
      have hcomm₁ : (u : G) * e₁ = e₁ * (u : G) := by
        have h : (u : G) * e₁ * (u : G)⁻¹ = e₁ := hconj₁
        rw [mul_inv_eq_iff_eq_mul] at h
        exact h
      have he₁1 : e₁ = 1 :=
        eq_one_of_comm d (w16q_not_comm_swap d hxy) hu ha1 he₁ hcomm₁
      refine ⟨e₂, he₂, ?_⟩
      rw [he₁1, one_mul]

theorem natCard_modDataB (d : DichCfg M V₀ V U S H φ) {x y : ↥(conjClosure V H)}
    (hne : conjSubgroup V₀ (x : G) ≠ conjSubgroup V₀ (y : G))
    (D : ModDataB φ (yConj V H φ x ⊔ yConj V H φ y) (conjPairSub V₀ x y)) :
    Nat.card D.W = Nat.card V₀ ^ 2 := by
  have hbij : Function.Bijective (fun e : ↥(conjPairSub V₀ x y) => D.ι e.1) := by
    refine ⟨?_, ?_⟩
    · intro e e' h
      exact Subtype.ext (w16q_ι_injOn D e.2 e'.2 h)
    · intro w
      obtain ⟨e, he, hwe⟩ := D.ι_surj w
      exact ⟨⟨e, he⟩, hwe⟩
  have hcardW : Nat.card D.W = Nat.card (conjPairSub V₀ x y) :=
    (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
  have hcardE : Nat.card (conjPairSub V₀ x y) = Nat.card V₀ ^ 2 := by
    have hc : ∀ p ∈ conjSubgroup V₀ (x : G), ∀ q ∈ conjSubgroup V₀ (y : G),
        p * q = q * p := fun p hp q hq =>
      (w16q_iSub16_elemAbelian d).comm
        (w16q_conjPair_le_iSub16 d x y (Subgroup.mem_sup_left hp))
        (w16q_conjPair_le_iSub16 d x y (Subgroup.mem_sup_right hq))
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (conjSubgroup V₀ (x : G)) (conjSubgroup V₀ (y : G)) hc
    have hinf : conjSubgroup V₀ (x : G) ⊓ conjSubgroup V₀ (y : G) = ⊥ := inf_conj_V₀_eq_bot d hne
    have hcx : Nat.card (conjSubgroup V₀ (x : G)) = Nat.card V₀ := by
      rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj (x : G)⁻¹).injective]
    have hcy : Nat.card (conjSubgroup V₀ (y : G)) = Nat.card V₀ := by
      rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj (y : G)⁻¹).injective]
    rw [hinf, Subgroup.card_bot, mul_one, hcx, hcy] at hcard
    show Nat.card ((conjSubgroup V₀ (x : G) ⊔ conjSubgroup V₀ (y : G) : Subgroup G)) =
      Nat.card V₀ ^ 2
    rw [pow_two]
    exact hcard
  rw [hcardW, hcardE]

theorem eq_zero_of_mul_fixed (d : DichCfg M V₀ V U S H φ) {x y : ↥(conjClosure V H)}
    (hxy : ¬ ∀ a ∈ yConj V H φ x, ∀ b ∈ yConj V H φ y, a * b = b * a)
    (hne : conjSubgroup V₀ (x : G) ≠ conjSubgroup V₀ (y : G))
    (D : ModDataB φ (yConj V H φ x ⊔ yConj V H φ y) (conjPairSub V₀ x y))
    {a b : X} (ha : a ∈ yConj V H φ x) (hb : b ∈ yConj V H φ y) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (haB : a ∈ yConj V H φ x ⊔ yConj V H φ y) (hbB : b ∈ yConj V H φ x ⊔ yConj V H φ y)
    (w : D.W) (hw : D.ρ ⟨a, haB⟩ (D.ρ ⟨b, hbB⟩ w) = w) : w = 0 := by
  obtain ⟨u, hu, rfl⟩ := w16q_exists_lift d ha
  obtain ⟨v, hv, rfl⟩ := w16q_exists_lift d hb
  obtain ⟨e, heE, rfl⟩ := D.ι_surj w
  have hYu : IsElemAbelian 2 (yConj V H φ x) := w16q_yConj_elemAbelian d x
  have hua : (φ u) * (φ u) = 1 := by
    have h2 := hYu.2 (φ u) ha
    rwa [pow_two] at h2
  have hρuu : D.ρ ⟨φ u, haB⟩ * D.ρ ⟨φ u, haB⟩ = 1 := by
    have h1 : (⟨φ u, haB⟩ : ↥(yConj V H φ x ⊔ yConj V H φ y)) * ⟨φ u, haB⟩ = 1 :=
      Subtype.ext (by simpa using hua)
    rw [← map_mul, h1, map_one]
  have hρuu_fun : ∀ z : D.W, D.ρ ⟨φ u, haB⟩ (D.ρ ⟨φ u, haB⟩ z) = z := by
    intro z
    have h2 := congrArg (fun f : LGL 2 D.W => f z) hρuu
    simpa using h2
  have hb_eq : D.ρ ⟨φ v, hbB⟩ (D.ι e) = D.ρ ⟨φ u, haB⟩ (D.ι e) := by
    have h2 : D.ρ ⟨φ u, haB⟩ (D.ρ ⟨φ u, haB⟩ (D.ρ ⟨φ v, hbB⟩ (D.ι e))) =
        D.ρ ⟨φ u, haB⟩ (D.ι e) := congrArg (D.ρ ⟨φ u, haB⟩) hw
    rw [hρuu_fun] at h2
    exact h2
  have huE : (u : G) * e * (u : G)⁻¹ ∈ conjPairSub V₀ x y :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_conjPairSub d x y u haB) e).1 heE
  have hιa : D.ρ ⟨φ u, haB⟩ (D.ι e) - D.ι e =
      D.ι ((u : G) * e * (u : G)⁻¹ * e⁻¹) := by
    rw [D.ρ_ι u haB e heE]
    exact (w16q_ι_mul_inv D huE heE).symm
  have hvE : (v : G) * e * (v : G)⁻¹ ∈ conjPairSub V₀ x y :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_conjPairSub d x y v hbB) e).1 heE
  have hιb : D.ρ ⟨φ u, haB⟩ (D.ι e) - D.ι e =
      D.ι ((v : G) * e * (v : G)⁻¹ * e⁻¹) := by
    rw [← hb_eq, D.ρ_ι v hbB e heE]
    exact (w16q_ι_mul_inv D hvE heE).symm
  have hxmem : (u : G) * e * (u : G)⁻¹ * e⁻¹ ∈ conjPairSub V₀ x y :=
    Subgroup.mem_sup_left
      (comm_mem_conj_V₀ d x.2 hu (w16q_conjPair_le_iSub16 d x y heE))
  have hymem : (v : G) * e * (v : G)⁻¹ * e⁻¹ ∈ conjPairSub V₀ x y :=
    Subgroup.mem_sup_right
      (comm_mem_conj_V₀ d y.2 hv (w16q_conjPair_le_iSub16 d x y heE))
  have hcross : (u : G) * e * (u : G)⁻¹ * e⁻¹ =
      (v : G) * e * (v : G)⁻¹ * e⁻¹ :=
    w16q_ι_injOn D hxmem hymem (by rw [← hιa, ← hιb])
  have ht : D.ρ ⟨φ u, haB⟩ (D.ι e) - D.ι e = 0 := by
    have hxV₀ : (u : G) * e * (u : G)⁻¹ * e⁻¹ ∈ conjSubgroup V₀ (x : G) :=
      comm_mem_conj_V₀ d x.2 hu (w16q_conjPair_le_iSub16 d x y heE)
    have hyV₀ : (v : G) * e * (v : G)⁻¹ * e⁻¹ ∈ conjSubgroup V₀ (y : G) :=
      comm_mem_conj_V₀ d y.2 hv (w16q_conjPair_le_iSub16 d x y heE)
    have hx0 : (u : G) * e * (u : G)⁻¹ * e⁻¹ = 1 := by
      have hbot : (u : G) * e * (u : G)⁻¹ * e⁻¹ ∈ (⊥ : Subgroup G) := by
        rw [← inf_conj_V₀_eq_bot d hne]
        exact ⟨hxV₀, by rw [hcross]; exact hyV₀⟩
      exact Subgroup.mem_bot.mp hbot
    rw [hιa, hx0, w16q_ι_one D]
  have hwa : D.ρ ⟨φ u, haB⟩ (D.ι e) = D.ι e := sub_eq_zero.mp ht
  have hwb : D.ρ ⟨φ v, hbB⟩ (D.ι e) = D.ι e := by rw [hb_eq, hwa]
  obtain ⟨e₁, he₁, hw₁⟩ :=
    (fixed_iff d hxy D (Or.inl rfl) ha ha1 haB (D.ι e)).mp hwa
  obtain ⟨e₂, he₂, hw₂⟩ :=
    (fixed_iff d hxy D (Or.inr rfl) hb hb1 hbB (D.ι e)).mp hwb
  have hι : D.ι e₁ = D.ι e₂ := by rw [hw₁, hw₂]
  have h12 : e₁ = e₂ :=
    w16q_ι_injOn D (Subgroup.mem_sup_left he₁) (Subgroup.mem_sup_right he₂) hι
  have hbot : e₁ ∈ (⊥ : Subgroup G) := by
    rw [← inf_conj_V₀_eq_bot d hne]
    exact ⟨he₁, by rw [h12]; exact he₂⟩
  have he₁1 : e₁ = 1 := Subgroup.mem_bot.mp hbot
  rw [← hw₁, he₁1, w16q_ι_one D]

theorem exists_ρ_ne_one (d : DichCfg M V₀ V U S H φ) {x y : ↥(conjClosure V H)}
    (hxy : ¬ ∀ a ∈ yConj V H φ x, ∀ b ∈ yConj V H φ y, a * b = b * a)
    (hne : conjSubgroup V₀ (x : G) ≠ conjSubgroup V₀ (y : G))
    (D : ModDataB φ (yConj V H φ x ⊔ yConj V H φ y) (conjPairSub V₀ x y)) : D.ρ ≠ 1 := by
  intro hρ
  have hxne : yConj V H φ x ≠ ⊥ := by
    intro hbot
    apply hxy
    intro a ha b hb
    have ha1 : a = 1 := by
      rw [hbot] at ha
      exact Subgroup.mem_bot.mp ha
    rw [ha1, one_mul, mul_one]
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hxne
  have haX1 : (a : X) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haB : (a : X) ∈ yConj V H φ x ⊔ yConj V H φ y := Subgroup.mem_sup_left a.2
  have hV0y : conjSubgroup V₀ (y : G) ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (conjSubgroup V₀ (y : G)) = 1 := by rw [hbot, Subgroup.card_bot]
    have hcard0 : Nat.card V₀ = 1 := by
      rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj (y : G)⁻¹).injective] at hcard
      exact hcard
    exact d.cfg.cex.hyp.ne_bot (Subgroup.card_eq_one.mp hcard0)
  obtain ⟨e, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hV0y
  have heE : (e : G) ∈ conjPairSub V₀ x y := Subgroup.mem_sup_right e.2
  have hfix : D.ρ ⟨(a : X), haB⟩ (D.ι (e : G)) = D.ι (e : G) := by
    have h1 : D.ρ ⟨(a : X), haB⟩ = 1 :=
      congrArg (fun f : ↥(yConj V H φ x ⊔ yConj V H φ y) →* LGL 2 D.W => f ⟨(a : X), haB⟩) hρ
    rw [h1]
    rfl
  obtain ⟨e₀, he₀, hι⟩ :=
    (fixed_iff d hxy D (Or.inl rfl) a.2 haX1 haB (D.ι (e : G))).mp hfix
  have hE₀ : e₀ ∈ conjPairSub V₀ x y := Subgroup.mem_sup_left he₀
  have heq : e₀ = (e : G) := w16q_ι_injOn D hE₀ heE hι
  have hbot : (e : G) ∈ (⊥ : Subgroup G) := by
    rw [← inf_conj_V₀_eq_bot d hne]
    exact ⟨by rw [← heq]; exact he₀, e.2⟩
  exact he1 (Subtype.ext (Subgroup.mem_bot.mp hbot))

end DichCfg

end CFSG.LocalAnalysis.WeakClosure81

end
