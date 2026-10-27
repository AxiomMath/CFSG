module

public import CFSG.Monster.B.TwoA.Sp8.Normalizer
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagJointQuadratic
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixPointRadical

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open Module CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Co2Inv
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open scoped commutatorElement

private theorem coe_bilinIsometryEquivTauCeti
    (g : CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup b0) (w : V8) :
    ((bilinIsometryEquivTauCeti b0 g :
      V8 ≃ₗ[ZMod 2] V8)) w =
      (((g : LinearMap.GeneralLinearGroup (ZMod 2) V8) : V8 →ₗ[ZMod 2] V8)) w := rfl


@[expose] def PLam (Λ : Submodule (ZMod 2) V8) : Subgroup Dfull :=
  Xgrp ⊓ Subgroup.centralizer
    ((fun v : V8 => (aEquiv (Multiplicative.ofAdd v) : Dfull)) '' (Λ : Set V8))

private theorem commutator_aEquiv_rhoX (x : Xgrp) (v : V8) :
    ⁅(aEquiv (Multiplicative.ofAdd v) : Dfull), (x : Dfull)⁆ =
      (aEquiv (Multiplicative.ofAdd (v - rhoX x v)) : Dfull) := by
  have h := aEquiv_rhoX x v
  have hrhs : (aEquiv (Multiplicative.ofAdd (v - rhoX x v)) : Dfull) =
      (aEquiv (Multiplicative.ofAdd v) : Dfull) *
        ((aEquiv (Multiplicative.ofAdd (rhoX x v)) : Dfull))⁻¹ := by
    simp [ofAdd_sub, div_eq_mul_inv]
  rw [commutatorElement_def, hrhs, h]
  group

theorem exists_conj_le_PLam_of_quadratic {A : Subgroup Dfull} (hAX : A ≤ Xgrp)
    (hq : ⁅⁅A8, A⁆, A⁆ = ⊥) {Λ : Submodule (ZMod 2) V8}
    (hΛ : IsTotallyIsotropic b0 Λ) (hd : finrank (ZMod 2) Λ = 4) :
    ∃ x ∈ Xgrp, A.map (MulAut.conj x).toMonoidHom ≤ PLam Λ := by
  let E : Subgroup (TauCeti.BilinForm.isometryGroup b0) := (A.subgroupOf Xgrp).map rhoXSp
  have hE : ∀ a ∈ E, ∀ c ∈ E, ∀ v : V8,
      (c : V8 ≃ₗ[ZMod 2] V8) ((a : V8 ≃ₗ[ZMod 2] V8) v - v) -
        ((a : V8 ≃ₗ[ZMod 2] V8) v - v) = 0 := by
    intro a ha c hc v
    obtain ⟨a0, ha0, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨c0, hc0, rfl⟩ := Subgroup.mem_map.1 hc
    have ha0A : (a0 : Dfull) ∈ A := Subgroup.mem_subgroupOf.1 ha0
    have hc0A : (c0 : Dfull) ∈ A := Subgroup.mem_subgroupOf.1 hc0
    have hq' : ⁅⁅(aEquiv (Multiplicative.ofAdd v) : Dfull), (a0 : Dfull)⁆,
        (c0 : Dfull)⁆ = 1 := by
      have hmem := Subgroup.commutator_mem_commutator
        (Subgroup.commutator_mem_commutator (aEquiv (Multiplicative.ofAdd v)).2 ha0A) hc0A
      rw [hq] at hmem
      exact Subgroup.mem_bot.1 hmem
    rw [commutator_aEquiv_rhoX a0 v,
      commutator_aEquiv_rhoX c0 (v - rhoX a0 v)] at hq'
    have hzero : v - rhoX a0 v - rhoX c0 (v - rhoX a0 v) = 0 := by
      apply aEquiv_coe_injective (w := 0)
      exact hq'.trans (by simp)
    have hfix : rhoX c0 (v - rhoX a0 v) = v - rhoX a0 v :=
      (sub_eq_zero.mp hzero).symm
    have hsymm : rhoX a0 v - v = v - rhoX a0 v := by
      rw [sub_eq_add_zmod_two,
        sub_eq_add_zmod_two, add_comm]
    rw [coe_rhoXSp, coe_rhoXSp, hsymm]
    exact sub_eq_zero.mpr hfix
  obtain ⟨W, hWiso, hWdim, hWfix⟩ :=
    exists_lagrangian_fixed_of_jointQuadratic b0_isAlt b0_nondegenerate finrank_V8 E hE
  obtain ⟨g, hg⟩ :=
    exists_isometry_map_eq_of_lagrangian b0_isAlt b0_nondegenerate finrank_V8 hWiso hWdim hΛ hd
  obtain ⟨x, hx⟩ := rhoXSp_surjective g
  refine ⟨(x : Dfull), x.2, ?_⟩
  rw [Subgroup.map_le_iff_le_comap]
  intro a ha
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · change MulAut.conj (x : Dfull) a ∈ Xgrp
    rw [MulAut.conj_apply]
    exact Xgrp.mul_mem (Xgrp.mul_mem x.2 (hAX ha)) (Xgrp.inv_mem x.2)
  · rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hwW : w ∈ Λ := hw
    rw [← hg] at hwW
    obtain ⟨w0, hw0W, hgw0⟩ := Submodule.mem_map.1 hwW
    have hw_eq : rhoX x w0 = w := by
      have h' : ((rhoXSp x : TauCeti.BilinForm.isometryGroup b0) : V8 ≃ₗ[ZMod 2] V8)
          w0 = w := by
        rw [hx]
        simpa using hgw0
      rwa [coe_rhoXSp] at h'
    have hz_eq : (aEquiv (Multiplicative.ofAdd w) : Dfull) =
        (x : Dfull) * (aEquiv (Multiplicative.ofAdd w0) : Dfull) * (x : Dfull)⁻¹ := by
      rw [← hw_eq]
      exact aEquiv_rhoX x w0
    have hfixa : rhoX ⟨a, hAX ha⟩ w0 = w0 := by
      have hmem : rhoXSp ⟨a, hAX ha⟩ ∈ E :=
        Subgroup.mem_map_of_mem rhoXSp (Subgroup.mem_subgroupOf.2 ha)
      have h := hWfix _ hmem w0 hw0W
      rwa [coe_rhoXSp] at h
    have hafix : (aEquiv (Multiplicative.ofAdd w0) : Dfull) =
        (a : Dfull) * (aEquiv (Multiplicative.ofAdd w0) : Dfull) * (a : Dfull)⁻¹ := by
      have h := aEquiv_rhoX (⟨a, hAX ha⟩ : Xgrp) w0
      rw [hfixa] at h
      simpa using h
    have hcomm_a : (a : Dfull) * (aEquiv (Multiplicative.ofAdd w0) : Dfull) =
        (aEquiv (Multiplicative.ofAdd w0) : Dfull) * (a : Dfull) := by
      calc (a : Dfull) * (aEquiv (Multiplicative.ofAdd w0) : Dfull)
          = ((a : Dfull) * (aEquiv (Multiplicative.ofAdd w0) : Dfull) *
              (a : Dfull)⁻¹) * (a : Dfull) := by group
        _ = (aEquiv (Multiplicative.ofAdd w0) : Dfull) * (a : Dfull) := by rw [← hafix]
    change (aEquiv (Multiplicative.ofAdd w) : Dfull) * MulAut.conj (x : Dfull) a =
      MulAut.conj (x : Dfull) a * (aEquiv (Multiplicative.ofAdd w) : Dfull)
    rw [MulAut.conj_apply]
    calc (aEquiv (Multiplicative.ofAdd w) : Dfull) *
          ((x : Dfull) * a * (x : Dfull)⁻¹)
        = ((x : Dfull) * (aEquiv (Multiplicative.ofAdd w0) : Dfull) * (x : Dfull)⁻¹) *
            ((x : Dfull) * a * (x : Dfull)⁻¹) := by rw [hz_eq]
      _ = (x : Dfull) * ((aEquiv (Multiplicative.ofAdd w0) : Dfull) * a) *
            (x : Dfull)⁻¹ := by group
      _ = (x : Dfull) * (a * (aEquiv (Multiplicative.ofAdd w0) : Dfull)) *
            (x : Dfull)⁻¹ := by rw [hcomm_a]
      _ = ((x : Dfull) * a * (x : Dfull)⁻¹) *
            ((x : Dfull) * (aEquiv (Multiplicative.ofAdd w0) : Dfull) * (x : Dfull)⁻¹) := by
          group
      _ = ((x : Dfull) * a * (x : Dfull)⁻¹) *
            (aEquiv (Multiplicative.ofAdd w) : Dfull) := by rw [hz_eq]

theorem Lgrp_le_PLam (Λ : Submodule (ZMod 2) V8) : Lgrp ≤ PLam Λ := by
  rw [PLam]
  refine le_inf Lgrp_le_Xgrp ?_
  rw [Lgrp]
  exact Subgroup.centralizer_le (by
    rintro _ ⟨v, -, rfl⟩
    exact (aEquiv (Multiplicative.ofAdd v)).2)

theorem natCard_PLam {Λ : Submodule (ZMod 2) V8} (hΛ : IsTotallyIsotropic b0 Λ)
    (hd : finrank (ZMod 2) Λ = 4) : Nat.card (PLam Λ) = 2 ^ 35 := by
  obtain ⟨e, he, hΛe⟩ :=
    exists_basis_lagrangianOf
      (n := 4) b0_isAlt b0_nondegenerate finrank_V8 hΛ hd
  subst Λ
  let R : Subgroup (TauCeti.BilinForm.isometryGroup b0) :=
    { carrier := {g | ∀ w ∈ lagrangianOf e,
        (g : V8 ≃ₗ[ZMod 2] V8) w = w}
      one_mem' := by intro w _; rfl
      mul_mem' := by
        intro g h hg hh w hw
        change ((g * h : TauCeti.BilinForm.isometryGroup b0) : V8 ≃ₗ[ZMod 2] V8) w = w
        rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hh w hw, hg w hw]
      inv_mem' := by
        intro g hg w hw
        change ((g⁻¹ : TauCeti.BilinForm.isometryGroup b0) : V8 ≃ₗ[ZMod 2] V8) w = w
        rw [Subgroup.coe_inv]
        exact (Equiv.symm_apply_eq (g : V8 ≃ₗ[ZMod 2] V8) (x := w) (y := w)).2
          (hg w hw).symm }
  have hRcard : Nat.card R = 2 ^ 10 := by
    have h1 : Nat.card R =
        Nat.card (pointwiseStabilizer b0
          (lagrangianOf e)) := by
      refine (Nat.card_congr (Equiv.subtypeEquiv
        (bilinIsometryEquivTauCeti b0)
        ?_)).symm
      intro g
      rw [mem_pointwiseStabilizer]
      constructor
      · intro h w hw
        rw [coe_bilinIsometryEquivTauCeti]
        exact h w hw
      · intro h w hw
        rw [← coe_bilinIsometryEquivTauCeti]
        exact h w hw
    calc Nat.card R =
        Nat.card (pointwiseStabilizer b0
          (lagrangianOf e)) := h1
      _ = 2 ^ (4 * (4 + 1) / 2) :=
          card_pointwiseStabilizer_lagrangianOf (n := 4) (b := b0) he
      _ = 2 ^ 10 := by norm_num
  have hfixiff : ∀ x : Xgrp,
      rhoXSp x ∈ R ↔ ∀ w ∈ lagrangianOf e,
        rhoX x w = w := by
    intro x
    constructor
    · intro h w hw
      have h' := h w hw
      rwa [coe_rhoXSp] at h'
    · intro h w hw
      rw [coe_rhoXSp]
      exact h w hw
  have hEq : PLam (lagrangianOf e) =
      (R.comap rhoXSp).map Xgrp.subtype := by
    apply le_antisymm
    · intro y hy
      rw [PLam] at hy
      obtain ⟨hyX, hyC⟩ := Subgroup.mem_inf.1 hy
      refine Subgroup.mem_map.2 ⟨⟨y, hyX⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      rw [hfixiff]
      intro w hw
      apply aEquiv_coe_injective (w := w)
      calc (aEquiv (Multiplicative.ofAdd (rhoX ⟨y, hyX⟩ w)) : Dfull)
          = y * (aEquiv (Multiplicative.ofAdd w) : Dfull) * y⁻¹ := aEquiv_rhoX ⟨y, hyX⟩ w
        _ = (aEquiv (Multiplicative.ofAdd w) : Dfull) := by
            have hc := Subgroup.mem_centralizer_iff.1 hyC
              (aEquiv (Multiplicative.ofAdd w)) ⟨w, hw, rfl⟩
            calc y * (aEquiv (Multiplicative.ofAdd w) : Dfull) * y⁻¹
                = (aEquiv (Multiplicative.ofAdd w) : Dfull) * y * y⁻¹ := by rw [hc]
              _ = (aEquiv (Multiplicative.ofAdd w) : Dfull) := by group
    · intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [Subgroup.mem_comap] at hx
      rw [PLam]
      refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨w, hw, rfl⟩ := hz
      have hxw : rhoX x w = w := (hfixiff x).1 hx w hw
      have h := aEquiv_rhoX x w
      rw [hxw] at h
      calc (aEquiv (Multiplicative.ofAdd w) : Dfull) * (x : Dfull)
          = ((x : Dfull) * (aEquiv (Multiplicative.ofAdd w) : Dfull) * (x : Dfull)⁻¹) *
              (x : Dfull) := by
            nth_rewrite 1 [h]
            rfl
        _ = (x : Dfull) * (aEquiv (Multiplicative.ofAdd w) : Dfull) := by group
  have hEqcard : Nat.card (PLam
      (lagrangianOf e)) =
      Nat.card (R.comap rhoXSp) := by
    rw [hEq, Subgroup.card_subtype]
  have hKcard : Nat.card rhoXSp.ker = 2 ^ 25 :=
    (congrArg (fun H : Subgroup Xgrp => Nat.card H) ker_rhoXSp).trans
      ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe Lgrp_le_Xgrp).toEquiv).trans natCard_Lgrp)
  have hKle : rhoXSp.ker ≤ R.comap rhoXSp := by
    intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
    exact R.one_mem
  let f : (R.comap rhoXSp) →* R :=
    { toFun := fun x => ⟨rhoXSp (x : Xgrp), x.2⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        apply Subtype.ext
        simp }
  have hfker : f.ker = rhoXSp.ker.subgroupOf (R.comap rhoXSp) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hfker_card : Nat.card f.ker = Nat.card rhoXSp.ker := by
    rw [hfker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv
  have hfsurj : Function.Surjective f := by
    intro r
    obtain ⟨x, hx⟩ := rhoXSp_surjective (r : TauCeti.BilinForm.isometryGroup b0)
    refine ⟨⟨x, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap, hx]
      exact r.2
    · exact Subtype.ext hx
  have hfrange : Nat.card f.range = Nat.card R :=
    (Subgroup.card_eq_iff_eq_top _).2 (MonoidHom.range_eq_top.2 hfsurj)
  have hcard : Nat.card (R.comap rhoXSp) = 2 ^ 25 * Nat.card R := by
    rw [← natCard_ker_mul_range f, hfker_card, hfrange, hKcard]
  rw [hEqcard, hcard, hRcard]
  norm_num

theorem PLam_le_H1 {Λ : Submodule (ZMod 2) V8} (h : e0 ∈ Λ) : PLam Λ ≤ H1 := by
  have h1 : PLam Λ ≤ Xgrp := by
    show Xgrp ⊓ Subgroup.centralizer
      ((fun v : V8 => (aEquiv (Multiplicative.ofAdd v) : Dfull)) '' (Λ : Set V8)) ≤ Xgrp
    exact inf_le_left
  have h2 : PLam Λ ≤ Subgroup.centralizer {xhat} := by
    show Xgrp ⊓ Subgroup.centralizer
      ((fun v : V8 => (aEquiv (Multiplicative.ofAdd v) : Dfull)) '' (Λ : Set V8)) ≤
        Subgroup.centralizer {xhat}
    refine le_trans inf_le_right ?_
    apply Subgroup.centralizer_le
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨e0, h, aEquiv_e0⟩
  rw [← Xgrp_inf_centralizer_xhat]
  exact le_inf h1 h2

end CFSG.Monster.B.TwoA.Sp8
