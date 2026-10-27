module

public import CFSG.Quasithin.H13.NQCoreWholeModuleTools
public import CFSG.Quasithin.SteinbergBQStrictFixedSpaceThompson

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup Module
open CFSG.Quasithin.SteinbergCD (glFixedSpace mem_glFixedSpace)
open scoped IsMulCommutative

section Transport

variable {G : Type} [Group G] {F : Subgroup G} (V : Subgroup ↥F) [IsMulCommutative ↥V]
  [Module (ZMod 2) (Additive ↥V)] {Y : Type} [Group Y] (ψ : Y ≃* ↥V)

@[expose] noncomputable def congrGL :
    MulAut Y →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V) :=
  (mulAutToGL V).comp (MulAut.congr ψ).toMonoidHom

theorem congrGL_apply (σ : MulAut Y) (y : Y) :
    ((congrGL V ψ σ : LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V)) :
      Additive ↥V →ₗ[ZMod 2] Additive ↥V) (Additive.ofMul (ψ y)) =
        Additive.ofMul (ψ (σ y)) := by
  change Additive.ofMul (ψ (σ (ψ.symm (ψ y)))) = _
  rw [ψ.symm_apply_apply]

theorem congrGL_injective : Function.Injective (congrGL V ψ) :=
  (mulAutToGL_injective V).comp (MulAut.congr ψ).injective

theorem card_map_congrGL (E : Subgroup (MulAut Y)) :
    Nat.card (E.map (congrGL V ψ)) = Nat.card E :=
  (Nat.card_congr (E.equivMapOfInjective _ (congrGL_injective V ψ)).toEquiv).symm

theorem map_congrGL_ne_bot {E : Subgroup (MulAut Y)} (hE : E ≠ ⊥) :
    E.map (congrGL V ψ) ≠ ⊥ := fun h =>
  hE ((map_eq_bot_iff_of_injective E (congrGL_injective V ψ)).mp h)

theorem isElementaryAbelian_map_congrGL {E : Subgroup (MulAut Y)}
    (hE : IsElementaryAbelian 2 ↥E) : IsElementaryAbelian 2 ↥(E.map (congrGL V ψ)) :=
  isElementaryAbelian_of_mulEquiv' (E.equivMapOfInjective _ (congrGL_injective V ψ)) hE

omit [IsMulCommutative ↥V] [Module (ZMod 2) (Additive ↥V)] in
include ψ in
theorem card_additive_eq : Nat.card (Additive ↥V) = Nat.card Y :=
  Nat.card_congr (Additive.toMul.trans ψ.symm.toEquiv)

theorem card_glFixedSpace_map_congrGL (E : Subgroup (MulAut Y)) :
    Nat.card (glFixedSpace (E.map (congrGL V ψ))) =
      Nat.card (FixedPoints.subgroup ↥E Y) := by
  have hmem : ∀ y : Y, Additive.ofMul (ψ y) ∈ glFixedSpace (E.map (congrGL V ψ)) ↔
      y ∈ FixedPoints.subgroup ↥E Y := by
    intro y
    rw [mem_glFixedSpace, SteinbergBQ.mem_fixedPoints_subgroup_mulAut_iff]
    constructor
    · intro h σ hσ
      have h1 := h _ ⟨σ, hσ, rfl⟩
      rw [congrGL_apply] at h1
      exact ψ.injective (Additive.ofMul.injective h1)
    · rintro h _ ⟨σ, hσ, rfl⟩
      rw [congrGL_apply, h σ hσ]
  exact (Nat.card_congr ((ψ.toEquiv.trans Additive.ofMul).subtypeEquiv fun y =>
    (hmem y).symm)).symm

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
@[expose] noncomputable def homDualEquiv :
    (Y →* Multiplicative (ZMod 2)) ≃ Module.Dual (ZMod 2) (Additive ↥V) :=
  ((MulEquiv.monoidHomCongrLeftEquiv ψ).trans MonoidHom.toAdditiveLeft).trans
    (AddMonoidHom.toZModLinearMapEquiv 2).toEquiv

theorem homDualEquiv_apply (φ : Y →* Multiplicative (ZMod 2)) (y : Y) :
    homDualEquiv V ψ φ (Additive.ofMul (ψ y)) = Multiplicative.toAdd (φ y) := by
  change Multiplicative.toAdd (φ (ψ.symm (ψ y))) = _
  rw [ψ.symm_apply_apply]

theorem card_invariant_dual_map_congrGL (E : Subgroup (MulAut Y)) :
    Nat.card {f : Module.Dual (ZMod 2) (Additive ↥V) //
        ∀ a ∈ E.map (congrGL V ψ), ∀ w,
          f ((a : Additive ↥V →ₗ[ZMod 2] Additive ↥V) w) = f w} =
      Nat.card {φ : Y →* Multiplicative (ZMod 2) // ∀ σ ∈ E, ∀ y, φ (σ y) = φ y} := by
  have hmem : ∀ φ : Y →* Multiplicative (ZMod 2), (∀ a ∈ E.map (congrGL V ψ), ∀ w,
      homDualEquiv V ψ φ ((a : Additive ↥V →ₗ[ZMod 2] Additive ↥V) w) =
        homDualEquiv V ψ φ w) ↔ ∀ σ ∈ E, ∀ y, φ (σ y) = φ y := by
    intro φ
    constructor
    · intro h σ hσ y
      have h1 := h _ ⟨σ, hσ, rfl⟩ (Additive.ofMul (ψ y))
      rw [congrGL_apply, homDualEquiv_apply, homDualEquiv_apply] at h1
      exact Multiplicative.toAdd.injective h1
    · rintro h _ ⟨σ, hσ, rfl⟩ w
      obtain ⟨y, rfl⟩ : ∃ y : Y, Additive.ofMul (ψ y) = w :=
        ⟨ψ.symm (Additive.toMul w), by rw [ψ.apply_symm_apply]; rfl⟩
      rw [congrGL_apply, homDualEquiv_apply, homDualEquiv_apply, h σ hσ]
  exact (Nat.card_congr ((homDualEquiv V ψ).subtypeEquiv fun φ => (hmem φ).symm)).symm

include ψ in
theorem card_dual_eq :
    Nat.card (Module.Dual (ZMod 2) (Additive ↥V)) = Nat.card (Y →* Multiplicative (ZMod 2)) :=
  (Nat.card_congr (homDualEquiv V ψ)).symm

theorem map_congrGL_le_of_conj [V.Normal] {T : Subgroup G} (hTF : T ≤ F) {E : Subgroup (MulAut Y)}
    (hE : ∀ σ ∈ E, ∃ t ∈ T, ∀ y : Y,
      (((ψ (σ y) : ↥V) : ↥F) : G) = t * (((ψ y : ↥V) : ↥F) : G) * t⁻¹) :
    E.map (congrGL V ψ) ≤ (T.subgroupOf F).map (conjGL V) := by
  rintro _ ⟨σ, hσ, rfl⟩
  obtain ⟨t, ht, hσt⟩ := hE σ hσ
  refine ⟨⟨t, hTF ht⟩, ht, ?_⟩
  apply Units.ext
  refine LinearMap.ext fun w => ?_
  obtain ⟨y, rfl⟩ : ∃ y : Y, Additive.ofMul (ψ y) = w :=
    ⟨ψ.symm (Additive.toMul w), by rw [ψ.apply_symm_apply]; rfl⟩
  rw [conjGL_apply, congrGL_apply]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  rw [hσt]
  rfl

end Transport

section Iso

variable {G : Type*} [Group G] {F : Subgroup G} (V : Subgroup ↥F) {P : Type*} [Group P]

@[expose] noncomputable def isoOfMap (ι : P →* G) (hι : Function.Injective ι) (K : Subgroup P)
    (hK : K.map ι = V.map F.subtype) : ↥K ≃* ↥V :=
  ((K.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hK)).trans
    (V.equivMapOfInjective F.subtype F.subtype_injective).symm

theorem isoOfMap_coe (ι : P →* G) (hι : Function.Injective ι) (K : Subgroup P)
    (hK : K.map ι = V.map F.subtype) (k : ↥K) :
    (((isoOfMap V ι hι K hK k : ↥V) : ↥F) : G) = ι k := by
  set e := V.equivMapOfInjective F.subtype F.subtype_injective with he
  have h1 : ∀ w : ↥(V.map F.subtype), (((e.symm w : ↥V) : ↥F) : G) = (w : G) := fun w => by
    conv_rhs => rw [← e.apply_symm_apply w]
    rfl
  exact h1 _

end Iso

theorem card_quotient_eq_two_pow_finrank {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (S : Submodule (ZMod 2) W) :
    Nat.card (W ⧸ S) = 2 ^ finrank (ZMod 2) (W ⧸ S) := by
  have : Finite (W ⧸ S) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective S)
  have : Module.Finite (ZMod 2) (W ⧸ S) := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

end CFSG.Quasithin.H13.NQCore
