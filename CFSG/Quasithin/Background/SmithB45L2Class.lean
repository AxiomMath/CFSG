module

public import CFSG.Quasithin.Background.SmithB45L2Outer
public import CFSG.Quasithin.Background.SmithB42L2Sl2

public section

namespace CFSG.Quasithin.B45L2

open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Lift
open scoped MatrixGroups

section W

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem twoF_class {n : ℕ} (hn : 3 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) SL(2, F) W) (hρ : Function.Injective ρ) (hirr : ρ.IsIrreducible)
    (A : Subgroup (Module.End (ZMod 2) W)ˣ) [CFSG.IsElementaryAbelian 2 A] (hA1 : A ≠ ⊥)
    (hAN : A ≤ Subgroup.normalizer (ρ.toHomUnits.range : Set (Module.End (ZMod 2) W)ˣ))
    (hoff : Nat.card W ≤ Nat.card A ^ 2 * Nat.card {w : W // ∀ a ∈ A, a.val w = w}) :
    (Nat.card (EndRing ρ) = 2 ^ n ∧ Module.finrank (EndRing ρ) W = 2) ∨
      ∃ s, n = 2 * s ∧ Nat.card (EndRing ρ) = 2 ^ s ∧ Module.finrank (EndRing ρ) W = 4 := by
  classical
  by_cases hAL : A ≤ ρ.toHomUnits.range
  · have : Fact ρ.IsIrreducible := ⟨hirr⟩
    have hne : (uElt (1 : F) : SL(2, F)) ≠ 1 := fun h =>
      one_ne_zero (uElt_injective (h.trans uElt_zero.symm))
    have hnt : ∃ g, ρ g ≠ 1 := ⟨uElt 1, fun h => hne (hρ (h.trans (map_one ρ).symm))⟩
    have hρU : Function.Injective ρ.toHomUnits := fun g h e =>
      hρ (by simpa using congrArg Units.val e)
    set A' : Subgroup SL(2, F) := A.comap ρ.toHomUnits with hA'
    have hmap : A'.map ρ.toHomUnits = A := Subgroup.map_comap_eq_self hAL
    have hcard : Nat.card A' = Nat.card A := by
      rw [← hmap, Subgroup.card_map_of_injective hρU]
    have hA'1 : A' ≠ ⊥ := by
      intro h
      apply hA1
      rw [← hmap, h, Subgroup.map_bot]
    have hA'2 : ∀ g ∈ A', g * g = 1 := by
      intro g hg
      apply hρU
      rw [map_mul, map_one]
      have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (ρ.toHomUnits g) hg
      rwa [pow_two] at this
    have hfix : Nat.card {w : W // ∀ g ∈ A', ρ g w = w} =
        Nat.card {w : W // ∀ a ∈ A, a.val w = w} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
      constructor
      · intro h a ha
        obtain ⟨g, rfl⟩ := hAL ha
        exact h g ha
      · intro h g hg
        exact h _ hg
    exact inner_class (by omega) hF ρ hnt A' hA'1 hA'2 (by rw [hcard, hfix]; exact hoff)
  · exact outer_class hn hF ρ hρ hirr A hAN hoff hAL

end W

section V

variable {V : Type} [CommGroup V] [Finite V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  {F : Type} [Field F]

@[expose] def repOf (θ : V ≃* Multiplicative W) {L : Subgroup (MulAut V)} (θL : ↥L ≃* SL(2, F)) :
    Representation (ZMod 2) SL(2, F) W where
  toFun g := (binPsi θ ((θL.symm g : ↥L) : MulAut V)).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro w
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro w
    simp

omit [Finite V] in
theorem repOf_apply (θ : V ≃* Multiplicative W) {L : Subgroup (MulAut V)} (θL : ↥L ≃* SL(2, F))
    (g : SL(2, F)) (w : W) :
    repOf θ θL g w = binPsi θ ((θL.symm g : ↥L) : MulAut V) w := rfl

omit [Finite V] in
theorem repOf_theta (θ : V ≃* Multiplicative W) {L : Subgroup (MulAut V)} (θL : ↥L ≃* SL(2, F))
    (l : ↥L) (w : W) : repOf θ θL (θL l) w = binPsi θ (l : MulAut V) w := by
  rw [repOf_apply, MulEquiv.symm_apply_apply]

omit [Finite V] in
theorem repOf_injective (θ : V ≃* Multiplicative W) {L : Subgroup (MulAut V)}
    (θL : ↥L ≃* SL(2, F)) : Function.Injective (repOf θ θL) := by
  intro g h hgh
  apply θL.symm.injective
  apply Subtype.ext
  apply (binPsi θ).injective
  apply LinearEquiv.ext
  intro w
  exact congrArg (fun f : Module.End (ZMod 2) W => f w) hgh

omit [Finite V] in
theorem repOf_range (θ : V ≃* Multiplicative W) {L : Subgroup (MulAut V)}
    (θL : ↥L ≃* SL(2, F)) :
    (repOf θ θL).toHomUnits.range = toUnits (L.map (binPsi θ).toMonoidHom) := by
  ext u
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨((θL.symm g : ↥L) : MulAut V), (θL.symm g).2, ?_⟩
    apply LinearEquiv.ext
    intro w
    rfl
  · rintro ⟨l, hl, hlu⟩
    refine ⟨θL ⟨l, hl⟩, Units.ext (LinearMap.ext fun w => ?_)⟩
    have h1 : (unitsEquiv (ZMod 2) W u) w = u.val w := rfl
    show repOf θ θL (θL ⟨l, hl⟩) w = u.val w
    rw [repOf_theta, ← h1]
    exact congrArg (fun f : W ≃ₗ[ZMod 2] W => f w) hlu

omit [Finite V] in
theorem repOf_isIrreducible (θ : V ≃* Multiplicative W) {L : Subgroup (MulAut V)}
    (θL : ↥L ≃* SL(2, F)) (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤) :
    (repOf θ θL).IsIrreducible := by
  have hirrV := CFSG.QuasithinUnique.Bridge.TypeList.irr_of_isIrrSec hirr
  have hntW : Nontrivial W := by
    obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hirr.1
    replace hv : v ≠ 1 := fun h => hv (h ▸ Subgroup.one_mem _)
    refine ⟨⟨Multiplicative.toAdd (θ v), 0, fun h => hv ?_⟩⟩
    have h1 : θ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  rw [isIrreducible_iff]
  refine ⟨hntW, fun U hU => B42L2.irr_map θ hirrV U ?_⟩
  rintro _ ⟨l, hl, rfl⟩ u hu
  have h := hU (θL ⟨l, hl⟩) u hu
  rwa [repOf_theta] at h

omit [Finite V] in
theorem natCard_fixed_toUnits_map (θ : V ≃* Multiplicative W) (A : Subgroup (MulAut V)) :
    Nat.card {w : W // ∀ a ∈ toUnits (A.map (binPsi θ).toMonoidHom), a.val w = w} =
      Nat.card (fixV A) := by
  refine (Nat.card_congr ?_).symm
  refine
    { toFun := fun v => ⟨Multiplicative.toAdd (θ v), fun a ha => ?_⟩
      invFun := fun w => ⟨θ.symm (Multiplicative.ofAdd w.1), fun b hb => ?_⟩
      left_inv := fun v => by
        apply Subtype.ext
        simp
      right_inv := fun w => by
        apply Subtype.ext
        simp }
  · obtain ⟨b, hb, hba⟩ := (mem_toUnits.mp ha)
    have h1 : a.val (Multiplicative.toAdd (θ v)) =
        (unitsEquiv (ZMod 2) W a) (Multiplicative.toAdd (θ v)) := rfl
    rw [h1, ← hba]
    show binPsi θ b (Multiplicative.toAdd (θ v)) = Multiplicative.toAdd (θ v)
    rw [B42L2.toAdd_binPsi, v.2 b hb]
  · have h := w.2 ((unitsEquiv (ZMod 2) W).symm (binPsi θ b)) (by
      rw [mem_toUnits, MulEquiv.apply_symm_apply]
      exact ⟨b, hb, rfl⟩)
    have h1 : ((unitsEquiv (ZMod 2) W).symm (binPsi θ b)).val w.1 = binPsi θ b w.1 := by
      have h2 : unitsEquiv (ZMod 2) W ((unitsEquiv (ZMod 2) W).symm (binPsi θ b)) =
          binPsi θ b := MulEquiv.apply_symm_apply _ _
      rw [← h2]
      rfl
    rw [h1, binPsi_apply] at h
    apply θ.injective
    apply Multiplicative.toAdd.injective
    simpa using h

end V

section Offender

variable {V : Type} [CommGroup V] {F : Type} [Field F] [Fintype F] [CharP F 2]

theorem twoF_class_of_offender {L : Subgroup (MulAut V)}
    (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤) {n : ℕ} (hn : 3 ≤ n)
    (hF : Fintype.card F = 2 ^ n) (θL : ↥L ≃* SL(2, F))
    {A : Subgroup (MulAut V)} (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut V))) (hA1 : A ≠ ⊥)
    (hA : IsElemAbelian2 A) (hoff : Nat.card V ≤ Nat.card A ^ 2 * Nat.card (fixV A))
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (θ : V ≃* Multiplicative W) :
    (Nat.card (EndRing (repOf θ θL)) = 2 ^ n ∧ Module.finrank (EndRing (repOf θ θL)) W = 2) ∨
      ∃ s, n = 2 * s ∧ Nat.card (EndRing (repOf θ θL)) = 2 ^ s ∧
        Module.finrank (EndRing (repOf θ θL)) W = 4 := by
  classical
  set A₀ := A.map (binPsi θ).toMonoidHom with hA₀
  have : CFSG.IsElementaryAbelian 2 ↥A₀ := (isElemAbelian2_iff_map θ A).1 hA
  have : CFSG.IsElementaryAbelian 2 ↥(toUnits A₀) :=
    isElementaryAbelian_of_equiv (toUnitsEquiv A₀) inferInstance
  have hcard : Nat.card ↥(toUnits A₀) = Nat.card A := by
    rw [natCard_toUnits, hA₀, Subgroup.card_map_of_injective (binPsi θ).injective]
  have hA1' : toUnits A₀ ≠ ⊥ := by
    intro h
    apply hA1
    rw [← Subgroup.card_eq_one, ← hcard, h, Subgroup.card_bot]
  have hAN' : toUnits A₀ ≤ Subgroup.normalizer
      ((repOf θ θL).toHomUnits.range : Set (Module.End (ZMod 2) W)ˣ) := by
    rw [repOf_range]
    apply toUnits_normalizer
    rw [hA₀, ← Subgroup.map_equiv_normalizer_eq L (binPsi θ)]
    exact Subgroup.map_mono hAN
  refine twoF_class hn hF (repOf θ θL) (repOf_injective θ θL) (repOf_isIrreducible θ θL hirr)
    (toUnits A₀) hA1' hAN' ?_
  rw [hcard, natCard_fixed_toUnits_map θ A, ← natCard_eq θ]
  exact hoff

end Offender

end CFSG.Quasithin.B45L2
