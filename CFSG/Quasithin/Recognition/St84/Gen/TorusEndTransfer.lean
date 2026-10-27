module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDensity

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.QuasithinUnique.Setup.SL2Modules

private def centralizer {R G W : Type*} [Semiring R] [Monoid G] [AddCommGroup W]
    [Module R W] (ρ : Representation R G W) : Subgroup (W ≃ₗ[R] W) where
  carrier := {φ | ∀ g w, φ (ρ g w) = ρ g (φ w)}
  one_mem' := by
    intro g w
    rfl
  mul_mem' := by
    intro φ ψ hφ hψ g w
    simp only [LinearEquiv.mul_apply]
    rw [hψ g w, hφ g (ψ w)]
  inv_mem' := by
    intro φ hφ g w
    change φ.symm (ρ g w) = ρ g (φ.symm w)
    apply φ.injective
    rw [LinearEquiv.apply_symm_apply, hφ g (φ.symm w), LinearEquiv.apply_symm_apply]

private theorem mem_centralizer {R G W : Type*} [Semiring R] [Monoid G] [AddCommGroup W]
    [Module R W] {ρ : Representation R G W} {φ : W ≃ₗ[R] W} :
    φ ∈ centralizer ρ ↔ ∀ g w, φ (ρ g w) = ρ g (φ w) := Iff.rfl

private noncomputable def centralizerToUnits {R G W : Type*} [Field R] [Monoid G]
    [AddCommGroup W] [Module R W] (ρ : Representation R G W) (φ : centralizer ρ) :
    (EndRing ρ)ˣ := by
  classical
  let h : ∃ ψ : EndRing ρ, (ψ : W → W) = (φ : W ≃ₗ[R] W).toLinearMap :=
    (mem_endRing_iff ρ (φ : W ≃ₗ[R] W).toLinearMap).mpr φ.2
  let ψ : EndRing ρ := Classical.choose h
  have hψ : (ψ : W → W) = (φ : W ≃ₗ[R] W).toLinearMap := Classical.choose_spec h
  have hunit : IsUnit ψ := (Module.End.isUnit_iff ψ).mpr (by
    simpa [hψ] using (φ : W ≃ₗ[R] W).bijective)
  exact hunit.unit

private theorem centralizerToUnits_apply {R G W : Type*} [Field R] [Monoid G]
    [AddCommGroup W] [Module R W] (ρ : Representation R G W) (φ : centralizer ρ) (w : W) :
    (centralizerToUnits ρ φ : EndRing ρ) w = (φ : W ≃ₗ[R] W) w := by
  classical
  unfold centralizerToUnits
  rw [IsUnit.unit_spec]
  change (Classical.choose
    ((mem_endRing_iff ρ (φ : W ≃ₗ[R] W).toLinearMap).mpr φ.2) : EndRing ρ) w =
    (φ : W ≃ₗ[R] W) w
  exact congrFun (Classical.choose_spec
    ((mem_endRing_iff ρ (φ : W ≃ₗ[R] W).toLinearMap).mpr φ.2)) w

private noncomputable def unitsToCentralizer {R G W : Type*} [Field R] [Monoid G]
    [AddCommGroup W] [Module R W] (ρ : Representation R G W) (u : (EndRing ρ)ˣ) :
    centralizer ρ := by
  classical
  let f : W →ₗ[R] W := (u : EndRing ρ).restrictScalars R
  let g : W →ₗ[R] W := ((u⁻¹ : (EndRing ρ)ˣ) : EndRing ρ).restrictScalars R
  refine ⟨{
    toFun := f
    invFun := g
    left_inv := ?_
    right_inv := ?_
    map_add' := f.map_add
    map_smul' := f.map_smul }, ?_⟩
  · intro w
    have h : (((u⁻¹ : (EndRing ρ)ˣ) : EndRing ρ) * (u : EndRing ρ)) = 1 := by simp
    have hw := congrArg (fun e : EndRing ρ => e w) h
    show ((u⁻¹ : (EndRing ρ)ˣ) : EndRing ρ) ((u : EndRing ρ) w) = w
    simpa only [Module.End.mul_apply, Module.End.one_apply] using hw
  · intro w
    have h : ((u : EndRing ρ) * ((u⁻¹ : (EndRing ρ)ˣ) : EndRing ρ)) = 1 := by simp
    have hw := congrArg (fun e : EndRing ρ => e w) h
    show (u : EndRing ρ) (((u⁻¹ : (EndRing ρ)ˣ) : EndRing ρ) w) = w
    simpa only [Module.End.mul_apply, Module.End.one_apply] using hw
  · intro g' w
    have h := (u : EndRing ρ).map_smul
      (⟨ρ g', Algebra.subset_adjoin ⟨g', rfl⟩⟩ : spanAlg ρ) w
    change f (ρ g' w) = ρ g' (f w)
    simpa only [f, Subalgebra.smul_def, Module.End.smul_def,
      LinearMap.coe_restrictScalars] using h

private theorem unitsToCentralizer_apply {R G W : Type*} [Field R] [Monoid G]
    [AddCommGroup W] [Module R W] (ρ : Representation R G W) (u : (EndRing ρ)ˣ) (w : W) :
    (unitsToCentralizer ρ u : W ≃ₗ[R] W) w = (u : EndRing ρ) w := rfl

private theorem unitsToCentralizer_centralizerToUnits {R G W : Type*} [Field R] [Monoid G]
    [AddCommGroup W] [Module R W] (ρ : Representation R G W) (φ : centralizer ρ) :
    unitsToCentralizer ρ (centralizerToUnits ρ φ) = φ := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro w
  rw [unitsToCentralizer_apply, centralizerToUnits_apply]

private theorem centralizerToUnits_unitsToCentralizer {R G W : Type*} [Field R] [Monoid G]
    [AddCommGroup W] [Module R W] (ρ : Representation R G W) (u : (EndRing ρ)ˣ) :
    centralizerToUnits ρ (unitsToCentralizer ρ u) = u := by
  apply Units.ext
  apply LinearMap.ext
  intro w
  rw [centralizerToUnits_apply, unitsToCentralizer_apply]

private theorem unitsToCentralizer_bijective {R G W : Type*} [Field R] [Monoid G]
    [AddCommGroup W] [Module R W] (ρ : Representation R G W) :
    Function.Bijective (unitsToCentralizer ρ) := by
  refine ⟨fun u v h => ?_, fun φ => ⟨centralizerToUnits ρ φ,
    unitsToCentralizer_centralizerToUnits ρ φ⟩⟩
  have h' := congrArg (centralizerToUnits ρ) h
  rwa [centralizerToUnits_unitsToCentralizer, centralizerToUnits_unitsToCentralizer] at h'

private theorem natCard_centralizer {R G W : Type*} [Field R] [Monoid G]
    [AddCommGroup W] [Module R W] (ρ : Representation R G W) [Fact ρ.IsIrreducible]
    [Finite W] : Nat.card (centralizer ρ) = Nat.card (EndRing ρ) - 1 := by
  calc
    Nat.card (centralizer ρ) =
        Nat.card ((EndRing ρ)ˣ) :=
      Nat.card_congr (Equiv.ofBijective (unitsToCentralizer ρ)
        (unitsToCentralizer_bijective ρ)).symm
    _ = Nat.card (EndRing ρ) - 1 := Nat.card_units (EndRing ρ)

section Transfer

variable {K K' W W' : Type*} [Group K] [Group K']
  [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup W'] [Module (ZMod 2) W']

private noncomputable def conjCentralizer
    (ρ : Representation (ZMod 2) K W) (ρ' : Representation (ZMod 2) K' W')
    (eK : K ≃* K') (f₀ : W ≃ₗ[ZMod 2] W')
    (hf₀ : ∀ k w, f₀ (ρ k w) = ρ' (eK k) (f₀ w)) :
    centralizer ρ →* centralizer ρ' where
  toFun φ := ⟨f₀.symm.trans ((φ : W ≃ₗ[ZMod 2] W).trans f₀), by
    intro k' w'
    obtain ⟨k, rfl⟩ := eK.surjective k'
    have hsymm : f₀.symm (ρ' (eK k) w') = ρ k (f₀.symm w') := by
      simpa using (congrArg f₀.symm (hf₀ k (f₀.symm w'))).symm
    simp only [LinearEquiv.trans_apply]
    rw [hsymm, φ.2 k (f₀.symm w'), hf₀ k ((φ : W ≃ₗ[ZMod 2] W) (f₀.symm w'))]⟩
  map_one' := by
    apply Subtype.ext
    ext w
    simp [LinearEquiv.trans_apply]
  map_mul' φ ψ := by
    apply Subtype.ext
    ext w
    simp [LinearEquiv.mul_apply, LinearEquiv.trans_apply]

private theorem conjCentralizer_apply
    (ρ : Representation (ZMod 2) K W) (ρ' : Representation (ZMod 2) K' W')
    (eK : K ≃* K') (f₀ : W ≃ₗ[ZMod 2] W')
    (hf₀ : ∀ k w, f₀ (ρ k w) = ρ' (eK k) (f₀ w)) (φ : centralizer ρ) :
    (conjCentralizer ρ ρ' eK f₀ hf₀ φ : W' ≃ₗ[ZMod 2] W') =
      f₀.symm.trans ((φ : W ≃ₗ[ZMod 2] W).trans f₀) := rfl

private theorem conjCentralizer_injective
    (ρ : Representation (ZMod 2) K W) (ρ' : Representation (ZMod 2) K' W')
    (eK : K ≃* K') (f₀ : W ≃ₗ[ZMod 2] W')
    (hf₀ : ∀ k w, f₀ (ρ k w) = ρ' (eK k) (f₀ w)) :
    Function.Injective (conjCentralizer ρ ρ' eK f₀ hf₀) := by
  intro φ ψ h
  apply Subtype.ext
  ext w
  have h' : (conjCentralizer ρ ρ' eK f₀ hf₀ φ : W' ≃ₗ[ZMod 2] W') =
      (conjCentralizer ρ ρ' eK f₀ hf₀ ψ : W' ≃ₗ[ZMod 2] W') :=
    congrArg (fun e : centralizer ρ' => (e : W' ≃ₗ[ZMod 2] W')) h
  have hw := congrArg (fun e : W' ≃ₗ[ZMod 2] W' => e (f₀ w)) h'
  apply f₀.injective
  simpa [conjCentralizer_apply, LinearEquiv.trans_apply] using hw

theorem exists_mulEquiv_of_commute_of_card {K K' H H' W W' : Type*} [Group K] [Group K']
    [Group H] [Group H'] [Finite H] [Finite H']
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [AddCommGroup W'] [Module (ZMod 2) W'] [Finite W']
    (ρ : Representation (ZMod 2) K W) (ρ' : Representation (ZMod 2) K' W')
    [Fact ρ.IsIrreducible] [Fact ρ'.IsIrreducible]
    (eK : K ≃* K') (f₀ : W ≃ₗ[ZMod 2] W') (hf₀ : ∀ k w, f₀ (ρ k w) = ρ' (eK k) (f₀ w))
    (τ : H →* (W ≃ₗ[ZMod 2] W)) (τ' : H' →* (W' ≃ₗ[ZMod 2] W'))
    (hτ : Function.Injective τ) (hτ' : Function.Injective τ')
    (hτρ : ∀ h k w, τ h (ρ k w) = ρ k (τ h w)) (hτρ' : ∀ h k w, τ' h (ρ' k w) = ρ' k (τ' h w))
    (hcard : Nat.card (EndRing ρ) = Nat.card H + 1)
    (hcard' : Nat.card (EndRing ρ') = Nat.card H' + 1) :
    ∃ eH : H ≃* H', ∀ h w, f₀ (τ h w) = τ' (eH h) (f₀ w) := by
  classical
  let C := centralizer ρ
  let C' := centralizer ρ'
  let τC : H →* C :=
    { toFun := fun h => ⟨τ h, mem_centralizer.mpr (hτρ h)⟩
      map_one' := Subtype.ext (map_one τ)
      map_mul' := fun h h' => Subtype.ext (map_mul τ h h') }
  let τC' : H' →* C' :=
    { toFun := fun h => ⟨τ' h, mem_centralizer.mpr (hτρ' h)⟩
      map_one' := Subtype.ext (map_one τ')
      map_mul' := fun h h' => Subtype.ext (map_mul τ' h h') }
  have hτCin : Function.Injective τC := by
    intro h h' hh
    exact hτ (congrArg Subtype.val hh)
  have hτC'in : Function.Injective τC' := by
    intro h h' hh
    exact hτ' (congrArg Subtype.val hh)
  haveI hEndFin : Finite (EndRing ρ) := finite_endRing ρ
  haveI hEndFin' : Finite (EndRing ρ') := finite_endRing ρ'
  haveI hCfin : Finite C :=
    Finite.ofBijective (unitsToCentralizer_bijective ρ)
  haveI hC'fin : Finite C' :=
    Finite.ofBijective (unitsToCentralizer_bijective ρ')
  have hcardC : Nat.card C = Nat.card H := by
    change Nat.card (centralizer ρ) = Nat.card H
    rw [natCard_centralizer ρ, hcard]
    omega
  have hcardC' : Nat.card C' = Nat.card H' := by
    change Nat.card (centralizer ρ') = Nat.card H'
    rw [natCard_centralizer ρ', hcard']
    omega
  have hτCbij : Function.Bijective τC :=
    (Nat.bijective_iff_injective_and_card τC).mpr ⟨hτCin, hcardC.symm⟩
  have hτC'bij : Function.Bijective τC' :=
    (Nat.bijective_iff_injective_and_card τC').mpr ⟨hτC'in, hcardC'.symm⟩
  let conjC : C →* C' := conjCentralizer ρ ρ' eK f₀ hf₀
  have hconjInj : Function.Injective conjC := conjCentralizer_injective ρ ρ' eK f₀ hf₀
  have hf₀' : ∀ k' w', f₀.symm (ρ' k' w') = ρ (eK.symm k') (f₀.symm w') := by
    intro k' w'
    simpa using (congrArg f₀.symm (hf₀ (eK.symm k') (f₀.symm w'))).symm
  let conjC' : C' →* C := conjCentralizer ρ' ρ eK.symm f₀.symm hf₀'
  have hconjInj' : Function.Injective conjC' :=
    conjCentralizer_injective ρ' ρ eK.symm f₀.symm hf₀'
  have hconjCard : Nat.card C = Nat.card C' :=
    le_antisymm (Nat.card_le_card_of_injective conjC hconjInj)
      (Nat.card_le_card_of_injective conjC' hconjInj')
  have hconjBij : Function.Bijective conjC :=
    (Nat.bijective_iff_injective_and_card conjC).mpr ⟨hconjInj, hconjCard⟩
  let eH : H ≃* H' :=
    (MulEquiv.ofBijective τC hτCbij).trans
      ((MulEquiv.ofBijective conjC hconjBij).trans
        (MulEquiv.ofBijective τC' hτC'bij).symm)
  refine ⟨eH, ?_⟩
  intro h w
  have h_eH : τC' (eH h) = conjC (τC h) := by
    simp [eH]
  have hval : (τ' (eH h) : W' ≃ₗ[ZMod 2] W') =
      (conjC (τC h) : W' ≃ₗ[ZMod 2] W') := congrArg Subtype.val h_eH
  rw [hval, conjCentralizer_apply]
  change f₀ (τ h w) =
    (f₀.symm.trans (((τC h : C) : W ≃ₗ[ZMod 2] W).trans f₀)) (f₀ w)
  have hτCval : (τC h : W ≃ₗ[ZMod 2] W) = τ h := rfl
  rw [hτCval]
  simp [LinearEquiv.trans_apply]

end Transfer

end CFSG.Quasithin.F112R.St84
