module

public import CFSG.RankThree.OddKernel.InvolutionDims
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.RankThree.OddKernel

open Module

variable {K : Type*} [Field K] {Y : Type*} [Group Y] {W : Type*} [AddCommGroup W] [Module K W]

@[expose] def IsIrreducibleFactor (α : Y →* (W ≃ₗ[K] W)) (U U' : Submodule K W) : Prop :=
  (∀ y, ∀ w ∈ U, α y w ∈ U) ∧ (∀ y, ∀ w ∈ U', α y w ∈ U') ∧ U < U' ∧
    ∀ X : Submodule K W, (∀ y, ∀ w ∈ X, α y w ∈ X) → U ≤ X → X ≤ U' → X = U ∨ X = U'

@[expose] def factorRel (α : Y →* (W ≃ₗ[K] W)) : SetRel (Submodule K W) (Submodule K W) :=
  {x | IsIrreducibleFactor α x.1 x.2}

@[expose] def toRep (α : Y →* (W ≃ₗ[K] W)) : Representation K Y W :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp α

@[expose] noncomputable def sectionRep (α : Y →* (W ≃ₗ[K] W)) {U U' : Submodule K W}
    (hU : ∀ y, ∀ w ∈ U, α y w ∈ U) (hU' : ∀ y, ∀ w ∈ U', α y w ∈ U') :
    Representation K Y (U' ⧸ U.comap U'.subtype) :=
  ((toRep α).subrepresentation U' fun y w hw => hU' y w hw).quotient (U.comap U'.subtype)
    fun y w hw => hU y w hw

theorem sectionRep_mk (α : Y →* (W ≃ₗ[K] W)) {U U' : Submodule K W}
    (hU : ∀ y, ∀ w ∈ U, α y w ∈ U) (hU' : ∀ y, ∀ w ∈ U', α y w ∈ U') (y : Y) (w : U') :
    sectionRep α hU hU' y (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk ⟨α y w, hU' y w w.2⟩ :=
  rfl

theorem sectionRep_mk_eq_mk_iff (α : Y →* (W ≃ₗ[K] W)) {U U' : Submodule K W}
    (hU : ∀ y, ∀ w ∈ U, α y w ∈ U) (hU' : ∀ y, ∀ w ∈ U', α y w ∈ U') (y : Y) (w : U') :
    sectionRep α hU hU' y (Submodule.Quotient.mk w) = Submodule.Quotient.mk w ↔
      α y w - w ∈ U := by
  rw [sectionRep_mk, Submodule.Quotient.eq, Submodule.mem_comap]
  rfl

theorem sectionRep_irreducible {α : Y →* (W ≃ₗ[K] W)} {U U' : Submodule K W}
    (h : IsIrreducibleFactor α U U') (Z : Submodule K (U' ⧸ U.comap U'.subtype))
    (hZ : ∀ y, ∀ v ∈ Z, sectionRep α h.1 h.2.1 y v ∈ Z) : Z = ⊥ ∨ Z = ⊤ := by
  obtain ⟨hU, hU', hlt, hirr⟩ := h
  let X : Submodule K W := (Z.comap (U.comap U'.subtype).mkQ).map U'.subtype
  have hmemX : ∀ w : U', (w : W) ∈ X ↔ Submodule.Quotient.mk w ∈ Z := by
    intro w
    constructor
    · rintro ⟨w', hw', hww'⟩
      rw [Subtype.ext hww'] at hw'
      exact hw'
    · intro hw
      exact Submodule.mem_map.2 ⟨w, hw, rfl⟩
  have hUX : U ≤ X := by
    intro u hu
    refine (hmemX ⟨u, hlt.le hu⟩).2 ?_
    rw [(Submodule.Quotient.mk_eq_zero (U.comap U'.subtype) (x := ⟨u, hlt.le hu⟩)).2 hu]
    exact Z.zero_mem
  have hXU' : X ≤ U' := Submodule.map_subtype_le _ _
  have hXinv : ∀ y, ∀ w ∈ X, α y w ∈ X := by
    intro y w hw
    obtain ⟨w, -, rfl⟩ := Submodule.mem_map.1 hw
    have hw' := (hmemX w).1 hw
    exact (hmemX ⟨α y w, hU' y w w.2⟩).2 (hZ y _ hw')
  rcases hirr X hXinv hUX hXU' with hXe | hXe
  · left
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ v
    have hwX : (w : W) ∈ X := (hmemX w).2 hv
    rw [hXe] at hwX
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hwX
  · right
    rw [eq_top_iff]
    rintro v -
    obtain ⟨w, hw⟩ := Submodule.mkQ_surjective _ v
    rw [← hw]
    have hwX : (w : W) ∈ X := by rw [hXe]; exact w.2
    exact (hmemX w).1 hwX

theorem exists_ne_zero_fixed {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup p Q) {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    [Nontrivial V] (ρ : Representation (ZMod p) Q V) : ∃ v : V, v ≠ 0 ∧ ∀ q, ρ q v = v := by
  let _ : MulAction Q V := MulAction.compHom V ρ
  have : Finite V := Module.finite_of_finite (ZMod p)
  have hcard : p ∣ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    exact dvd_pow_self p (Module.finrank_pos (R := ZMod p) (M := V)).ne'
  have h0 : (0 : V) ∈ MulAction.fixedPoints Q V := fun q => map_zero (ρ q)
  obtain ⟨v, hv, hne⟩ := hQ.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hcard h0
  exact ⟨v, hne.symm, fun q => hv q⟩

theorem finrank_eq_of_trivial_factor [FiniteDimensional K W] {α : Y →* (W ≃ₗ[K] W)}
    {U U' : Submodule K W} (h : IsIrreducibleFactor α U U')
    (htriv : ∀ y, ∀ w ∈ U', α y w - w ∈ U) : finrank K U' = finrank K U + 1 := by
  obtain ⟨-, -, hlt, hirr⟩ := h
  obtain ⟨w, hwU', hwU⟩ := IsConcreteLE.exists_of_lt hlt
  set X := U ⊔ Submodule.span K {w} with hX
  have hXinv : ∀ y, ∀ x ∈ X, α y x ∈ X := by
    intro y x hx
    have hxU' : x ∈ U' := sup_le hlt.le ((Submodule.span_singleton_le_iff_mem _ _).2 hwU') hx
    have : α y x = x + (α y x - x) := by abel
    rw [this]
    exact X.add_mem hx (Submodule.mem_sup_left (htriv y x hxU'))
  have hUX : U ≤ X := le_sup_left
  have hXU' : X ≤ U' := sup_le hlt.le ((Submodule.span_singleton_le_iff_mem _ _).2 hwU')
  rcases hirr X hXinv hUX hXU' with hXe | hXe
  · exact absurd (hXe ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self w)) hwU
  · have h1 := Submodule.finrank_add_le_finrank_add_finrank U (Submodule.span K {w})
    rw [← hX, hXe] at h1
    have hw0 : w ≠ 0 := fun h0 => hwU (h0 ▸ U.zero_mem)
    rw [finrank_span_singleton hw0] at h1
    have h3 := Submodule.finrank_lt_finrank_of_lt hlt
    omega

theorem apply_inv_apply (α : Y →* (W ≃ₗ[K] W)) (g : Y) (x : W) : α g (α g⁻¹ x) = x := by
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem inv_apply_apply (α : Y →* (W ≃ₗ[K] W)) (g : Y) (x : W) : α g⁻¹ (α g x) = x := by
  rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

theorem conj_apply (α : Y →* (W ≃ₗ[K] W)) (g t : Y) (x : W) :
    α (g * t * g⁻¹) x = α g (α t (α g⁻¹ x)) := by
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]

theorem finrank_inf_fixSpace_conj [FiniteDimensional K W] (α : Y →* (W ≃ₗ[K] W))
    {X : Submodule K W} (hX : ∀ y, ∀ w ∈ X, α y w ∈ X) (g t : Y) :
    finrank K ↥(X ⊓ fixSpace (α (g * t * g⁻¹)).toLinearMap) =
      finrank K ↥(X ⊓ fixSpace (α t).toLinearMap) := by
  have hmap : (X ⊓ fixSpace (α t).toLinearMap).map (α g).toLinearMap =
      X ⊓ fixSpace (α (g * t * g⁻¹)).toLinearMap := by
    ext v
    simp only [Submodule.mem_map, Submodule.mem_inf, mem_fixSpace, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨x, ⟨hx, hxt⟩, rfl⟩
      refine ⟨hX g x hx, ?_⟩
      rw [conj_apply, inv_apply_apply, hxt]
    · rintro ⟨hv, hvt⟩
      refine ⟨α g⁻¹ v, ⟨hX _ v hv, ?_⟩, apply_inv_apply α g v⟩
      rw [conj_apply] at hvt
      have := congrArg (α g⁻¹) hvt
      rwa [inv_apply_apply] at this
  rw [← hmap, LinearEquiv.finrank_map_eq]

theorem exists_relSeries_factorRel [FiniteDimensional K W] (α : Y →* (W ≃ₗ[K] W))
    (U' : Submodule K W) (hU' : ∀ y, ∀ w ∈ U', α y w ∈ U') :
    ∃ s : RelSeries (factorRel α), s.head = ⊥ ∧ s.last = U' := by
  induction hn : finrank K U' using Nat.strong_induction_on generalizing U' with
  | _ n ih =>
  by_cases hbot : U' = ⊥
  · exact ⟨RelSeries.singleton _ ⊥, rfl, hbot.symm⟩
  · let M : Set (Submodule K W) := {X | (∀ y, ∀ w ∈ X, α y w ∈ X) ∧ X < U'}
    have hM : M.Nonempty := ⟨⊥, fun y w hw => by
      rw [Submodule.mem_bot] at hw ⊢
      rw [hw, map_zero], bot_lt_iff_ne_bot.2 hbot⟩
    obtain ⟨X, ⟨hXinv, hXlt⟩, hXmax⟩ := set_has_maximal_iff_noetherian.2 inferInstance M hM
    have hfac : IsIrreducibleFactor α X U' := by
      refine ⟨hXinv, hU', hXlt, fun Z hZ hXZ hZU' => ?_⟩
      by_cases hZe : Z = U'
      · exact Or.inr hZe
      · exact Or.inl (eq_of_le_of_not_lt hXZ (hXmax Z ⟨hZ, lt_of_le_of_ne hZU' hZe⟩)).symm
    obtain ⟨s, hs0, hsl⟩ := ih (finrank K X) (hn ▸ Submodule.finrank_lt_finrank_of_lt hXlt) X
      hXinv rfl
    refine ⟨s.snoc U' ?_, by rw [RelSeries.head_snoc, hs0], RelSeries.last_snoc _ _ _⟩
    show IsIrreducibleFactor α s.last U'
    rw [hsl]
    exact hfac

end CFSG.RankThree.OddKernel
