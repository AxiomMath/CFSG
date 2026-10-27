module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueFieldTorus

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.Timmesfeld.ExceptionalOrders (zpowMatrix zpowMatrix_apply)

section Tuples

variable {K : Type} [Field K] {σ : K →+* K}

theorem cartanChar_eq_zpowMatrix {τ : Tag} (c : Fin τ.rank → Kˣ) :
    cartanChar c = zpowMatrix τ.cartan c :=
  funext fun _ => rfl

theorem monomialHom_transpose_eq_cartanChar {τ : Tag} (c : Fin τ.rank → Kˣ) :
    monomialHom τ.cartan.transpose c = cartanChar c := by
  funext l
  rw [monomialHom_apply]
  rfl

theorem units_map_units_map_of_involutive (hσσ : ∀ c, σ (σ c) = c) (u : Kˣ) :
    Units.map σ.toMonoidHom (Units.map σ.toMonoidHom u) = u :=
  Units.ext (hσσ (u : K))

theorem cartanChar_graphFieldTuple (c : Fin TwistTag.E6.tag.rank → Kˣ)
    (l : Fin TwistTag.E6.tag.rank) :
    cartanChar (fun i => Units.map σ.toMonoidHom (c (TwistTag.E6.perm i))) l =
      Units.map σ.toMonoidHom (cartanChar c (TwistTag.E6.perm l)) := by
  unfold cartanChar
  rw [map_prod]
  simp only [map_zpow]
  exact Fintype.prod_equiv TwistTag.E6.perm _ _ fun j => by rw [TwistTag.cartan_perm]

theorem cartanChar_graphFieldTuple_eq (hσσ : ∀ c, σ (σ c) = c)
    {c : Fin TwistTag.E6.tag.rank → Kˣ}
    (hl : ∀ i, cartanChar c (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (cartanChar c i)) :
    cartanChar (fun i => Units.map σ.toMonoidHom (c (TwistTag.E6.perm i))) = cartanChar c := by
  funext l
  rw [cartanChar_graphFieldTuple, hl, units_map_units_map_of_involutive hσσ]

theorem pow_three_eq_one_of_cartanChar_eq_one {x : Fin TwistTag.E6.tag.rank → Kˣ}
    (hx : cartanChar x = 1) : x ^ 3 = 1 := by
  rw [cartanChar_eq_zpowMatrix] at hx
  obtain ⟨ζ, hζ, rfl⟩ :=
    CFSG.Timmesfeld.ExceptionalOrders.mem_ker_zpowMatrix_twistedE6.1 (MonoidHom.mem_ker.2 hx)
  funext j
  rw [Pi.pow_apply, Pi.one_apply, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
    hζ, one_zpow]

theorem sq_mul_inv_eq_of_pow_three_eq {a b : Kˣ} (h : a ^ 3 = b ^ 3) :
    a ^ 2 * b⁻¹ = b ^ 2 * a⁻¹ := by
  have ha := a.ne_zero
  have hb := b.ne_zero
  have h' := congrArg Units.val h
  apply Units.ext
  push_cast at h' ⊢
  field_simp
  linear_combination h'

theorem compat_descendTuple (hσσ : ∀ c, σ (σ c) = c) {c : Fin TwistTag.E6.tag.rank → Kˣ}
    (hl : ∀ i, cartanChar c (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (cartanChar c i)) :
    (∀ i, (c ^ 2 * (fun i => Units.map σ.toMonoidHom (c (TwistTag.E6.perm i)))⁻¹)
        (TwistTag.E6.perm i) = Units.map σ.toMonoidHom
          ((c ^ 2 * (fun i => Units.map σ.toMonoidHom (c (TwistTag.E6.perm i)))⁻¹) i)) ∧
      cartanChar (c ^ 2 * (fun i => Units.map σ.toMonoidHom (c (TwistTag.E6.perm i)))⁻¹) =
        cartanChar c := by
  set Fc : Fin TwistTag.E6.tag.rank → Kˣ :=
    fun i => Units.map σ.toMonoidHom (c (TwistTag.E6.perm i)) with hFc
  have hχ : cartanChar Fc = cartanChar c := cartanChar_graphFieldTuple_eq hσσ hl
  have hx : cartanChar (Fc * c⁻¹) = 1 := by
    rw [cartanChar_eq_zpowMatrix, map_mul, map_inv, ← cartanChar_eq_zpowMatrix,
      ← cartanChar_eq_zpowMatrix, hχ, mul_inv_cancel]
  have hx3 := pow_three_eq_one_of_cartanChar_eq_one hx
  have hpp : ∀ i, TwistTag.E6.perm (TwistTag.E6.perm i) = i := by decide
  refine ⟨fun i => ?_, ?_⟩
  · have h3 := congrFun hx3 (TwistTag.E6.perm i)
    simp only [Pi.pow_apply, Pi.mul_apply, Pi.inv_apply, Pi.one_apply, hFc, hpp] at h3 ⊢
    rw [map_mul, map_inv, map_pow, units_map_units_map_of_involutive hσσ]
    rw [mul_pow, inv_pow, mul_inv_eq_one] at h3
    exact sq_mul_inv_eq_of_pow_three_eq h3.symm
  · rw [cartanChar_eq_zpowMatrix, map_mul, map_inv, map_pow, ← cartanChar_eq_zpowMatrix,
      ← cartanChar_eq_zpowMatrix, hχ, sq, mul_inv_cancel_right]

end Tuples

section Fixed


variable {K : Type} [Field K]

theorem graphFixedTorus_le_graphFixedRootGroup_twistedE6 {σ : K →+* K}
    (hσσ : ∀ c, σ (σ c) = c) :
    graphFixedTorus TwistTag.E6 K σ ≤ graphFixedRootGroup TwistTag.E6 K σ := by
  intro h hh
  obtain ⟨hhT, hhΓ⟩ := Subgroup.mem_inf.1 hh
  obtain ⟨c, rfl⟩ :=
    E6Pilot.torusGroup_le_range_rootDiagUnit_monomial (K := K) TwistTag.E6.tag hhT
  have hh' : ((rootDiagUnitHom TwistTag.E6.tag K).comp
      (monomialHom TwistTag.E6.tag.cartan.transpose)) c =
        rootDiagUnit TwistTag.E6.tag (cartanChar c) := by
    rw [MonoidHom.comp_apply, monomialHom_transpose_eq_cartanChar]
    rfl
  rw [hh'] at hhΓ ⊢
  have hl := compat_of_twistHom_rootDiagUnit
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ).1 hhΓ).2
  obtain ⟨hcompat, hchar⟩ := compat_descendTuple hσσ hl
  obtain ⟨w, hw⟩ := exists_compatDiag_eq hcompat
  rw [← hchar, ← hw, ← list_prod_orbitH_eq_rootDiagUnit]
  exact Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact orbitH_mem_graphFixedRootGroup _ _ _ _

theorem twistedFixedGroup_eq_graphFixedRootGroup_twistedE6 {σ : K →+* K}
    (hσσ : ∀ c, σ (σ c) = c) :
    twistedFixedGroup TwistTag.E6 K σ = graphFixedRootGroup TwistTag.E6 K σ := by
  refine le_antisymm (fun g hg => ?_) (graphFixedRootGroup_le _ _ _)
  have hσs : Function.Surjective σ := fun c => ⟨σ c, hσσ c⟩
  have hg' : g ∈ (twistedFixedGroup TwistTag.E6 K σ : Set (ModGL TwistTag.E6.tag K)) := hg
  rw [coe_twistedFixedGroup_eq_mul hσs] at hg'
  obtain ⟨h, hh, c, hc, rfl⟩ := hg'
  exact mul_mem (graphFixedTorus_le_graphFixedRootGroup_twistedE6 hσσ hh) hc

theorem fixSubgroup_graphField_eq_twistedE6 (σ : K ≃+* K) (hσσ : ∀ c, σ (σ c) = c) :
    E6Pilot.fixSubgroup (diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σ) =
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subgroupOf
        (adjointGroup TwistTag.E6.tag K) := by
  rw [← twistedFixedGroup_eq_graphFixedRootGroup_twistedE6 (σ := σ.toRingHom) hσσ,
    twistedFixedGroup_subgroupOf]
  unfold E6Pilot.fixSubgroup
  congr 1
  refine MonoidHom.ext fun g => Subtype.ext ?_
  rw [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, coe_diagramConjAut, coe_entrywiseAdjointAut,
    coe_twistC, twistHom_apply]

theorem sigma_apply_apply_of_sq_eq_one_twistedE6 {σ : K ≃+* K} (hσ2 : σ ^ 2 = 1) (c : K) :
    σ (σ c) = c := by
  have h := congrArg (fun φ : K ≃+* K => φ c) hσ2
  simpa only [pow_two, RingAut.mul_apply, RingAut.one_apply] using h


theorem fixSubgroup_graphField_perfect_card_twistedE6 {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ (2 * f)) (σ : K ≃+* K) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) :
    ⁅E6Pilot.fixSubgroup (diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σ),
        E6Pilot.fixSubgroup
          (diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σ)⁆ =
      E6Pilot.fixSubgroup (diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σ) ∧
    Nat.card (E6Pilot.fixSubgroup
      (diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σ)) =
        ordTwistedE6 (2 ^ f) := by
  obtain ⟨-, hperf, hcard⟩ := E6Pilot.commutator_fixSubgroup_graphField_E6 hf hK σ hσ2 hσ1
  rw [fixSubgroup_graphField_eq_twistedE6 σ (sigma_apply_apply_of_sq_eq_one_twistedE6 hσ2)]
  exact ⟨hperf, hcard⟩

end Fixed

end CFSG.SeitzReduction.TwistedE6Pilot
