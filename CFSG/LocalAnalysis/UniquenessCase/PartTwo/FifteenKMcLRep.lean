module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKMcLDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem s15k_mcl_nonempty {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {J : Subgroup (MulAut W)} {R : Subgroup W} (hst : StableUnder J R)
    (hfaith : ∀ j ∈ J, (∀ r ∈ R, j r = r) → j = 1) : Nonempty (McRep J R) := by
  have h2 : ∀ x : Additive ↥R, (2 : ℕ) • x = 0 := fun x => by
    apply Additive.toMul.injective
    show (Additive.toMul x) ^ 2 = 1
    exact Subtype.ext (hW _)
  letI : Module (ZMod 2) (Additive ↥R) := AddCommGroup.zmodModule h2
  let rest : ↥J → (Additive ↥R →+ Additive ↥R) := fun j =>
    { toFun := fun x => Additive.ofMul ⟨(j : MulAut W) (Additive.toMul x : ↥R),
        hst j j.2 _ (Additive.toMul x).2⟩
      map_zero' := by
        apply Additive.toMul.injective
        exact Subtype.ext (map_one _)
      map_add' := fun x y => by
        apply Additive.toMul.injective
        exact Subtype.ext (map_mul _ _ _) }
  let T : ↥J →* Module.End (ZMod 2) (Additive ↥R) :=
    { toFun := fun j => (rest j).toZModLinearMap 2
      map_one' := by
        apply LinearMap.ext
        intro x
        rfl
      map_mul' := fun a b => by
        apply LinearMap.ext
        intro x
        rfl }
  let eR : ↥R ≃* Multiplicative (Additive ↥R) :=
    { toFun := fun r => Multiplicative.ofAdd (Additive.ofMul r)
      invFun := fun x => Additive.toMul (Multiplicative.toAdd x)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨⟨Additive ↥R, eR, T.toHomUnits, hst, ?_, ?_⟩⟩
  · intro j r hr
    rfl
  · rw [injective_iff_map_eq_one]
    intro j hj
    apply Subtype.ext
    apply hfaith j j.2
    intro r hr
    have h1 := congrArg (fun u : LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥R) =>
      (u : Additive ↥R →ₗ[ZMod 2] Additive ↥R) (Additive.ofMul ⟨r, hr⟩)) hj
    have h3 := congrArg Additive.toMul h1
    exact congrArg Subtype.val h3

theorem s15k_mcl_irr {W : Type} [CommGroup W] {J : Subgroup (MulAut W)} {R : Subgroup W}
    (D : McRep J R) (h : IsIrrOn J R ⊥) :
    ∀ U : Submodule (ZMod 2) D.V,
      (∀ g ∈ D.ρ.range, ∀ w ∈ U, (g : D.V →ₗ[ZMod 2] D.V) w ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro U hU
  let U' : Subgroup W :=
    { carrier := {w | ∃ hw : w ∈ R, Multiplicative.toAdd (D.e ⟨w, hw⟩) ∈ U}
      one_mem' := ⟨R.one_mem, by
        rw [show (⟨1, R.one_mem⟩ : ↥R) = 1 from rfl, map_one, toAdd_one]
        exact U.zero_mem⟩
      mul_mem' := by
        rintro a b ⟨ha, hUa⟩ ⟨hb, hUb⟩
        refine ⟨R.mul_mem ha hb, ?_⟩
        have : (⟨a * b, R.mul_mem ha hb⟩ : ↥R) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
        rw [this, map_mul, toAdd_mul]
        exact U.add_mem hUa hUb
      inv_mem' := by
        rintro a ⟨ha, hUa⟩
        refine ⟨R.inv_mem ha, ?_⟩
        have : (⟨a⁻¹, R.inv_mem ha⟩ : ↥R) = (⟨a, ha⟩ : ↥R)⁻¹ := rfl
        rw [this, map_inv, toAdd_inv]
        exact U.neg_mem hUa }
  have hU'R : U' ≤ R := fun w hw => hw.1
  have hst : StableUnder J U' := by
    rintro x hx u ⟨hu, hUu⟩
    refine ⟨D.stable x hx u hu, ?_⟩
    have := D.hρ ⟨x, hx⟩ ⟨u, hu⟩ (D.stable x hx u hu)
    rw [this, toAdd_ofAdd]
    exact hU _ ⟨⟨x, hx⟩, rfl⟩ _ hUu
  rcases h.2.2.2 U' hst bot_le hU'R with h0 | h1
  · left
    rw [eq_bot_iff]
    intro x hx
    have hmem : (D.e.symm (Multiplicative.ofAdd x) : W) ∈ U' := by
      refine ⟨(D.e.symm (Multiplicative.ofAdd x)).2, ?_⟩
      simpa using hx
    rw [h0, Subgroup.mem_bot] at hmem
    have : D.e.symm (Multiplicative.ofAdd x) = 1 := Subtype.ext hmem
    have h' := congrArg D.e this
    rw [MulEquiv.apply_symm_apply, map_one] at h'
    have h'' := congrArg Multiplicative.toAdd h'
    simpa using h''
  · right
    rw [eq_top_iff]
    intro x _
    have hmem : (D.e.symm (Multiplicative.ofAdd x) : W) ∈ U' := by
      rw [h1]
      exact (D.e.symm (Multiplicative.ofAdd x)).2
    obtain ⟨hw, hUw⟩ := hmem
    simpa using hUw

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
