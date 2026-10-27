module

public import CFSG.RankThree.LocalRank.ElementaryTwoWeights
public import TauCeti.LinearAlgebra.BilinearForm.Isometry
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.RankThree.Classical

open Module CFSG.RankThree.LocalRank

section General

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem card_le_two_pow_of_symplectic_elementary_two (hk : (2 : k) ≠ 0) [FiniteDimensional k V]
    {n : ℕ} (hV : finrank k V = 2 * n) (B : LinearMap.BilinForm k V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (R : Subgroup (V ≃ₗ[k] V))
    (hRB : R ≤ TauCeti.BilinForm.isometryGroup B) [Finite R] (hR2 : ∀ r ∈ R, r * r = 1) :
    Nat.card R ≤ 2 ^ n := by
  classical
  have hsq : ∀ r : R, r * r = 1 := fun r => Subtype.ext (hR2 r r.2)
  let : CommGroup R :=
    { (inferInstance : Group R) with
      mul_comm := fun a b => by
        rw [← inv_eq_of_mul_eq_one_right (hsq (a * b)), mul_inv_rev,
          inv_eq_of_mul_eq_one_right (hsq a), inv_eq_of_mul_eq_one_right (hsq b)] }
  let : Module (ZMod 2) (Additive R) := AddCommGroup.zmodModule fun x => by
    rw [two_nsmul]
    exact hsq (Additive.toMul x)
  have : Finite (Module.Dual (ZMod 2) (Additive R)) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) (Additive R) => (f : Additive R → ZMod 2))
      DFunLike.coe_injective
  let := Fintype.ofFinite (Module.Dual (ZMod 2) (Additive R))
  let := Fintype.ofFinite R
  let ρ : Representation k R V :=
    { toFun := fun r => ((r : V ≃ₗ[k] V) : V →ₗ[k] V)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hρ : Function.Injective ρ := fun r s h =>
    Subtype.ext (LinearEquiv.toLinearMap_injective h)
  obtain ⟨hbij, -, hspan, -, -⟩ := elementary_two_weight_decomposition hk ρ
  have hspan' := hspan.mp hρ
  have horth : ∀ χ ψ, χ ≠ ψ → ∀ v ∈ signWeightSpace ρ χ, ∀ w ∈ signWeightSpace ρ ψ,
      B v w = 0 := by
    intro χ ψ hχψ v hv w hw
    obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hχψ
    have hva := (mem_signWeightSpace ρ χ v).mp hv (Additive.toMul x)
    have hwa := (mem_signWeightSpace ρ ψ w).mp hw (Additive.toMul x)
    have hiso := TauCeti.BilinForm.mem_isometryGroup_iff.mp (hRB (Additive.toMul x).2) v w
    change B (ρ (Additive.toMul x) v) (ρ (Additive.toMul x) w) = B v w at hiso
    rw [hva, hwa, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at hiso
    have hsum : χ (Additive.ofMul (Additive.toMul x)) + ψ (Additive.ofMul (Additive.toMul x)) =
        1 := (by decide : ∀ y z : ZMod 2, y ≠ z → y + z = 1) _ _ hx
    have hm1 : (-1 : k) ^ ZMod.val (χ (Additive.ofMul (Additive.toMul x))) *
        (-1) ^ ZMod.val (ψ (Additive.ofMul (Additive.toMul x))) = -1 := by
      rw [← neg_one_pow_val_add, hsum, ZMod.val_one, pow_one]
    have h2 : (2 : k) * B v w = 0 := by linear_combination (-1 : k) * hiso + B v w * hm1
    exact (mul_eq_zero.mp h2).resolve_left hk
  have htop := iSup_signWeightSpace_eq_top ρ hk
  have hres : ∀ χ, (B.restrict (signWeightSpace ρ χ)).Nondegenerate := by
    intro χ
    have hBr : (B.restrict (signWeightSpace ρ χ)).IsAlt := fun x => hB x
    refine hBr.isRefl.nondegenerate_iff_separatingLeft.mpr fun v hv => ?_
    apply Subtype.ext
    rw [Submodule.coe_zero]
    refine hnd.1 _ fun y => ?_
    have hy : y ∈ ⨆ ψ, signWeightSpace ρ ψ := by rw [htop]; exact Submodule.mem_top
    refine Submodule.iSup_induction (signWeightSpace ρ) (motive := fun y => B (v : V) y = 0) hy
      (fun ψ w hw => ?_) (map_zero _) (fun y₁ y₂ h₁ h₂ => by rw [map_add, h₁, h₂, add_zero])
    by_cases hψ : ψ = χ
    · rw [hψ] at hw
      exact hv ⟨w, hw⟩
    · exact horth χ ψ (Ne.symm hψ) v v.2 w hw
  have heven : ∀ χ, Even (finrank k (signWeightSpace ρ χ)) := fun χ =>
    LinearMap.BilinForm.IsAlt.even_finrank (B := B.restrict (signWeightSpace ρ χ))
      (fun x => hB x) (hres χ)
  have hsumdim : ∑ χ, finrank k (signWeightSpace ρ χ) = 2 * n := by
    rw [← hV, ← Module.finrank_directSum, LinearEquiv.finrank_eq (LinearEquiv.ofBijective _ hbij)]
  have hS : {χ | signWeightSpace ρ χ ≠ ⊥}.toFinset.card ≤ n := by
    have h2 : 2 * {χ | signWeightSpace ρ χ ≠ ⊥}.toFinset.card ≤ 2 * n := by
      rw [← hsumdim]
      calc 2 * {χ | signWeightSpace ρ χ ≠ ⊥}.toFinset.card
          = ∑ _χ ∈ {χ | signWeightSpace ρ χ ≠ ⊥}.toFinset, 2 := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ χ ∈ {χ | signWeightSpace ρ χ ≠ ⊥}.toFinset, finrank k (signWeightSpace ρ χ) :=
            Finset.sum_le_sum fun χ hχ => by
              rw [Set.mem_toFinset, Set.mem_ofPred_eq] at hχ
              have hne : finrank k (signWeightSpace ρ χ) ≠ 0 := fun h0 =>
                hχ (Submodule.finrank_eq_zero.mp h0)
              obtain ⟨m, hm⟩ := heven χ
              omega
        _ ≤ ∑ χ, finrank k (signWeightSpace ρ χ) :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    omega
  have h1 : finrank (ZMod 2) (Module.Dual (ZMod 2) (Additive R)) ≤
      {χ | signWeightSpace ρ χ ≠ ⊥}.toFinset.card := by
    have h := finrank_span_le_card (R := ZMod 2) {χ | signWeightSpace ρ χ ≠ ⊥}
    rwa [hspan', finrank_top] at h
  rw [Subspace.dual_finrank_eq] at h1
  have hcard : Nat.card R = 2 ^ finrank (ZMod 2) (Additive R) := by
    let := Fintype.ofFinite (Additive R)
    change Nat.card (Additive R) = _
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  rw [hcard]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end General

end CFSG.RankThree.Classical
