module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.ZS.AbsIrred
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U] {n : ℕ}

private lemma two_ne_zero_zmod (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hpdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  rcases (Nat.dvd_prime Nat.prime_two).mp hpdiv with hp1 | hp2
  · exact (Fact.out : p.Prime).ne_one hp1
  · exact hp hp2

private lemma equivFun_diagMap (b : Module.Basis (Fin n) (ZMod p) U)
    (d : Fin n → (ZMod p)ˣ) (w : U) :
    b.equivFun (diagMap p b d w) = fun j => (d j : ZMod p) • b.equivFun w j := by
  rw [diagMap, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  funext j
  rw [LinearEquiv.piCongrRight_apply, LinearEquiv.smulOfUnit,
    DistribMulAction.toLinearEquiv_apply, Units.smul_def]

private lemma sub_diagMap_sign (b : Module.Basis (Fin n) (ZMod p) U) (i : Fin n) (w : U) :
    w - diagMap p b (fun j => if j = i then (-1 : (ZMod p)ˣ) else 1) w =
      (2 * b.equivFun w i) • b i := by
  apply b.equivFun.injective
  rw [map_sub, equivFun_diagMap, map_smul]
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Module.Basis.equivFun_self, if_true, Units.val_neg, Units.val_one]
    rw [neg_one_mul, mul_one, two_mul]
    abel
  · have hji : ¬ i = j := fun h => hj h.symm
    simp only [Pi.sub_apply, Pi.smul_apply, Module.Basis.equivFun_self,
      Units.val_one, hj, hji, if_false, one_smul, smul_zero]
    abel

private lemma signChange_sub_id_apply (b : Module.Basis (Fin n) (ZMod p) U) (i : Fin n)
    (w : U) :
    (((diagMap p b (fun j => if j = i then (-1 : (ZMod p)ˣ) else 1) :
      U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - (LinearMap.id : U →ₗ[ZMod p] U)) w =
      (-(2 * b.equivFun w i)) • b i := by
  rw [LinearMap.sub_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply, ← neg_sub,
    sub_diagMap_sign]
  rw [← neg_smul]
  rfl

private lemma range_signChange_eq_span (hp : p ≠ 2)
    (b : Module.Basis (Fin n) (ZMod p) U) (i : Fin n) :
    LinearMap.range (((diagMap p b (fun j => if j = i then (-1 : (ZMod p)ˣ) else 1) :
      U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - (LinearMap.id : U →ₗ[ZMod p] U)) =
      Submodule.span (ZMod p) {b i} := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp
  have hcalc : (-(2 * (-((2 : ZMod p)⁻¹)))) = 1 := by
    field_simp [h2]
  apply le_antisymm
  · rintro x ⟨w, rfl⟩
    rw [signChange_sub_id_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton (b i)))
  · rw [Submodule.span_le]
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨(-((2 : ZMod p)⁻¹)) • b i, ?_⟩
    rw [signChange_sub_id_apply, map_smul, Pi.smul_apply, Module.Basis.equivFun_self]
    simp only [if_true, smul_eq_mul, mul_one, hcalc, one_smul]

theorem irreducible_of_signed_le (hp : p ≠ 2) (b : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hperm : ∀ σ, permMap p b σ ∈ A)
    (hsgn : ∀ i, diagMap p b (fun j => if j = i then -1 else 1) ∈ A)
    (W : Submodule (ZMod p) U) (hW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  rcases eq_or_ne W ⊥ with hbot | hne
  · exact Or.inl hbot
  · refine Or.inr ?_
    obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hne
    obtain ⟨i, hi⟩ : ∃ i, b.equivFun w i ≠ 0 := by
      by_contra h
      simp only [not_exists, not_ne_iff] at h
      refine hw0 (b.equivFun.injective ?_)
      rw [map_zero]
      funext j
      exact h j
    let s : U ≃ₗ[ZMod p] U :=
      diagMap p b (fun j => if j = i then (-1 : (ZMod p)ˣ) else 1)
    have hsA : s ∈ A := hsgn i
    have hdiff : w - s w = (2 * b.equivFun w i) • b i := sub_diagMap_sign b i w
    have hmem : (2 * b.equivFun w i) • b i ∈ W := by
      rw [← hdiff]
      exact W.sub_mem hwW (hW s hsA w hwW)
    have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp
    have hc : (2 : ZMod p) * b.equivFun w i ≠ 0 := mul_ne_zero h2 hi
    have hbi : b i ∈ W := by
      have h := W.smul_mem ((2 * b.equivFun w i)⁻¹) hmem
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
    have hb : ∀ j, b j ∈ W := by
      intro j
      have h := hW (permMap p b (Equiv.swap i j)) (hperm (Equiv.swap i j)) (b i) hbi
      rwa [permMap_apply_basis, Equiv.swap_apply_left] at h
    have hle : Submodule.span (ZMod p) (Set.range b) ≤ W :=
      Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hb j)
    rw [b.span_eq] at hle
    exact le_antisymm le_top hle

theorem absIrred_of_signed_le (hp : p ≠ 2) (hn : 1 ≤ n) (b : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hperm : ∀ σ, permMap p b σ ∈ A)
    (hsgn : ∀ i, diagMap p b (fun j => if j = i then -1 else 1) ∈ A) : AbsIrred p A := by
  let i : Fin n := ⟨0, by omega⟩
  refine absIrred_of_finrank_range_eq_one
    (irreducible_of_signed_le hp b hperm hsgn) (hsgn i) ?_
  rw [range_signChange_eq_span hp b i, finrank_span_singleton (b.ne_zero i)]

end CFSG.StandardType.ZS

end
