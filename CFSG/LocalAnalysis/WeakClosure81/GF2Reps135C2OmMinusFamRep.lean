module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusFamData
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusFamNat
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFMain
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNodes
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQTrivType
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQScaffold

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

private theorem w135c2_omfMRep_finrank_range_conj {G k V : Type*} [Group G] [Field k]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) {z : G} (g y : G)
    (hz : z = g * y * g⁻¹) :
    Module.finrank k (LinearMap.range (ρ z - 1)) =
      Module.finrank k (LinearMap.range (ρ y - 1)) := by
  subst hz
  have hconj : ρ (g * y * g⁻¹) - 1 = ρ g * (ρ y - 1) * ρ (g⁻¹) := by
    rw [map_mul, map_mul]
    have h2 : ρ g * ρ (g⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    calc ρ g * ρ y * ρ (g⁻¹) - 1 = (ρ g * ρ y - ρ g) * ρ (g⁻¹) := by rw [sub_mul, h2]
      _ = ρ g * (ρ y - 1) * ρ (g⁻¹) := by rw [mul_sub, mul_one]
  have hsurj : Function.Surjective (ρ (g⁻¹)) := fun b =>
    ⟨ρ g b, by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]⟩
  have hrange : LinearMap.range (ρ g * (ρ y - 1) * ρ (g⁻¹)) =
      (LinearMap.range (ρ y - 1)).map (ρ g) := by
    rw [show ρ g * (ρ y - 1) * ρ (g⁻¹) =
      (ρ g).comp ((ρ y - 1).comp (ρ (g⁻¹))) from rfl]
    rw [LinearMap.range_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]
  have hleft : Function.LeftInverse (ρ (g⁻¹)) (ρ g) := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hright : Function.RightInverse (ρ (g⁻¹)) (ρ g) := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  let e : V ≃ₗ[k] V := LinearEquiv.ofBijective (ρ g) ⟨hleft.injective, hright.surjective⟩
  rw [hconj, hrange]
  exact e.finrank_map_eq (LinearMap.range (ρ y - 1))

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem w135c2_omfMRep_four_le_of_separating {n : ℕ} (hn5 : 5 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k V V₀ : Type} [Field k] [CharP k 2]
    [AddCommGroup V] [Module k V] [Module.Finite k V] [AddCommGroup V₀] [Module (ZMod 2) V₀]
    {σ : Representation k (spinGroup (quadMinus n K b c)) V} (hσ : IsSimpleRep σ)
    {y : spinGroup (quadMinus n K b c)} (hy : y * y = 1) (hy1 : y ≠ 1)
    {y₀ : V} {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n (by omega) hirrQ).IsCurtisType σ y₀ χ μ)
    {j : Fin (n - 1)} (hj0 : j.val ≠ 0)
    (hsep : μ j = (SmallO8mCurtis.curtisDatum n (by omega) hirrQ).dScalar χ j) {s : ℕ}
    (hs : 0 < s) {ρ : Representation (ZMod 2) (spinGroup (quadMinus n K b c)) V₀}
    (hrank : ∀ g : spinGroup (quadMinus n K b c),
      Module.finrank (ZMod 2) (LinearMap.range (ρ g - 1)) =
        s * Module.finrank k (LinearMap.range (σ g - 1))) :
    4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  have hn4 : 4 ≤ n := by omega
  obtain ⟨g, x, π, e, he, hxr, hnW, hshape⟩ := omqnf_exists_conj_nW hn4 hirrQ hy hy1
  have hsh : OmqMinusShape (by omega : 2 ≤ n - 1) π e := hshape
  have h4y : 4 ≤ Module.finrank k (LinearMap.range (σ y - 1)) := by
    rw [← w135c2_omfMRep_finrank_range_conj σ g y hnW]
    by_cases hj2 : j.val + 2 ≤ n - 1
    · exact omq_omMinus_four_le_rank_of_long_node hn4 hirrQ hσ ht hxr he hsh
        (by omega : 1 ≤ j.val) hj2 hsep
    · have hjval : j.val = n - 2 := by
        have hlt := j.isLt
        omega
      have hjn : j = (⟨n - 2, by omega⟩ : Fin (n - 1)) := Fin.ext hjval
      have hsep' : μ ⟨n - 2, by omega⟩ =
          (SmallO8mCurtis.curtisDatum n hn4 hirrQ).dScalar χ ⟨n - 2, by omega⟩ :=
        (congrArg (fun i : Fin (n - 1) => μ i =
          (SmallO8mCurtis.curtisDatum n hn4 hirrQ).dScalar χ i) hjn).mp hsep
      exact omq_omMinus_four_le_rank_of_short_node hn4 hirrQ hσ ht hxr he hsh hsep' (Or.inl hn5)
  rw [hrank y]
  exact Nat.le_trans (by norm_num : 4 ≤ 1 * 4)
    (Nat.mul_le_mul (show 1 ≤ s by omega) h4y)

theorem omMinus_two_natural_or_four_le_family (hK : Nat.card K = 2) {n : ℕ} (hn : 5 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] {ρ : Representation (ZMod 2) (spinGroup (quadMinus n K b c)) V}
    (hρ : IsSimpleRep ρ) {y : spinGroup (quadMinus n K b c)} (hy : y * y = 1) (hρy : ρ y ≠ 1) :
    (∃ β : V ≃+ (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K),
      ∀ (g : spinGroup (quadMinus n K b c)) (v : V), β (ρ g v) = mat n g *ᵥ β v) ∨
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  classical
  have hn4 : 4 ≤ n := by omega
  have : ρ.IsIrreducible :=
    (CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρ).mpr hρ
  have : Finite (CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Universal.Spin.isFiniteType_cartanB (n - 1))).Group :=
    CFSG.LieType.RootSystem.finite_group
      (CFSG.LieType.Universal.Spin.isFiniteType_cartanB (n - 1))
  let D :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.SmallO8mCurtis.curtisDatum
      n hn4 hirrQ
  obtain ⟨k, _hk, _hkc, _hka, _halg, ι, s, y₀, χ, μ, hs, _hE, hsimp, ht, _hfrob, hrank,
    htriv⟩ := omq_endfield_scaffold D (F := K) ρ
  let σ := CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have : FiniteDimensional (Module.End (MonoidAlgebra (ZMod 2)
      (spinGroup (quadMinus n K b c))) ρ.asModule) ρ.asModule :=
    CFSG.HardMathSupport.GuralnickMalle.finiteDimensional_endField ρ
  have : Module.Finite k (TensorProduct (Module.End (MonoidAlgebra (ZMod 2)
      (spinGroup (quadMinus n K b c))) ρ.asModule) k ρ.asModule) := inferInstance
  have hy1 : y ≠ 1 := fun h => hρy (by rw [h, map_one])
  have hσ : IsSimpleRep σ := hsimp
  have hσy : σ y ≠ 1 := fun h => hρy ((htriv y).mp h)
  rcases omMinus_two_type_cases hK hn4 hirrQ ht with ⟨hχ1, hμ0⟩ | hrest
  · rw [hμ0] at ht
    exact absurd (omq_rep_eq_one_of_isCurtisType_zero _ hσ ht hχ1 y) hσy
  · rcases hrest with ⟨hχ2, hμnat⟩ | ⟨j, hj0, hsep⟩
    · rw [hμnat] at ht
      exact Or.inl (omMinus_two_exists_addEquiv_of_isCurtisType hK hn4 hirrQ ρ k ι ht hχ2)
    · exact Or.inr (w135c2_omfMRep_four_le_of_separating hn hirrQ hσ hy hy1 ht hj0 hsep hs hrank)

end CFSG.LocalAnalysis.WeakClosure81
