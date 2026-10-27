module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusFamAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusFamOuterRank
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusFamOuterField
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusFamOrbit
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusFamNat
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusFamData
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFWeylEx
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQScaffold
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQTrivType
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mModule
import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

private theorem omfo_isSign (n : ℕ) :
    CFSG.StandardType.SpIsSign (fun a : Fin (n - 1) => if n ≤ a.val + 3 then (-1 : ℤ) else 1) := by
  intro a
  dsimp only
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem omMinus_two_outer_natural_or_four_le_family (hK : Nat.card K = 2) {n : ℕ} (hn : 5 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] {ρ : Representation (ZMod 2) (spinGroup (quadMinus n K b c)) V}
    (hρ : IsSimpleRep ρ) (hρ1 : ∃ g, ρ g ≠ 1) (T : V ≃ₗ[ZMod 2] V) (hT2 : ∀ v, T (T v) = v)
    {h : spinGroup (quadMinus n K b c)} (hh : h * omMinusReflAut n (by omega) hirrQ h = 1)
    (hT : ∀ (g : spinGroup (quadMinus n K b c)) (v : V),
      T (ρ g v) = ρ (h * omMinusReflAut n (by omega) hirrQ g * h⁻¹) (T v)) :
    (∃ β : V ≃+ (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K),
      ∀ (g : spinGroup (quadMinus n K b c)) (v : V), β (ρ g v) = mat n g *ᵥ β v) ∨
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (T.toLinearMap - 1)) := by
  have hn4 : 4 ≤ n := by omega
  have : ρ.IsIrreducible := (CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρ).mpr hρ
  have : Finite (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartanB (n - 1))).Group :=
    CFSG.LieType.RootSystem.finite_group (isFiniteType_cartanB (n - 1))
  set D := UniquenessCase.PartTwo.Inputs1719.Thm14_5.SmallO8mCurtis.curtisDatum n hn4 hirrQ
    with hD
  obtain ⟨k, _hk, _hkc, _hka, _halg, ι, s, y, χ, μ, hs, _hE, hτ, ht, _hfrob, hrank, htriv⟩ :=
    omq_endfield_scaffold D (F := K) ρ
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have : FiniteDimensional (Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadMinus n K b c)))
      ρ.asModule) ρ.asModule :=
    CFSG.HardMathSupport.GuralnickMalle.finiteDimensional_endField ρ
  have : Module.Finite k (TensorProduct (Module.End (MonoidAlgebra (ZMod 2)
      (spinGroup (quadMinus n K b c))) ρ.asModule) k ρ.asModule) := inferInstance
  rcases omMinus_two_type_cases hK hn4 hirrQ ht with ⟨hχ, hμ⟩ | ⟨hχ, hμ⟩ | ⟨j, hj, hsep⟩
  ·
    subst hμ
    obtain ⟨g, hg⟩ := hρ1
    exact absurd ((htriv g).mp (omq_rep_eq_one_of_isCurtisType_zero _ hτ ht hχ g)) hg
  ·
    subst hμ
    exact Or.inl (omMinus_two_exists_addEquiv_of_isCurtisType hK hn4 hirrQ ρ k ι ht hχ)
  ·
    refine Or.inr ?_
    by_contra hlt
    have hlt' : Module.finrank (ZMod 2) (LinearMap.range (T.toLinearMap - 1)) < 4 :=
      not_le.mp hlt
    obtain ⟨x₂, hx₂⟩ := exists_omqnfRealizes_of_signedPerm (1 : Equiv.Perm (Fin (n - 1)))
      (omfo_isSign n)
    have h7 := omMinus_seven_le_rank_negLastTwo hn hirrQ hτ ht hj hsep hx₂
    have hs1 : 1 ≤ s := hs
    have h7' : 7 ≤ Module.finrank (ZMod 2)
        (LinearMap.range (ρ (D.nW x₂) - 1)) := by
      rw [hrank]
      calc 7 = 1 * 7 := (one_mul 7).symm
        _ ≤ _ := Nat.mul_le_mul hs1 h7
    have hV := Submodule.finrank_le
      (LinearMap.range (ρ (D.nW x₂) - 1))
    have hN : ∀ g, ∃ g', ∀ w, T (ρ g (T w)) = ρ g' w :=
      fun g => ⟨h * omMinusReflAut n hn4 hirrQ g * h⁻¹, fun w => by rw [hT, hT2]⟩
    have hcomm :=
      UniquenessCase.PartTwo.Inputs1719.Thm14_5.commute_endRing_of_two_mul_finrank_range_lt ρ
        inferInstance T hT2 hN (by omega)
    obtain ⟨T', hT', hle⟩ := exists_extendScalars_endField_intertwiner ρ k T.toLinearMap
      (fun g => h * omMinusReflAut n hn4 hirrQ g * h⁻¹) hT hcomm
    have h4 := omMinus_two_outer_four_le_of_isCurtisType hK hn hirrQ hτ ht hj hsep T' hh hT'
    omega

end CFSG.LocalAnalysis.WeakClosure81
