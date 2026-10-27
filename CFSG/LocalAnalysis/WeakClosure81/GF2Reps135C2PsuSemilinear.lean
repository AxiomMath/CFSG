module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallField

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Module

private theorem w135c2_two_mul_finrank_range_sub_one_eq {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (τ : V →ₗ[ZMod 2] V) (hτ : ∀ v, τ (τ v) = v)
    (hcard : Nat.card {w : V // τ w = w} ^ 2 = Nat.card V) :
    2 * finrank (ZMod 2) (LinearMap.range (τ - 1)) = finrank (ZMod 2) V := by
  classical
  have hfix : Nat.card {w : V // τ w = w} = Nat.card (LinearMap.ker (τ - 1)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun w => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero])
  have hW : Nat.card V = 2 ^ finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hker : Nat.card (LinearMap.ker (τ - 1)) =
      2 ^ finrank (ZMod 2) (LinearMap.ker (τ - 1)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hfix, hker, hW, ← pow_mul] at hcard
  have hdim := (Nat.pow_right_injective (by norm_num : 2 ≤ 2)) hcard
  have hrank := LinearMap.finrank_range_add_finrank_ker (τ - 1)
  omega

theorem w135c2_psu_semilinear_finrank {G V : Type} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) G V) (hirr : ρ.IsIrreducible)
    (τ : V ≃ₗ[ZMod 2] V) (hτ : ∀ v, τ (τ v) = v)
    (hN : ∀ g, ∃ g', ∀ v, τ (ρ g (τ v)) = ρ g' v)
    (hD : ∃ (T : Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) (v : V),
      τ (T (τ v)) ≠ T v) :
    2 * finrank (ZMod 2) (LinearMap.range ((τ : V →ₗ[ZMod 2] V) - 1)) = finrank (ZMod 2) V := by
  classical
  haveI : Fact ρ.IsIrreducible := ⟨hirr⟩
  have hD' : ∃ d : CFSG.QuasithinUnique.Setup.SL2Modules.EndRing ρ,
      ∃ w : V, τ (d (τ w)) ≠ d w := by
    obtain ⟨T, v, hv⟩ := hD
    let φ : Module.End (ZMod 2) V := T.restrictScalars (ZMod 2)
    have hsmul : ∀ (g : G) (y : ρ.asModule),
        MonoidAlgebra.of (ZMod 2) G g • y = ρ g y := fun g y => by
      rw [← Representation.asAlgebraHom_of (ρ := ρ) g]
      rfl
    have hcomm : ∀ g (x : ρ.asModule), φ (ρ g x) = ρ g (φ x) := by
      intro g x
      have h1 : MonoidAlgebra.of (ZMod 2) G g • x = ρ g x := hsmul g x
      show T (ρ g x) = ρ g (T x)
      rw [← h1, T.map_smul, hsmul g (T x)]
    obtain ⟨d, hd⟩ := (CFSG.QuasithinUnique.Setup.SL2Modules.mem_endRing_iff ρ φ).mpr hcomm
    refine ⟨d, v, ?_⟩
    intro h
    rw [congrFun hd (τ v), congrFun hd v] at h
    exact hv h
  have hcard :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.card_fix_sq_of_not_commute_endRing
      ρ τ hτ hN hD'
  exact w135c2_two_mul_finrank_range_sub_one_eq (τ : V →ₗ[ZMod 2] V) hτ hcard

end CFSG.LocalAnalysis.WeakClosure81
