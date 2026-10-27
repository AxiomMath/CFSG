module

public import CFSG.LocalAnalysis.SteinbergCDEvenLinearThreeGraphElementary
public import CFSG.LocalAnalysis.SteinbergCDEvenLinearThreeSemilinearFixed
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.SteinbergCD

variable {K : Type*} [Field K]

theorem conjAut_fieldAut_dualAut_eq_descendAut_graphSemilinearAut (A : GL (Fin 3) K)
    (σ : K ≃+* K) :
    conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K =
      descendAut 3 K (graphSemilinearAut A⁻¹ σ) := by
  obtain ⟨-, -, -, hδδ, -, hδf, -⟩ := standard_automorphism_transport (K := K) (n := 3)
  rw [descendAut_graphSemilinearAut, inv_inv, mul_assoc, mul_assoc]
  congr 1
  calc fieldAut 3 K σ * dualAut 3 K
      = dualAut 3 K * fieldAut 3 K σ * dualAut 3 K * dualAut 3 K := by rw [hδf σ]
    _ = dualAut 3 K * fieldAut 3 K σ * (dualAut 3 K * dualAut 3 K) := by
        simp only [mul_assoc]
    _ = dualAut 3 K * fieldAut 3 K σ := by rw [hδδ, mul_one]

variable [Finite K] [CharP K 2]

theorem linearThreeInvolution_isEmpty_fixed_SL_two (β : MulAut (projectiveSL 3 K))
    (hβ : orderOf β = 2) (U : Subgroup (projectiveSL 3 K)) [IsElementaryAbelian 2 U]
    (hUcard : Nat.card U = Nat.card K ^ 2) (hUβ : U.map β.toMonoidHom ≤ U)
    (J : Subgroup (projectiveSL 3 K)) (hJ : J ≤ TauCeti.fixedSubgroup β.toMonoidHom) :
    IsEmpty (J ≃* SpecialLinearGroup (Fin 2) K) := by
  have hUβ' : U.map β.toMonoidHom = U :=
    Subgroup.eq_of_le_of_card_ge hUβ (by rw [Subgroup.card_map_of_injective β.injective])
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 β
  interval_cases ε
  · rw [pow_zero, mul_one] at hβ hJ
    exact (characteristic_two_linear_three_semilinear_involution_fixed_order K A σ hβ).2.2.2.2 J hJ
  · rw [pow_one, conjAut_fieldAut_dualAut_eq_descendAut_graphSemilinearAut] at hUβ'
    exact absurd hUβ' (map_descendAut_ne A⁻¹ σ U hUcard)

theorem linearThreeInvolution_isEmpty_mulEquiv_of_mulAut {D : Type*} [Group D] (α : MulAut D)
    (hα : orderOf α = 2) (K₀ : Subgroup D) (hK₀ : K₀ ≤ TauCeti.fixedSubgroup α.toMonoidHom)
    (hK₀SL : Nonempty (K₀ ≃* SpecialLinearGroup (Fin 2) K)) (U₀ : Subgroup D)
    [IsElementaryAbelian 2 U₀] (hU₀card : Nat.card U₀ = Nat.card K ^ 2)
    (hU₀α : U₀.map α.toMonoidHom ≤ U₀) :
    IsEmpty (D ≃* projectiveSL 3 K) := by
  refine ⟨fun η => ?_⟩
  obtain ⟨e⟩ := hK₀SL
  set β := MulAut.congr η α with hβdef
  have hβ : orderOf β = 2 := by rw [hβdef, MulEquiv.orderOf_eq]; exact hα
  have hβη : ∀ d, β (η d) = η (α d) := fun d => by
    rw [hβdef, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  have hcomp : β.toMonoidHom.comp η.toMonoidHom = η.toMonoidHom.comp α.toMonoidHom :=
    MonoidHom.ext fun d => hβη d
  have : IsElementaryAbelian 2 (U₀.map η.toMonoidHom) := IsElementaryAbelian.map _
  refine (linearThreeInvolution_isEmpty_fixed_SL_two β hβ (U₀.map η.toMonoidHom) ?_ ?_
    (K₀.map η.toMonoidHom) ?_).false
    ((K₀.equivMapOfInjective η.toMonoidHom η.injective).symm.trans e)
  · rw [Subgroup.card_map_of_injective η.injective, hU₀card]
  · rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
    exact Subgroup.map_mono hU₀α
  · rintro _ ⟨k, hk, rfl⟩
    rw [TauCeti.mem_fixedSubgroup, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, hβη]
    exact congrArg η (hK₀ hk)

end CFSG.LocalAnalysis.SymplecticFourStandard
