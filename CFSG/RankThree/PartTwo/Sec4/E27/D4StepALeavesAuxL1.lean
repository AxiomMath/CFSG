module

public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL1Data
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityAB
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorusLayerAux
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL1Conj

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof Subgroup
  CFSG.RankThree.PartTwo.Sec19
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec4.E27

section Leaves


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem layer_linear_model (P : D4Par n X σ) (hn : 2 ≤ n) (hev : Even n) {x : C0 σ}
    (hx : IsClassX σ x) : LayerLinearModel σ x := by
  classical
  unfold IsClassX at hx
  obtain ⟨hx3, hx1, g₀, hg₀⟩ := hx
  have hv3 : (g₀ * x * g₀⁻¹) ^ 3 = 1 := TorusLayerAux.conj_pow_eq_one hx3
  have hv1 : g₀ * x * g₀⁻¹ ≠ 1 := TorusLayerAux.conj_ne_one hx1
  have hf : 1 ≤ n := by omega
  have hK : Nat.card X = (2 ^ n) ^ 3 := P.card
  have hσ : ∀ c : X, σ c = c ^ (2 ^ n) := P.frob
  have hq1 : 2 ^ n % 3 = 1 := by
    obtain ⟨m, hm⟩ := hev
    rw [hm, ← two_mul]
    exact TorusLayerAux.two_pow_mod_three_even m
  have hq4 : 4 ≤ 2 ^ n := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hn
    simpa using this
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP X 2 := finite_field_prime_power_characteristic Nat.prime_two (k := n * 3)
    (by omega) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure X) 2 :=
    charP_of_injective_algebraMap (algebraMap X (AlgebraicClosure X)).injective 2
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ] using this
  have h3L : (3 : AlgebraicClosure X) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : AlgebraicClosure X) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (AlgebraicClosure X) 2] at h'
    omega
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_three (AlgebraicClosure X) h3L
  obtain ⟨x₀, k, hk, hxk, hmodel⟩ := exists_threeA_layer_linear (ℓ := 2) (f := n) hf (by decide)
    hq1 hq4 hK hσ hζ
  obtain ⟨k', hk', hzk⟩ := exists_conj_dA_of_mem_short hσ3 hζ hg₀ hv3 hv1
  obtain ⟨c, hc⟩ := exists_conj_of_triEmb_conj hf hK hσ (isPointIrreducible_gA hζ) hk' hk hzk hxk
  apply layerLinearModel_of_conj σ (c * g₀) x
  have : c * g₀ * x * (c * g₀)⁻¹ = x₀ := by
    rw [← hc]
    group
  rw [this]
  exact hmodel

theorem layer_unitary_model (P : D4Par n X σ) (hn : 2 ≤ n) (hodd : Odd n) {x : C0 σ}
    (hx : IsClassX σ x) : LayerUnitaryModel σ n x := by
  classical
  unfold IsClassX at hx
  obtain ⟨hx3, hx1, g₀, hg₀⟩ := hx
  have hv3 : (g₀ * x * g₀⁻¹) ^ 3 = 1 := TorusLayerAux.conj_pow_eq_one hx3
  have hv1 : g₀ * x * g₀⁻¹ ≠ 1 := TorusLayerAux.conj_ne_one hx1
  have hf : 1 ≤ n := by omega
  have hK : Nat.card X = (2 ^ n) ^ 3 := P.card
  have hσ : ∀ c : X, σ c = c ^ (2 ^ n) := P.frob
  have hq1 : 2 ^ n % 3 = 2 := by
    obtain ⟨m, hm⟩ := hodd
    rw [hm]
    exact TorusLayerAux.two_pow_mod_three_odd m
  have hq2 : 2 < 2 ^ n := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hn
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP X 2 := finite_field_prime_power_characteristic Nat.prime_two (k := n * 3)
    (by omega) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure X) 2 :=
    charP_of_injective_algebraMap (algebraMap X (AlgebraicClosure X)).injective 2
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ] using this
  have h3L : (3 : AlgebraicClosure X) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : AlgebraicClosure X) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (AlgebraicClosure X) 2] at h'
    omega
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_three (AlgebraicClosure X) h3L
  obtain ⟨x₀, k, hk, hxk, hmodel⟩ := exists_threeA_layer_unitary (n := n) hf hq1 hq2 hK hσ hζ
  obtain ⟨k', hk', hzk⟩ := exists_conj_dA_of_mem_short hσ3 hζ hg₀ hv3 hv1
  obtain ⟨c, hc⟩ := exists_conj_of_triEmb_conj hf hK hσ (isPointIrreducible_gA hζ) hk' hk hzk hxk
  apply layerUnitaryModel_of_conj σ n (c * g₀) x
  have : c * g₀ * x * (c * g₀)⁻¹ = x₀ := by
    rw [← hc]
    group
  rw [this]
  exact hmodel

end Leaves

end CFSG.RankThree.PartTwo.Sec4.E27
