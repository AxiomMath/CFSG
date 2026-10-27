module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTw
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcD4TwField
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcE7

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups


theorem involInvertsGood_D4tw {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (h3 : 3 < p ^ f) :
    InvolInvertsGood p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hp (by omega : 1 ≤ 3 * f) (by rw [hK, ← pow_mul, mul_comm])
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  intro β hβ
  have hβ2 : β ^ 2 = 1 := by rw [← hβ, pow_orderOf_eq_one]
  obtain ⟨-, hNF, ⟨Θ, hΘ, -, hker, hinv⟩, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  rcases hinv β hβ2 with h1 | ⟨⟨a, ha⟩, hδc⟩
  ·
    have hin : β ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
      rw [← hker]
      exact h1
    obtain ⟨g, rfl⟩ := hin
    exact exists_inv_good_conj_twisted TwistTag.D4 hp2 hf hK σ hσ (AlgebraicClosure K)
      (twistedInnerData_D4 hp2 hf h3 (AlgebraicClosure K)) g hβ
  ·
    obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hNF β
    change β = MulAut.conj g * fieldActor σ δ at hgδ
    rw [hΘ β g δ hgδ] at hδc
    have hodd : Odd (p ^ a) := (hp.eq_two_or_odd'.resolve_left hp2).pow
    have hK6 : Nat.card K = (p ^ a) ^ 6 := by
      rw [hK, ha, ← pow_mul, ← pow_mul]
      ring_nf
    have hσr : ∀ c, σ c = c ^ ((p ^ a) ^ 2) := fun c => by
      rw [hσ, ha, ← pow_mul]
      ring_nf
    have hδr : ∀ c, δ c = c ^ ((p ^ a) ^ 3) := fun c => by
      rw [hδc, ha, ← pow_mul, show 3 * (a + a) / 2 = a * 3 by omega]
    have hβ2' : (MulAut.conj g * fieldActor σ δ) ^ 2 = 1 := by rw [← hgδ]; exact hβ2
    obtain ⟨-, ⟨ψ, hψ⟩, -⟩ := odd_triality_field_coset_involution_fixed_p_components
      (hp.isPrimePow.pow (by omega)) hodd K hK6 σ hσr δ hδr g hβ2'
    obtain ⟨x, hx, hxinv, hgood⟩ :=
      exists_inv_good_D4tw_field hp hp2 hf hK σ hσ h3 ⟨a, ha⟩ δ hδc
    have hβ' : β = ψ⁻¹ * fieldActor σ δ * ψ := by
      rw [← hψ, hgδ]
      group
    refine ⟨ψ⁻¹ x, (MulEquiv.orderOf_eq ψ⁻¹ x).trans hx, ?_, Or.inl ?_⟩
    · rw [hβ', MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, hxinv, map_inv]
    · exact IsSpecialGood.map (f := MulEquiv.toMonoidHom ψ⁻¹) (MulEquiv.injective ψ⁻¹) hgood

theorem involQAt_trialityD4 : InvolQAt .trialityD4 := by
  intro S _ _ n p e hp2 h3 _ hS
  obtain ⟨⟨hp, he, -⟩, hm⟩ := hS.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, σ, hK, hσ, ⟨φ⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 hp he hm
  exact InvolInvertsGood.of_mulEquiv φ.symm (involInvertsGood_D4tw hp hp2 he hK σ hσ h3)

theorem w4Lem10_5InvolQ_holds : W4Lem10_5InvolQ :=
  w4Lem10_5InvolQ_of_twisted involQAt_twistedE6 involQAt_trialityD4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
