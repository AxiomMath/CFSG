module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.TwE6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.D4Tw
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTw

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

theorem isExtraGood_iff_exists_isSpecialType {S : Type*} [Group S] {x : S} :
    IsExtraGood x ↔ ∃ (H : Subgroup S) (e n : ℕ), x ∈ H ∧ IsSpecialType 3 e n ↥H ∧ e = 1 ∧ 2 ≤ n :=
  ⟨fun ⟨H, n, hx, hH, hn⟩ => ⟨H, 1, n, hx, hH, rfl, hn⟩,
    fun ⟨H, _, n, hx, hH, he, hn⟩ => ⟨H, n, hx, he ▸ hH, hn⟩⟩


theorem twistedInnerDataOf_E6_three (L : Type) [Field L] [IsAlgClosed L] [CharP L 3] :
    TwistedInnerDataOf TwistTag.E6 L 3 1 fun e n => e = 1 ∧ 2 ≤ n := by
  intro x hx hx2 hx1
  obtain ⟨r, hr, l, hl, g₁, hg₁, hgx, hgF⟩ :=
    exists_conj_toral_twist_E6tw 3 (by norm_num) le_rfl hx hx2
  obtain ⟨u, hu, hgood, hinv⟩ :=
    exists_inv_extraGood_E6tw_twist (k := L) hr (mask_ne_zero_of_conj_ne_one hx1 hgx) hl
  exact ⟨g₁, hg₁, _, hgF, u, hu, isExtraGood_iff_exists_isSpecialType.1 hgood,
    by rw [hgx]; exact hinv⟩

theorem twistedInnerDataOf_D4_three (L : Type) [Field L] [IsAlgClosed L] [CharP L 3] :
    TwistedInnerDataOf TwistTag.D4 L 3 1 fun e n => e = 1 ∧ 2 ≤ n := by
  intro x hx hx2 hx1
  obtain ⟨r, hr, l, hl, g₁, hg₁, hgx, hgF⟩ :=
    exists_conj_toral_twist_D4tw 3 (by norm_num) le_rfl hx hx2
  obtain ⟨u, hu, hgood, hinv⟩ :=
    exists_inv_extraGood_D4tw_twist (k := L) hr (mask_ne_zero_of_conj_ne_one hx1 hgx) hl
  exact ⟨g₁, hg₁, _, hgF, u, hu, isExtraGood_iff_exists_isSpecialType.1 hgood,
    by rw [hgx]; exact hinv⟩

theorem involGood_E6tw_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3 ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 3) :
    InvolGood (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
  have hK' : Nat.card K = (3 ^ 1) ^ 2 := hK
  have hσ' : ∀ c, σ c = c ^ (3 ^ 1) := fun c => by rw [hσ, pow_one]
  have : CharP K 3 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_three (by norm_num : 1 ≤ 2) hK
  have : CharP (AlgebraicClosure K) 3 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 3
  intro α hα
  refine Or.inl ?_
  by_cases hin : α ∈ twistedE6Inn K σ
  · obtain ⟨g, rfl⟩ := hin
    obtain ⟨x, hx, hinv, hgood⟩ := exists_inv_conj_twisted TwistTag.E6 (by norm_num) le_rfl hK' σ
      hσ' (AlgebraicClosure K) (twistedInnerDataOf_E6_three _) g hα
    exact ⟨x, hx, hinv, isExtraGood_iff_exists_isSpecialType.2 hgood⟩
  · have hα2 : α ^ 2 = 1 := by rw [← hα, pow_orderOf_eq_one]
    obtain ⟨x, hx, hinv, hgood⟩ := exists_inv_outer_E6tw (by norm_num) le_rfl hK' σ hσ'
      (R := fun e n => e = 1 ∧ 2 ≤ n)
      (fun k _ _ _ => by
        obtain ⟨u, hu, hg, hi⟩ := exists_inv_extraGood_E6tw_graph (k := k)
        exact ⟨u, hu, isExtraGood_iff_exists_isSpecialType.1 hg, hi⟩)
      (fun k _ _ _ => by
        obtain ⟨u, hu, hg, hi⟩ := exists_inv_extraGood_E6tw_graph_diag (k := k)
        exact ⟨u, hu, isExtraGood_iff_exists_isSpecialType.1 hg, hi⟩)
      α hα2 hin
    exact ⟨x, hx, hinv, isExtraGood_iff_exists_isSpecialType.2 hgood⟩

theorem involGood_D4tw_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3 ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 3) :
    InvolGood (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have hK' : Nat.card K = (3 ^ 1) ^ 3 := hK
  have hσ' : ∀ c, σ c = c ^ (3 ^ 1) := fun c => by rw [hσ, pow_one]
  have : CharP K 3 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_three (by norm_num : 1 ≤ 3) hK
  have : CharP (AlgebraicClosure K) 3 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 3
  intro β hβ
  refine Or.inl ?_
  have hβ2 : β ^ 2 = 1 := by rw [← hβ, pow_orderOf_eq_one]
  obtain ⟨-, -, ⟨_, -, -, hker, hinv⟩, -⟩ :=
    odd_triality_exact_automorphism_normal_form Nat.prime_three (by norm_num) le_rfl K hK' σ hσ'
  rcases hinv β hβ2 with h1 | ⟨⟨a, ha⟩, -⟩
  ·
    have hin : β ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
      rw [← hker]
      exact h1
    obtain ⟨g, rfl⟩ := hin
    obtain ⟨x, hx, hinv', hgood⟩ := exists_inv_conj_twisted TwistTag.D4 (by norm_num) le_rfl hK' σ
      hσ' (AlgebraicClosure K) (twistedInnerDataOf_D4_three _) g hβ
    exact ⟨x, hx, hinv', isExtraGood_iff_exists_isSpecialType.2 hgood⟩
  ·
    omega

theorem involAt_twistedE6 : InvolAt .twistedE6 := by
  intro S _ _ n _ _ hS
  obtain ⟨⟨hp, he, -⟩, hm⟩ := hS.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, σ, hK, hσ, ⟨φ⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.E6 hp he hm
  exact InvolGood.of_mulEquiv φ.symm
    (involGood_E6tw_three (hK.trans (by decide)) σ fun c => by rw [hσ, pow_one])

theorem involAt_trialityD4 : InvolAt .trialityD4 := by
  intro S _ _ n _ _ hS
  obtain ⟨⟨hp, he, -⟩, hm⟩ := hS.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, σ, hK, hσ, ⟨φ⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 hp he hm
  exact InvolGood.of_mulEquiv φ.symm
    (involGood_D4tw_three (hK.trans (by decide)) σ fun c => by rw [hσ, pow_one])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
