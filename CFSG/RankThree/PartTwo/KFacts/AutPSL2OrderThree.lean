module

public import CFSG.RankThree.PartTwo.KFacts.AutPSL2
import CFSG.RankThree.SteinbergR3ELinearTwoFieldDescent

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable {K : Type*} [Field K] [Finite K]

private theorem coordinateAutAction_pglAction (g : PGL2 K) :
    coordinateAutAction K (pglAction K g) = coordinatePGLAction K g := by
  rw [← coordinateSemilinearAction_inl, coordinateSemilinearAction, MonoidHom.comp_apply,
    semilinearAction_inl]

private theorem coordinateAutAction_psl2FieldAut (σ : K ≃+* K) :
    coordinateAutAction K (psl2FieldAut K σ) = fieldExtension K σ := by
  rw [← coordinateSemilinearAction_inr, coordinateSemilinearAction, MonoidHom.comp_apply,
    semilinearAction_inr]

theorem linear_two_prime_order_field_descent {p : ℕ} (hp : p.Prime) (α : MulAut (PSL2 K))
    (hα : orderOf α = p) (hD : α ∉ (pglAction K).range) :
    ∃ σ : K ≃+* K, orderOf σ = p ∧ ∃ g : PGL2 K,
      α = pglAction K g * psl2FieldAut K σ * (pglAction K g)⁻¹ := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ℓ, -, f, hℓ, hcard⟩ := FiniteField.card' K
  have hK : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have haE : coordinateAutAction K α ∈ coordinateE K := by
    rw [← coordinateSemilinearAction_range_eq_E]
    obtain ⟨x, rfl⟩ := semilinearAction_surjective K α
    exact ⟨x, rfl⟩
  have haD : coordinateAutAction K α ∉ coordinateD K := by
    rw [← coordinatePGLAction_range_eq_D]
    rintro ⟨g, hg⟩
    exact hD ⟨g, coordinateAutAction_injective K (by rw [coordinateAutAction_pglAction, hg])⟩
  have hap : orderOf (coordinateAutAction K α) = p := by
    rw [orderOf_injective _ (coordinateAutAction_injective K) α, hα]
  obtain ⟨-, σ, hσ, ⟨h, hh, hah⟩, -⟩ :=
    CFSG.RankThree.LinearTwo.linear_two_prime_semilinear_field_descent hℓ hp f.pos K
      hK haE haD hap
  rw [← coordinatePGLAction_range_eq_D] at hh
  obtain ⟨g, rfl⟩ := hh
  refine ⟨σ, hσ, g, coordinateAutAction_injective K ?_⟩
  rw [map_mul, map_mul, map_inv, coordinateAutAction_pglAction, coordinateAutAction_psl2FieldAut]
  exact hah

theorem isField_psl2_of_orderOf_prime {p : ℕ} (hp : p.Prime) {α : MulAut (PSL2 K)}
    (hα : orderOf α = p) (hD : α ∉ (pglAction K).range) : (stdPinnedPSL2 K).IsField α := by
  obtain ⟨σ, hσ, g, rfl⟩ := linear_two_prime_order_field_descent hp α hα hD
  refine ⟨psl2FieldAut K σ, ⟨σ, rfl⟩, fun h1 => ?_, pglAction K g, ⟨g, rfl⟩, rfl⟩
  have h := psl2FieldAut_injective K (h1.trans (map_one _).symm)
  rw [h, orderOf_one] at hσ
  exact hp.one_lt.ne hσ

theorem hasKind_psl2_diagonal_or_field_of_pow_three_eq_one {α : MulAut (PSL2 K)}
    (hα : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    (stdPinnedPSL2 K).HasKind α .diagonal ∨ (stdPinnedPSL2 K).HasKind α .field := by
  by_cases hD : α ∈ (pglAction K).range
  · exact Or.inl ⟨hD, hout⟩
  · refine Or.inr (isField_psl2_of_orderOf_prime Nat.prime_three ?_ hD)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime hα fun h1 => hout ?_
    rw [h1]
    exact ⟨1, map_one _⟩

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

theorem inducesKindPSL2_diagonal_or_field {x : G} (hx3 : x ^ 3 = 1)
    (hout : InducesOuterTheta x L) (e : L ⧸ aschbacherSolvableCore 3 L ≃* PSL2 K) :
    InducesKind L (stdPinnedPSL2 K) e x .diagonal ∨
      InducesKind L (stdPinnedPSL2 K) e x .field := by
  obtain ⟨hx, -⟩ := id hout
  rcases hasKind_psl2_diagonal_or_field_of_pow_three_eq_one (inducedAutHom_pow_eq_one L e hx hx3)
    ((not_isInnerAut_inducedAutHom_iff L e hx).mpr hout) with h | h
  · exact Or.inl ⟨hx, h⟩
  · exact Or.inr ⟨hx, h⟩

end Induced

end CFSG.RankThree.PartTwo.KFacts
