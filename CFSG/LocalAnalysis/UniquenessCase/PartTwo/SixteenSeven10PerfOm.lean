module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.Background.P3OrthoOm4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Open.StatedAPI CFSG.Quasithin.G11.P3Ortho Subgroup
open scoped MatrixGroups

private theorem center_sl2_aux {K : Type} [Field K] [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have h2 : r ^ 2 = 1 := by simpa using hr
  have hr1 : r = 1 := by
    have h0 : (r - 1) ^ 2 = 0 := by
      rw [CharTwo.sub_eq_add, CharTwo.add_sq, h2, one_pow, one_add_one_eq_two]
      exact CharTwo.two_eq_zero
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1]
  simp

private theorem center_bot_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : Subgroup.center B = ⊥) : Subgroup.center A = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hz' : e z ∈ Subgroup.center B := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
  rw [h, Subgroup.mem_bot] at hz'
  exact e.injective (by rw [hz', map_one])

private theorem commutator_top_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : _root_.commutator B = ⊤) : _root_.commutator A = ⊤ := by
  have h1 : (⁅(⊤ : Subgroup B), (⊤ : Subgroup B)⁆).map e.symm.toMonoidHom =
      ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.symm.surjective]
  show ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ = ⊤
  rw [← h1, show ⁅(⊤ : Subgroup B), (⊤ : Subgroup B)⁆ = ⊤ from h,
    Subgroup.map_top_of_surjective _ e.symm.surjective]

private theorem omegaPlus_equiv {Y : Type} [Group Y] (h : IsOmegaPlus Y 4 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), 4 ≤ Nat.card K ∧
      Nonempty (Y ≃* (SL(2, K) × SL(2, K))) := by
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := h
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 2) (by rw [← Nat.card_eq_fintype_card, hcard])
  have h4 : 4 ≤ Nat.card K := by rw [hcard]; norm_num
  obtain ⟨ε⟩ := Om4.iso_of_card K h4
  have hZ : Subgroup.center ↥(StatedOmega (StatedQuadPlus 2 K)) = ⊥ :=
    center_bot_of_equiv ε (by rw [Subgroup.center_prod, center_sl2_aux, Subgroup.bot_prod_bot])
  have hS : (StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedOmega (StatedQuadPlus 2 K)) = ⊥ :=
    le_bot_iff.1 (hZ ▸ statedScalars_subgroupOf_le_center _)
  let q : StatedProj (StatedOmega (StatedQuadPlus 2 K)) ≃* ↥(StatedOmega (StatedQuadPlus 2 K)) :=
    (QuotientGroup.quotientMulEquivOfEq hS).trans QuotientGroup.quotientBot
  exact ⟨K, inferInstance, inferInstance, inferInstance, h4, ⟨(e.trans q).trans ε⟩⟩

theorem s16c1610_center_of_isOmegaPlus_four_two {Y : Type} [Group Y]
    (h : IsOmegaPlus Y 4 2) : Subgroup.center Y = ⊥ := by
  obtain ⟨K, _, _, _, -, ⟨e⟩⟩ := omegaPlus_equiv h
  exact center_bot_of_equiv e (by rw [Subgroup.center_prod, center_sl2_aux, Subgroup.bot_prod_bot])

theorem s16c1610_commutator_of_isOmegaPlus_four_two {Y : Type} [Group Y]
    (h : IsOmegaPlus Y 4 2) : _root_.commutator Y = ⊤ := by
  obtain ⟨K, _, _, _, h4, ⟨e⟩⟩ := omegaPlus_equiv h
  have hSL := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K h4
  exact commutator_top_of_equiv e (Om4.isPerfect_prod hSL hSL).commutator_eq_top

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
