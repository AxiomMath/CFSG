module

public import CFSG.RankThree.PartTwo.KFacts.KS21SylowCore
public import CFSG.RankThree.PartTwo.KFacts.KS21FusionL44

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts.KS21.L44

open CFSG.RankThree.PartTwo.KFacts.KS21.DFT CFSG.Assembly.RankThreeEven

theorem exists_omega_data : ∃ ω : F4ˣ, orderOf ω = 3 ∧ ω ^ 3 = 1 ∧ (ω : F4) ^ 2 + ω + 1 = 0 := by
  obtain ⟨ω, hω⟩ := exists_omega
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hω
    norm_num at hω
  exact ⟨ω, hω, hω3, sq_add_add_one_eq_zero hω3 hω1⟩

theorem maxEA_M : MaxEA M 3 := by
  obtain ⟨ω, hω, hω3, -⟩ := exists_omega_data
  exact maxEA_of_torus_hom embSL embSL_injective (tau3_injective hω3 hω) permGL3_pow_three
    (permGL3_mul_tau3 hω3) rot3_ne card_V3 card_M_eq (by norm_num) rot3_norm' card_fix3_lt
    card_V3_three

theorem maxEA_projSL : MaxEA (projSL 4 F4) 3 := maxEA_M.of_mulEquiv equivSL.symm

theorem sylowModel_M : SylowModel M (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)) := by
  obtain ⟨ω, hω, hω3, -⟩ := exists_omega_data
  refine ⟨embSL.comp (wreathHom (tau3 hω3) permGL3 permGL3_pow_three (permGL3_mul_tau3 hω3)),
    embSL_injective.comp (wreathHom_injective (tau3_injective hω3 hω) permGL3_pow_three
      (permGL3_mul_tau3 hω3) rot3_ne), ?_⟩
  rw [factorization_three_eq card_M_eq (by norm_num), RegularWreathProduct.card]
  simp

theorem sylowModel_projSL :
    SylowModel (projSL 4 F4) (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)) :=
  sylowModel_M.of_mulEquiv equivSL.symm

end CFSG.RankThree.PartTwo.KFacts.KS21.L44
