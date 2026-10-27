module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KFacts
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParOrders
import CFSG.LieType.Universal.Unitary.RootGroupCardRankTwo
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.Models.PGL
import CFSG.RankThree.PartTwo.Sec21.KS21U4Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22

namespace BorelOrders

open CFSG.Open (StatedProj StatedSU)
open CFSG.LieType.Universal.Unitary (rootDatum card_rootGroup_four_zero_ne_one
  card_rootGroup_five_zero_ne_one exists_traceZero_ne_zero)

theorem eq_of_normalizer_le_of_card_eq_of_mulEquiv {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) {m : ℕ} (hm : m = 4 ∨ m = 5) {Y : Type} [Group Y]
    [Finite Y] (e : Y ≃* StatedProj (StatedSU m (2 ^ f) F)) (T : Sylow 2 Y)
    {Z₁ Z₂ : Subgroup Y} (h₁ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ Z₁)
    (h₂ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ Z₂)
    (hZ : Nat.card Z₁ = Nat.card Z₂) : Z₁ = Z₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have h := CFSG.AGLEmbedding.ParabHub.borelQuotient_su hF (by omega) ζ hζ e
  refine CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.eq_of_normalizer_le_of_card_eq h
    (show m / 2 ≤ 2 by omega) ?_ T h₁ h₂ hZ
  rcases hm with rfl | rfl
  · have h01 := card_rootGroup_four_zero_ne_one hF
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h01
    · exact h01.symm
    · exact absurd rfl hij
  · have h01 := card_rootGroup_five_zero_ne_one hF
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h01
    · exact h01.symm
    · exact absurd rfl hij

theorem eq_of_normalizer_le_of_card_eq_of_isU4 {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : IsU4 X n) (T : Sylow 2 X) {Z₁ Z₂ : Subgroup X}
    (h₁ : Subgroup.normalizer ((T : Subgroup X) : Set X) ≤ Z₁)
    (h₂ : Subgroup.normalizer ((T : Subgroup X) : Set X) ≤ Z₂)
    (hZ : Nat.card Z₁ = Nat.card Z₂) : Z₁ = Z₂ := by
  have hn0 : 0 < n := (CFSG.Blueprint.LieModel.admissible hX).2.1
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel
    (CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide))
    (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
      (CFSG.Blueprint.LieModel.admissible hX) (MulEquiv.refl _))
  exact eq_of_normalizer_le_of_card_eq_of_mulEquiv
    (CFSG.RankThree.PartTwo.Sec21.U4Lines.card_galoisField_two_mul n hn0) (Or.inl rfl)
    (e.trans (CFSG.PGLModel.projSUEquivStatedProj 4 2 n)) T h₁ h₂ hZ

theorem eq_of_normalizer_le_of_card_eq_of_isU5 {X : Type} [Group X] [Finite X] (hX : IsU5 X 2)
    (T : Sylow 2 X) {Z₁ Z₂ : Subgroup X}
    (h₁ : Subgroup.normalizer ((T : Subgroup X) : Set X) ≤ Z₁)
    (h₂ : Subgroup.normalizer ((T : Subgroup X) : Set X) ≤ Z₂)
    (hZ : Nat.card Z₁ = Nat.card Z₂) : Z₁ = Z₂ := by
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel
    (CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide))
    (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
      (CFSG.Blueprint.LieModel.admissible hX) (MulEquiv.refl _))
  exact eq_of_normalizer_le_of_card_eq_of_mulEquiv
    (CFSG.RankThree.PartTwo.Sec21.U4Lines.card_galoisField_two_mul 2 (by norm_num)) (Or.inr rfl)
    (e.trans (CFSG.PGLModel.projSUEquivStatedProj 5 2 2)) T h₁ h₂ hZ

end BorelOrders

theorem kU45BorelOrders_holds : KU45BorelOrders := by
  intro X _ _ n hX T₀ Z₁ Z₂ h₁ h₂ hZ
  rcases hX with ⟨hU5, rfl⟩ | ⟨hU4, -⟩
  · exact BorelOrders.eq_of_normalizer_le_of_card_eq_of_isU5 hU5 T₀ h₁ h₂ hZ
  · exact BorelOrders.eq_of_normalizer_le_of_card_eq_of_isU4 hU4 T₀ h₁ h₂ hZ

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
