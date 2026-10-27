module

public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs
public import CFSG.LocalAnalysis.StandardType.GGTriD4ComponentsPGLDer
public import CFSG.LocalAnalysis.StandardType.GGTriD4ComponentsMark
import CFSG.LocalAnalysis.StandardType.GGL45FixA2Comp
import CFSG.LocalAnalysis.StandardType.GGL45FixA2Arith
import CFSG.LocalAnalysis.StandardType.GGL45FixA2UniFix
import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearProj

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.RankThree.PartTwo
open CFSG.PGLModel (projImage)

theorem ggTriD4_pgl_clause {X : Type} [Group X] {C : Subgroup X} {n : ℕ} (hn : Even n)
    (hn1 : 1 ≤ n) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ n)
    (E : ↥C ≃* ↥(projImage (Sec4.glPi true 3 (2 ^ n) F))) {Q : Subgroup X}
    (hQ : IsComponentOf Q C) :
    Subgroup.center Q = ⊥ ∧ LargeEvenMarking Q fun lab _ _ _ _ _ => GGLabelA2 lab := by
  have hn2 : 2 ≤ n := by
    obtain ⟨k, hk⟩ := hn
    omega
  obtain ⟨E'⟩ := gffa2_commutator_equiv E
  obtain ⟨T₀⟩ := ggTriD4_pgl_derived_equiv hn2 hF
  let T : ↥⁅C, C⁆ ≃* LargeEvenProj (LargeEvenSLGroup (Fin 3) F) := E'.trans T₀
  have hs : IsSimpleGroup (LargeEvenProj (LargeEvenSLGroup (Fin 3) F)) :=
    LinearFieldFix.isSimpleGroup_proj (d := 3) (by norm_num) F
  have hnab : ∃ a b : LargeEvenProj (LargeEvenSLGroup (Fin 3) F), a * b ≠ b * a :=
    LinearFieldFix.exists_noncomm_proj (d := 3) (by norm_num) F
  obtain ⟨Qe⟩ := gffa2_component_equiv T hs hQ
  obtain ⟨hlab, hA2⟩ := gffa2_label_linear hn hn1
  have hdatum : LargeEvenRawDatum ⟨.A, 2, n⟩ fun R₀ _ _ _ =>
      IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ Nonempty (↥Q ≃* R₀) := by
    dsimp only [LargeEvenRawDatum]
    exact ⟨F, inferInstance, inferInstance, hF, hs, hnab, ⟨Qe⟩⟩
  exact ggMarking_of_rawDatum hlab hA2 hdatum

theorem ggTriD4_pgu_clause {X : Type} [Group X] {C : Subgroup X} {n : ℕ} (hn : Odd n)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2)
    (E : ↥C ≃* ↥(projImage (Sec4.glPi false 3 (2 ^ n) F))) {Q : Subgroup X}
    (hQ : IsComponentOf Q C) :
    Subgroup.center Q = ⊥ ∧ LargeEvenMarking Q fun lab _ _ _ _ _ => GGLabelA2 lab := by
  have hodd : Odd n := hn
  obtain ⟨k, hk⟩ := hn
  have hcases : n = 1 ∨ 3 ≤ n := by
    rcases k with _ | k
    · left; omega
    · right; omega
  rcases hcases with hn1 | hn3
  · subst hn1
    have hsolv : Group.IsSolvable ↥(projImage (Sec4.glPi false 3 (2 ^ 1) F)) :=
      ggTriD4_pgu_two_solvable (n := 1) rfl hF
    have hsolvC : Group.IsSolvable ↥C := by
      haveI := hsolv
      exact Group.isSolvable_of_isSolvable_injective (f := E.toMonoidHom) E.injective
    exact (gffa2_false_of_solvable hsolvC hQ).elim
  · have hn2 : 2 ≤ n := by omega
    obtain ⟨E'⟩ := gffa2_commutator_equiv E
    obtain ⟨T₀⟩ := ggTriD4_pgu_derived_equiv hn2 hF
    let T : ↥⁅C, C⁆ ≃* LargeEvenProj (LargeEvenSUGroup (Fin 3) F (2 ^ n)) := E'.trans T₀
    obtain ⟨hs, hnab⟩ := gffa2_unitary_simple_nonab hn2 hF
    obtain ⟨Qe⟩ := gffa2_component_equiv T hs hQ
    obtain ⟨hlab, hA2⟩ := gffa2_label_unitary hodd hn3
    have hdatum : LargeEvenRawDatum ⟨.twA, 2, n⟩ fun R₀ _ _ _ =>
        IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ Nonempty (↥Q ≃* R₀) := by
      dsimp only [LargeEvenRawDatum]
      exact ⟨F, inferInstance, inferInstance, hF, hs, hnab, ⟨Qe⟩⟩
    exact ggMarking_of_rawDatum hlab hA2 hdatum

end CFSG.StandardType
