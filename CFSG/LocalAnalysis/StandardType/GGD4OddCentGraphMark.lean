module

public import CFSG.LocalAnalysis.StandardType.GGTriD4ComponentsG2
public import CFSG.LocalAnalysis.StandardType.GGTriD4ComponentsPGL
import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGL45FixA2Comp
import CFSG.LocalAnalysis.StandardType.GGL45FixA2Arith
import CFSG.LocalAnalysis.StandardType.GGL45FixA2UniFix
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorComponents

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.PartTwo
open CFSG.PGLModel (projImage)

@[expose] def GGD4OddCentOuterShape (n : ℕ) (C : Type) [Group C] : Prop :=
  (∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ n ∧
      Nonempty (C ≃* ↥(adjointGroup Tag.G2 k))) ∨
  (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
      Nonempty (C ≃* ↥(projImage (Sec4.glPi false 3 (2 ^ n) F)))) ∨
  (∃ (d : ℕ) (K₃ : Type) (_ : Field K₃) (_ : Finite K₃), 1 ≤ d ∧ n = 3 * d ∧
      Nat.card K₃ = (2 ^ d) ^ 3 ∧ IsSimpleGroup C ∧ (∃ a b : C, a * b ≠ b * a) ∧
      Nonempty (C ≃* GGTriD4R d K₃))

theorem GGD4OddCentOuterShape.of_mulEquiv {n : ℕ} {C C' : Type} [Group C] [Group C']
    (e : C ≃* C') (h : GGD4OddCentOuterShape n C') : GGD4OddCentOuterShape n C := by
  rcases h with ⟨k, i₁, i₂, hk, ⟨E⟩⟩ | ⟨F, i₁, i₂, hF, ⟨E⟩⟩ |
    ⟨d, K₃, i₁, i₂, hd, hn3, hK₃, hs, hnab, ⟨E⟩⟩
  · exact Or.inl ⟨k, i₁, i₂, hk, ⟨e.trans E⟩⟩
  · exact Or.inr (Or.inl ⟨F, i₁, i₂, hF, ⟨e.trans E⟩⟩)
  · haveI := hs
    obtain ⟨a, b, hab⟩ := hnab
    exact Or.inr (Or.inr ⟨d, K₃, i₁, i₂, hd, hn3, hK₃, e.isSimpleGroup,
      ⟨e.symm a, e.symm b, fun h' => hab (by
        have := congrArg e h'
        simpa only [map_mul, MulEquiv.apply_symm_apply] using this)⟩,
      ⟨e.trans E⟩⟩)

private theorem ggD4OddCent_pgu_clause {X : Type} [Group X] {C : Subgroup X} {n : ℕ} (hn : Odd n)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2)
    (E : ↥C ≃* ↥(projImage (Sec4.glPi false 3 (2 ^ n) F))) {Q : Subgroup X}
    (hQ : IsComponentOf Q C) :
    Subgroup.center Q = ⊥ ∧
      LargeEvenMarking Q fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA := by
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
    exact ggMarking_of_rawDatum (lab := ⟨.twA, 2, n⟩)
      (P := fun lab => GGLabelA2 lab ∧ lab.tag = .twA) hlab ⟨hA2, rfl⟩ hdatum

theorem ggD4OddCent_outerShape_marking
    {X : Type} [Group X] {C : Subgroup X} {n : ℕ}
    (hn : Odd n) (h : GGD4OddCentOuterShape n ↥C) {Q : Subgroup X} (hQ : IsComponentOf Q C) :
    LargeEvenMarking Q fun lab _ _ _ _ _ =>
      GGLabelG2 lab ∨ lab.tag = .triD4 ∨
        (GGLabelA2 lab ∧ lab.tag = .twA ∧ Subgroup.center Q = ⊥) := by
  rcases h with ⟨k, i₁, i₂, hk, ⟨E⟩⟩ | ⟨F, i₁, i₂, hF, ⟨E⟩⟩ |
    ⟨d, K₃, i₁, i₂, hd, hn3, hK₃, hs, hnab, ⟨E⟩⟩
  · have hn1 : 1 ≤ n := by obtain ⟨m, hm⟩ := hn; omega
    exact largeEvenMarking_mono (fun lab R _ I F θ h' => Or.inl h')
      (ggTriD4_g2_clause hn1 hk E hQ).2
  · obtain ⟨hZ, hmark⟩ := ggD4OddCent_pgu_clause hn hF E hQ
    exact largeEvenMarking_mono
      (fun lab R _ I F θ h' => Or.inr (Or.inr ⟨h'.1, h'.2, hZ⟩)) hmark
  · haveI := hs
    have hQeq : Q = C :=
      CFSG.ComponentClassification.ExcSelector.eq_of_isComponentOf_of_isSimpleGroup hQ
    rw [hQeq]
    have hdatum : LargeEvenRawDatum ⟨.triD4, 0, d⟩ fun R₀ _ _ _ =>
        IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ Nonempty (↥C ≃* R₀) := by
      dsimp only [LargeEvenRawDatum]
      obtain ⟨a, b, hab⟩ := hnab
      exact ⟨K₃, i₁, i₂, hK₃, E.symm.isSimpleGroup,
        ⟨E a, E b, fun h' => hab (E.injective (by simpa only [map_mul] using h'))⟩, ⟨E⟩⟩
    have htri : LargeEvenMarking ↥C (fun lab _ _ _ _ _ => lab.tag = .triD4) :=
      (ggMarking_of_rawDatum (Y := ↥C) (lab := ⟨.triD4, 0, d⟩)
        (P := fun lab => lab.tag = .triD4) ⟨hd, rfl⟩ rfl hdatum).2
    exact largeEvenMarking_mono (fun lab R _ I F θ h' => Or.inr (Or.inl h')) htri

end CFSG.StandardType
