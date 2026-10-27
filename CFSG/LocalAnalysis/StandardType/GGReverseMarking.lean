module

public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
public import CFSG.LocalAnalysis.StandardType.GGInterfaceBridge
public import CFSG.LieType.Catalog.Realization
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem exists_mul_ne_mul_centerQuot_of_perfect {X : Type*} [Group X] (hX : commutator X = ⊤)
    (hne : Nontrivial (X ⧸ Subgroup.center X)) :
    ∃ a b : X ⧸ Subgroup.center X, a * b ≠ b * a := by
  by_contra hnab
  have hab : ∀ a b : X ⧸ Subgroup.center X, a * b = b * a := fun a b => by
    by_contra h
    exact hnab ⟨a, b, h⟩
  have hle : commutator X ≤ Subgroup.center X := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g _ h _
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      hab (g : X ⧸ Subgroup.center X) h]
    group
  obtain ⟨q, hq⟩ := exists_ne (1 : X ⧸ Subgroup.center X)
  induction q using QuotientGroup.induction_on with
  | H g => exact hq ((QuotientGroup.eq_one_iff g).mpr (hle (by rw [hX]; exact Subgroup.mem_top g)))

theorem center_eq_bot_of_isSimpleGroup_of_nonabelian {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hnab : ∃ a b : Q, a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center Q := by rw [h]; exact Subgroup.mem_top a
    exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab

section Main

theorem largeEvenMarking_of_lieModel_centerQuot {X : Type} [Group X] (hX : commutator X = ⊤)
    {t : StatedLieTag} {n f : ℕ} (h : LieModel (X ⧸ Subgroup.center X) t n 2 f) :
    LargeEvenMarking X fun lab _ _ _ _ _ =>
      markTag lab = t ∧ markRank lab = n ∧ markChar lab = 2 ∧ markDeg lab = f := by
  obtain ⟨-, hnt, hs⟩ := CFSG.LieType.Catalog.lieModel_finite_simple _ t n 2 f h
  have hnab := exists_mul_ne_mul_centerQuot_of_perfect hX hnt
  obtain ⟨lab, hlab, ht, hn, hp, hf, hraw⟩ :=
    exists_label_rawDatum_of_lieModel (center_eq_bot_of_isSimpleGroup_of_nonabelian hnab) h
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨e⟩
  exact ⟨e.symm.isSimpleGroup, nonabelian_of_mulEquiv e hnab, e, ht, hn, hp, hf⟩

theorem ggLieModelMarkingInput_holds : GGLieModelMarkingInput := by
  intro X _ _ t n f _ hX h
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial)
    (largeEvenMarking_of_lieModel_centerQuot hX h)

namespace Legacy
abbrev largeEvenMarking_of_lieModel_centerQuot :=
  @CFSG.StandardType.largeEvenMarking_of_lieModel_centerQuot
abbrev ggLieModelMarkingInput_holds := @CFSG.StandardType.ggLieModelMarkingInput_holds
end Legacy

namespace Canonical
theorem largeEvenMarking_of_lieModel_centerQuot {X : Type} [Group X] (hX : commutator X = ⊤)
    {t : StatedLieTag} {n f : ℕ} (h : LieModel (X ⧸ Subgroup.center X) t n 2 f) :
    CFSG.Assembly.LargeEvenMarking X fun lab _ _ _ _ _ =>
      markTag lab = t ∧ markRank lab = n ∧ markChar lab = 2 ∧ markDeg lab = f := by
  exact CFSG.Assembly.largeEvenMarkingLegacy_to_canonical_carrier
    (CFSG.StandardType.largeEvenMarking_of_lieModel_centerQuot hX h)

theorem ggLieModelMarkingInput_holds : GGLieModelMarkingInput := by
  intro X _ _ t n f _ hX h
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial)
    (largeEvenMarking_of_lieModel_centerQuot hX h)
end Canonical

end Main

end CFSG.StandardType
