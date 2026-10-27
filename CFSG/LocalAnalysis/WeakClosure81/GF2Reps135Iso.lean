module

import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.StatedPSLTwoSeven
import CFSG.Blueprint.LieModelAPI
import CFSG.GF2Type.Aschbacher1977.SymplecticExclusions
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.GH74.GLS (InChev2)
open scoped commutatorElement Pointwise

theorem w135_center_eq_bot_of_lieModel {L : Type} [Group L] (hq : CFSG.IsQuasisimple L)
    {t : CFSG.Open.StatedLieTag} {n p f : ℕ} (ht : t ∈ CFSG.Blueprint.classicalTags)
    (h : LieModel L t n p f) : Subgroup.center L = ⊥ := by
  have : IsSimpleGroup L := LieModel.isSimpleGroup_of_mem_classicalTags ht h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h0 | h0
  · exact h0
  · exfalso
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have ha' : a' ∈ Subgroup.center L := by rw [h0]; trivial
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp ha' b']

section InChev2

variable {S : Type} [Group S]

theorem w135_inChev2_of_alt_five (h : IsAlt S 5) : InChev2 S := by
  have hmodel := CFSG.QuasithinUnique.Ch1.statedClassicalModel_psl_two_four_of_alternating_five
    S h
  exact Or.inl ⟨.PSL, 2, 2, ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩,
    Or.inl ⟨by decide, hmodel⟩⟩

theorem w135_inChev2_of_alt_six (h : IsAlt S 6) : InChev2 S :=
  Or.inr (Or.inl h)

theorem w135_inChev2_of_alt_eight (h : IsAlt S 8) : InChev2 S := by
  have hmodel := CFSG.QuasithinUnique.Ch1.statedClassicalModel_psl_four_two_of_alternating_eight
    S h
  exact Or.inl ⟨.PSL, 4, 1, ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩,
    Or.inl ⟨by decide, hmodel⟩⟩

theorem w135_inChev2_of_psl_two_five
    (h : LieModel S .PSL 2 5 1) : InChev2 S :=
  w135_inChev2_of_alt_five
    (CFSG.Semidihedral.Principal.LargePrimeTorus.nonempty_equiv_alternating_five_of_model
      (h.statedClassicalModel (by decide)))

theorem w135_inChev2_of_psl_two_seven (h : LieModel S .PSL 2 7 1) : InChev2 S := by
  have hmodel := CFSG.Open.StatedAPI.statedClassicalModel_psl_three_two_of_psl_two_seven
    (h.statedClassicalModel (by decide))
  exact Or.inl ⟨.PSL, 3, 1, ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩,
    Or.inl ⟨by decide, hmodel⟩⟩

theorem w135_inChev2_of_psl_two_nine (h : LieModel S .PSL 2 3 2) : InChev2 S :=
  Or.inr (Or.inl
    (CFSG.Open.StatedAPI.nonempty_mulEquiv_alternating_six_of_psl_two_nine
      (h.statedClassicalModel (by decide))))

theorem w135_inChev2_of_psp_two_three (h : LieModel S .PSp 2 3 1) : InChev2 S := by
  have hPSU := CFSG.GF2Type.Aschbacher1977.lieModel_PSU_four_two_of_PSp_two_three h
  exact Or.inl ⟨.PSU, 4, 1, ⟨Nat.prime_two, by norm_num, by norm_num, by decide⟩, hPSU⟩

theorem w135_inChev2_of_psl_two_eight (h : LieModel S .PSL 2 2 3) : InChev2 S :=
  Or.inl ⟨.PSL, 2, 3, ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, h⟩

theorem w135_inChev2_of_psu_three_three (h : LieModel S .PSU 3 3 1) : InChev2 S :=
  Or.inr (Or.inr h)

end InChev2

section Quotient

variable {L : Type} [Group L]

theorem w135_inChev2_quotient_of_psu_three_three (hq : CFSG.IsQuasisimple L)
    (h : LieModel L .PSU 3 3 1) : InChev2 (L ⧸ Subgroup.center L) :=
  w135_inChev2_of_psu_three_three
    (LieModel.quotient_center (w135_center_eq_bot_of_lieModel hq (by decide) h) h)

theorem w135_inChev2_quotient_of_psp_two_three (hq : CFSG.IsQuasisimple L)
    (h : LieModel L .PSp 2 3 1) : InChev2 (L ⧸ Subgroup.center L) :=
  w135_inChev2_of_psp_two_three
    (LieModel.quotient_center (w135_center_eq_bot_of_lieModel hq (by decide) h) h)

theorem w135_inChev2_quotient_of_psl_two_eight (hq : CFSG.IsQuasisimple L)
    (h : LieModel L .PSL 2 2 3) : InChev2 (L ⧸ Subgroup.center L) :=
  w135_inChev2_of_psl_two_eight
    (LieModel.quotient_center (w135_center_eq_bot_of_lieModel hq (by decide) h) h)

end Quotient

end CFSG.LocalAnalysis.WeakClosure81
