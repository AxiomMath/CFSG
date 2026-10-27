module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixOpenDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixChev
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixReeChev
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem gff_not_labelA2 {lab : LargeEvenLabel} (hA : lab.tag ≠ .A) (hB : lab.tag ≠ .twA) :
    ¬ GGLabelA2 lab := fun h => h.2.2.elim (fun h' => hA h'.1) (fun h' => hB h'.1)

theorem ggL45FieldFixLabelAll_twF4der {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twF4der) :
    LargeEvenLabelAll lab (GGL45FieldFixKGRaw p lab) := by
  refine largeEvenLabelAll_smallExc hlab (Or.inr ht) fun {r} A K _ _ hK H => ?_
  refine ggL45FieldFixKGRaw_of_torsion
    (gff_not_labelA2 (by rw [ht]; decide) (by rw [ht]; decide)) ?_
  rintro X _ _ θ hX ψ hψ ⟨f, hfF, u, -, hford, -⟩ Q hQ
  have hf1 : f = 1 := chevFieldImage_eq_one_of_card_two hK H hfF
  rw [hf1, orderOf_one] at hford
  exact absurd hford.symm hp.one_lt.ne'

section Open

theorem ggL45FieldFixKnownForms_of_open (h : GGL45FieldFixKnownFormsOpen) :
    GGL45FieldFixKnownForms := by
  intro p hp hp2 lab hlab
  by_cases hopen : GGL45FieldFixOpenLabel p lab
  · exact h p hp hp2 lab hlab hopen
  · have hA : GGLabelA2 lab → p ≠ 3 := fun h3 hp3 => hopen ⟨h3, hp3⟩
    by_cases hT : GGL45TorsionTag lab
    · rcases hT with ht | ht | ht | ht
      · exact ggL45FieldFixLabelAll_of_torsion
          (gff_not_labelA2 (by rw [ht]; decide) (by rw [ht]; decide))
          (ggL45FieldFixLabelAll_chev hp hp2 hlab (Or.inr ht))
      · exact ggL45FieldFixLabelAll_of_torsion
          (gff_not_labelA2 (by rw [ht]; decide) (by rw [ht]; decide))
          (ggL45FieldFixLabelAll_chev hp hp2 hlab (Or.inl ht))
      · exact ggL45FieldFixLabelAll_of_torsion
          (gff_not_labelA2 (by rw [ht]; decide) (by rw [ht]; decide))
          (ggL45FieldFixLabelAll_twF4 hp hp2 hlab ht)
      · exact ggL45FieldFixLabelAll_twF4der hp hlab ht
    · exact ggL45FieldFixLabelAll_of_vac hA hT

end Open

end CFSG.StandardType
