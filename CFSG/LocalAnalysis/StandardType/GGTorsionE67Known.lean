module

public import CFSG.LocalAnalysis.StandardType.GGTorsionE67Basic
public import CFSG.LocalAnalysis.StandardType.GGTorsionE67Linear
public import CFSG.LocalAnalysis.StandardType.GGTorsionE67BCD
public import CFSG.LocalAnalysis.StandardType.GGTorsionE67Exc
public import CFSG.LocalAnalysis.StandardType.GGTorsionE67Small

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionE67Known

theorem ggTorsionKnownOverTags_nonE
    : GGTorsionKnownOverTags
      (fun lab => lab.tag ≠ .E8 ∧ lab.tag ≠ .E7 ∧ lab.tag ≠ .E6 ∧ lab.tag ≠ .twE6)
      (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) := by
  have hA : GGTorsionKnownOverTags GGTorsionAmbA
      (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) :=
    ggTorsionKnownOverTagsE67_ambA
  have hB : GGTorsionKnownOverTags GGTorsionAmbBCD
      (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) :=
    ggTorsionKnownOverTagsE67_ambBCD
  have hS : GGTorsionKnownOverTags GGTorsionAmbSmall
      (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) :=
    ggTorsionKnownOverTagsE67_small
  have hE : GGTorsionKnownOverTags
      (fun lab => GGTorsionAmbExc lab ∧
        (lab.tag ≠ .E8 ∧ lab.tag ≠ .E7 ∧ lab.tag ≠ .E6 ∧ lab.tag ≠ .twE6))
      (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) :=
    ggTorsionKnownOverTags_mono
      (P := fun lab => lab.tag = .F4 ∨ lab.tag = .triD4 ∨ lab.tag = .G2)
      ggTorsionKnownOverTagsE67_exc (by
        rintro ⟨t, _, _⟩ ⟨hexc, h8, h7, h6, h6'⟩
        simp only [GGTorsionAmbExc] at hexc
        rcases hexc with h | h | h | h | h | h | h <;> simp_all)
  have hAB := ggTorsionKnownOverTags_or hA hB
  have hABE := ggTorsionKnownOverTags_or hAB hE
  have hU := ggTorsionKnownOverTags_or hABE hS
  refine ggTorsionKnownOverTags_mono hU ?_
  rintro ⟨t, r, n⟩ ⟨h8, h7, h6, h6'⟩
  have hcls : GGTorsionAmbA (⟨t, r, n⟩ : LargeEvenLabel) ∨
      GGTorsionAmbBCD (⟨t, r, n⟩ : LargeEvenLabel) ∨
      GGTorsionAmbExc (⟨t, r, n⟩ : LargeEvenLabel) ∨
      GGTorsionAmbSmall (⟨t, r, n⟩ : LargeEvenLabel) := by
    cases t <;> simp [GGTorsionAmbA, GGTorsionAmbBCD, GGTorsionAmbExc, GGTorsionAmbSmall]
  rcases hcls with h | h | h | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr ⟨h, h8, h7, h6, h6'⟩)
  · exact Or.inr h

end TorsionE67Known

end CFSG.StandardType
