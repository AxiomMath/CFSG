module

public import CFSG.LocalAnalysis.StandardType.GGL45TorusPackageP4
public import CFSG.LocalAnalysis.StandardType.GGL45FamCover

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL45TorusKGRaw_of_H (p : ℕ) (hp : p.Prime) (lab : LargeEvenLabel) (R : Type) [Group R]
    (I F : Set (MulAut R)) (h : GGL45TorusHRaw p lab R I F) : GGL45TorusKGRaw p lab R I F :=
  (ggL45TorusKGRaw_iff_hyp p lab R I F).2 fun K _ _ θ hK hA ψ E hH =>
    ggL45TorusPackage_of_HMod hp hK hH.2.2.2.2.2.2.1 (h K θ hK hA ψ E hH)

theorem ggL45TorusKnownFormsOn_of_H (S : ℕ → LargeEvenLabel → Prop)
    (h : GGL45TorusHKnownFormsOn S) : GGL45TorusKnownFormsOn S :=
  fun p hp hp2 lab hlab hkg hS =>
    (h p hp hp2 lab hlab hkg hS).mono fun R _ I F hR => ggL45TorusKGRaw_of_H p hp lab R I F hR

theorem ggL45TorusKnownForms_of_H (h₁ : GGL45TorusHKnownFormsOn GGL45FamNonTorsion)
    (h₂ : GGL45TorusHKnownFormsOn GGL45FamTypeA) (h₃ : GGL45TorusHKnownFormsOn GGL45FamE67) :
    GGL45TorusKnownForms :=
  ggL45TorusKnownForms_of_families (ggL45TorusKnownFormsOn_of_H _ h₁)
    (ggL45TorusKnownFormsOn_of_H _ h₂) (ggL45TorusKnownFormsOn_of_H _ h₃)

theorem ggL45TorusHKnownFormsOn_of_split (S S₁ S₂ : ℕ → LargeEvenLabel → Prop)
    (hcov : ∀ (p : ℕ) (lab : LargeEvenLabel), S p lab → S₁ p lab ∨ S₂ p lab)
    (h₁ : GGL45TorusHKnownFormsOn S₁) (h₂ : GGL45TorusHKnownFormsOn S₂) :
    GGL45TorusHKnownFormsOn S := by
  intro p hp hp2 lab hlab hkg hS
  rcases hcov p lab hS with h | h
  · exact h₁ p hp hp2 lab hlab hkg h
  · exact h₂ p hp hp2 lab hlab hkg h

end CFSG.StandardType
