module

public import Certificates.Certificate715750
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.QuotientGraph

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel LargeEvenSplit LargeEvenHalfSplit)
open CFSG.StandardType (GGLabelIso)


theorem tcC1_of_certificate
    (w : WeylGroup Tag.E6) (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = w • γ)
    {F : ℕ} (hF : F = 1 ∨ (3 ≤ F ∧ F % 2 = 1))
    (P : Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3)) (hP2 : Module.finrank (ZMod 3) P = 2)
    (hfrob : ∀ v ∈ P, ∀ j : Fin Tag.E6.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod 3) * v k = 2 * v j)
    (iJ : KernelComponent (tcChiPl Tag.E6 3 P))
    (hJ2 : 2 ≤ componentOrbitLength ρ (componentRoots (tcChiPl Tag.E6 3 P) iJ))
    {x : Fin Tag.E6.rank → ZMod 3} (hxP : x ∈ P) (hx0 : x ≠ 0)
    (ix : KernelComponent (tcChiLn Tag.E6 3 x))
    (hJx : componentRoots (tcChiPl Tag.E6 3 P) iJ ⊆ componentRoots (tcChiLn Tag.E6 3 x) ix)
    (hne : componentRoots (tcChiLn Tag.E6 3 x) ix ≠ componentRoots (tcChiPl Tag.E6 3 P) iJ)
    (hsplit : ∃ lab', GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 x) ix)) ∧
      LargeEvenSplit 3 lab')
    (hoth : ∀ d ∈ P, d ≠ 0 → (∀ c : ZMod 3, d ≠ c • x) →
      ∀ i : KernelComponent (tcChiLn Tag.E6 3 d),
      componentRoots (tcChiPl Tag.E6 3 P) iJ ⊆ componentRoots (tcChiLn Tag.E6 3 d) i →
      GGLabelIso (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 d) i))
        (LabAt ρ F (componentRoots (tcChiPl Tag.E6 3 P) iJ)) ∨
      ∃ (c : Prop) (lab' : LargeEvenLabel),
        GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 d) i)) ∧
        LargeEvenHalfSplit 3 lab' c) :
    F = 1 ∧ TcC1Row ρ (componentRoots (tcChiPl Tag.E6 3 P) iJ)
      (componentRoots (tcChiLn Tag.E6 3 x) ix) :=
  Certificates.certificate715750.1 w ρ hρ hF P hP2 hfrob iJ hJ2 hxP hx0 ix hJx hne hsplit
    hoth

theorem tcC1_neg_odd_of_certificate
    (w : WeylGroup Tag.E6) (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = -(w • γ))
    {F : ℕ} (hF : F = 1 ∨ (3 ≤ F ∧ F % 2 = 1))
    (P : Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3)) (hP2 : Module.finrank (ZMod 3) P = 2)
    (hfrob : ∀ v ∈ P, ∀ j : Fin Tag.E6.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod 3) * v k = 2 * v j)
    (iJ : KernelComponent (tcChiPl Tag.E6 3 P))
    (hJ2 : 2 ≤ componentOrbitLength ρ (componentRoots (tcChiPl Tag.E6 3 P) iJ))
    {x : Fin Tag.E6.rank → ZMod 3} (hxP : x ∈ P) (hx0 : x ≠ 0)
    (ix : KernelComponent (tcChiLn Tag.E6 3 x))
    (hJx : componentRoots (tcChiPl Tag.E6 3 P) iJ ⊆ componentRoots (tcChiLn Tag.E6 3 x) ix)
    (hne : componentRoots (tcChiLn Tag.E6 3 x) ix ≠ componentRoots (tcChiPl Tag.E6 3 P) iJ)
    (hsplit : ∃ lab', GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 x) ix)) ∧
      LargeEvenSplit 3 lab')
    (hoth : ∀ d ∈ P, d ≠ 0 → (∀ c : ZMod 3, d ≠ c • x) →
      ∀ i : KernelComponent (tcChiLn Tag.E6 3 d),
      componentRoots (tcChiPl Tag.E6 3 P) iJ ⊆ componentRoots (tcChiLn Tag.E6 3 d) i →
      GGLabelIso (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 d) i))
        (LabAt ρ F (componentRoots (tcChiPl Tag.E6 3 P) iJ)) ∨
      ∃ (c : Prop) (lab' : LargeEvenLabel),
        GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 d) i)) ∧
        LargeEvenHalfSplit 3 lab' c) :
    F = 1 ∧ TcC1RowNegOne ρ (componentRoots (tcChiPl Tag.E6 3 P) iJ)
      (componentRoots (tcChiLn Tag.E6 3 x) ix) :=
  Certificates.certificate715750.2.1 w ρ hρ hF P hP2 hfrob iJ hJ2 hxP hx0 ix hJx hne hsplit
    hoth

theorem tcC1_neg_even_of_certificate
    (w : WeylGroup Tag.E6) (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = -(w • γ))
    {F : ℕ} (hF : 2 ≤ F ∧ F % 2 = 0)
    (P : Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3)) (hP2 : Module.finrank (ZMod 3) P = 2)
    (hfrob : ∀ v ∈ P, ∀ j : Fin Tag.E6.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod 3) * v k = v j)
    (iJ : KernelComponent (tcChiPl Tag.E6 3 P))
    (hJ2 : 2 ≤ componentOrbitLength ρ (componentRoots (tcChiPl Tag.E6 3 P) iJ))
    {x : Fin Tag.E6.rank → ZMod 3} (hxP : x ∈ P) (hx0 : x ≠ 0)
    (ix : KernelComponent (tcChiLn Tag.E6 3 x))
    (hJx : componentRoots (tcChiPl Tag.E6 3 P) iJ ⊆ componentRoots (tcChiLn Tag.E6 3 x) ix)
    (hne : componentRoots (tcChiLn Tag.E6 3 x) ix ≠ componentRoots (tcChiPl Tag.E6 3 P) iJ)
    (hsplit : ∃ lab', GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 x) ix)) ∧
      LargeEvenSplit 3 lab')
    (hoth : ∀ d ∈ P, d ≠ 0 → (∀ c : ZMod 3, d ≠ c • x) →
      ∀ i : KernelComponent (tcChiLn Tag.E6 3 d),
      componentRoots (tcChiPl Tag.E6 3 P) iJ ⊆ componentRoots (tcChiLn Tag.E6 3 d) i →
      GGLabelIso (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 d) i))
        (LabAt ρ F (componentRoots (tcChiPl Tag.E6 3 P) iJ)) ∨
      ∃ (c : Prop) (lab' : LargeEvenLabel),
        GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 d) i)) ∧
        LargeEvenHalfSplit 3 lab' c) :
    TcC1RowNegTwo ρ (componentRoots (tcChiPl Tag.E6 3 P) iJ)
      (componentRoots (tcChiLn Tag.E6 3 x) ix) :=
  Certificates.certificate715750.2.2 w ρ hρ hF P hP2 hfrob iJ hJ2 hxP hx0 ix hJx hne hsplit
    hoth

end CFSG.StandardType.TableCRes
