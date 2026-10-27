module

public import Certificates.Certificate715751

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel LargeEvenSplit LargeEvenHalfSplit)
open CFSG.StandardType (GGLabelIso)

theorem tcC2_of_certificate
    (φ : AddMonoid.End (Fin Tag.E8.rank → ℤ)) (hφ : ∀ x y, iform (φ x) (φ y) = iform x y)
    (hφr : ∀ γ, IsRoot Tag.E8 γ → IsRoot Tag.E8 (φ γ)) (hφ2 : ∀ x, φ (φ x) = -x)
    (ρ : Equiv.Perm (Fin Tag.E8.rank → ℤ)) (hρ : ∀ γ, IsRoot Tag.E8 γ → ρ γ = φ γ)
    {F r : ℕ} (hfl : (r = 2 ∧ (F = 1 ∨ (F % 4 = 1 ∧ 5 ≤ F))) ∨ (r = 3 ∧ F % 4 = 3 ∧ 3 ≤ F))
    (P : Submodule (ZMod 5) (Fin Tag.E8.rank → ZMod 5)) (hP2 : Module.finrank (ZMod 5) P = 2)
    (hfrob : ∀ v ∈ P, ∀ j : Fin Tag.E8.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod 5) * v k = (r : ZMod 5) * v j)
    (iJ : KernelComponent (tcChiPl Tag.E8 5 P))
    (hJ2 : 2 ≤ componentOrbitLength ρ (componentRoots (tcChiPl Tag.E8 5 P) iJ))
    {x : Fin Tag.E8.rank → ZMod 5} (hxP : x ∈ P) (hx0 : x ≠ 0)
    (ix : KernelComponent (tcChiLn Tag.E8 5 x))
    (hJx : componentRoots (tcChiPl Tag.E8 5 P) iJ ⊆ componentRoots (tcChiLn Tag.E8 5 x) ix)
    (hne : componentRoots (tcChiLn Tag.E8 5 x) ix ≠ componentRoots (tcChiPl Tag.E8 5 P) iJ)
    (hsplit : ∃ lab', GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E8 5 x) ix)) ∧
      LargeEvenSplit 5 lab')
    (hoth : ∀ d ∈ P, d ≠ 0 → (∀ c : ZMod 5, d ≠ c • x) →
      ∀ i : KernelComponent (tcChiLn Tag.E8 5 d),
      componentRoots (tcChiPl Tag.E8 5 P) iJ ⊆ componentRoots (tcChiLn Tag.E8 5 d) i →
      GGLabelIso (LabAt ρ F (componentRoots (tcChiLn Tag.E8 5 d) i))
        (LabAt ρ F (componentRoots (tcChiPl Tag.E8 5 P) iJ)) ∨
      ∃ (c : Prop) (lab' : LargeEvenLabel),
        GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E8 5 d) i)) ∧
        LargeEvenHalfSplit 5 lab' c) : False :=
  Certificates.certificate715751 φ hφ hφr hφ2 ρ hρ hfl P hP2 hfrob iJ hJ2 hxP hx0 ix hJx hne
    hsplit hoth

end CFSG.StandardType.TableCRes
