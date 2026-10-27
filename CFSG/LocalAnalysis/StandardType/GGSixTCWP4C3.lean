
module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDefs
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
public import CFSG.LieType.Steinberg.Adjoint.Pairs

public import Certificates.Certificate715752

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel LargeEvenSplit LargeEvenHalfSplit)
open CFSG.StandardType (GGLabelIso)

theorem tcC3_of_certificate
    {p : ℕ} [Fact p.Prime] (hp13 : 13 ≤ p) {F : ℕ} (hF4 : orderOf ((2 : ZMod p) ^ F) = 4)
    (φ : AddMonoid.End (Fin Tag.E8.rank → ℤ)) (hφ : ∀ x y, iform (φ x) (φ y) = iform x y)
    (hφr : ∀ γ, IsRoot Tag.E8 γ → IsRoot Tag.E8 (φ γ)) (hφ2 : ∀ x, φ (φ x) = -x)
    (ρ : Equiv.Perm (Fin Tag.E8.rank → ℤ)) (hρ : ∀ x, ρ x = φ x)
    (P : Submodule (ZMod p) (Fin Tag.E8.rank → ZMod p)) (hP2 : Module.finrank (ZMod p) P = 2)
    (hfrob : ∀ v ∈ P, ∀ j : Fin Tag.E8.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod p) * v k = ((2 ^ F : ℕ) : ZMod p) * v j)
    (iJ : KernelComponent (tcChiPl Tag.E8 p P))
    (hJ2 : 2 ≤ componentOrbitLength ρ (componentRoots (tcChiPl Tag.E8 p P) iJ))
    (hab : ∃ a ∈ componentRoots (tcChiPl Tag.E8 p P) iJ,
      ∃ b ∈ componentRoots (tcChiPl Tag.E8 p P) iJ, iform a b = -1)
    {x : Fin Tag.E8.rank → ZMod p} (hxP : x ∈ P) (hx0 : x ≠ 0)
    (ix : KernelComponent (tcChiLn Tag.E8 p x))
    (hJx : componentRoots (tcChiPl Tag.E8 p P) iJ ⊆ componentRoots (tcChiLn Tag.E8 p x) ix)
    (hne : componentRoots (tcChiLn Tag.E8 p x) ix ≠ componentRoots (tcChiPl Tag.E8 p P) iJ)
    (hsplit : ∃ lab', GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E8 p x) ix)) ∧
      LargeEvenSplit p lab')
    (hoth : ∀ d ∈ P, d ≠ 0 → (∀ c : ZMod p, d ≠ c • x) →
      ∀ i : KernelComponent (tcChiLn Tag.E8 p d),
      componentRoots (tcChiPl Tag.E8 p P) iJ ⊆ componentRoots (tcChiLn Tag.E8 p d) i →
      GGLabelIso (LabAt ρ F (componentRoots (tcChiLn Tag.E8 p d) i))
        (LabAt ρ F (componentRoots (tcChiPl Tag.E8 p P) iJ)) ∨
      ∃ (c : Prop) (lab' : LargeEvenLabel),
        GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E8 p d) i)) ∧
        LargeEvenHalfSplit p lab' c) : False :=
  Certificates.certificate715752 hp13 hF4 φ hφ hφr hφ2 ρ hρ P hP2 hfrob iJ hJ2 hab hxP hx0
    ix hJx hne hsplit hoth

end CFSG.StandardType.TableCRes
