module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDefs
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
public import CFSG.LieType.Steinberg.Adjoint.Pairs
import Certificates.Certificate113
import Certificates.Certificate114
import Certificates.Kernel.TcRes.Sound

public section

namespace Certificates

open CFSG.KD.TcRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.TableCRes in
open CFSG.Assembly (LargeEvenLabel LargeEvenSplit LargeEvenHalfSplit) in
open CFSG.StandardType (GGLabelIso) in
theorem certificate715751 : ∀ (φ : AddMonoid.End (Fin Tag.E8.rank → ℤ)), (∀ x y, iform (φ x) (φ y) = iform x y) →
    (∀ γ, CFSG.Blueprint.Chevalley.IsRoot Tag.E8 γ → CFSG.Blueprint.Chevalley.IsRoot Tag.E8 (φ γ)) → (∀ x, φ (φ x) = -x) →
    ∀ (ρ : Equiv.Perm (Fin Tag.E8.rank → ℤ)), (∀ γ, CFSG.Blueprint.Chevalley.IsRoot Tag.E8 γ → ρ γ = φ γ) →
    ∀ {F r : ℕ}, ((r = 2 ∧ (F = 1 ∨ (F % 4 = 1 ∧ 5 ≤ F))) ∨ (r = 3 ∧ F % 4 = 3 ∧ 3 ≤ F)) →
    ∀ (P : Submodule (ZMod 5) (Fin Tag.E8.rank → ZMod 5)), Module.finrank (ZMod 5) P = 2 →
    (∀ v ∈ P, ∀ j : Fin Tag.E8.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod 5) * v k = (r : ZMod 5) * v j) →
    ∀ (iJ : KernelComponent (tcChiPl Tag.E8 5 P)),
    2 ≤ componentOrbitLength ρ (componentRoots (tcChiPl Tag.E8 5 P) iJ) →
    ∀ {x : Fin Tag.E8.rank → ZMod 5}, x ∈ P → x ≠ 0 →
    ∀ (ix : KernelComponent (tcChiLn Tag.E8 5 x)),
    componentRoots (tcChiPl Tag.E8 5 P) iJ ⊆ componentRoots (tcChiLn Tag.E8 5 x) ix →
    componentRoots (tcChiLn Tag.E8 5 x) ix ≠ componentRoots (tcChiPl Tag.E8 5 P) iJ →
    (∃ lab', GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E8 5 x) ix)) ∧
      LargeEvenSplit 5 lab') →
    (∀ d ∈ P, d ≠ 0 → (∀ c : ZMod 5, d ≠ c • x) →
      ∀ i : KernelComponent (tcChiLn Tag.E8 5 d),
      componentRoots (tcChiPl Tag.E8 5 P) iJ ⊆ componentRoots (tcChiLn Tag.E8 5 d) i →
      GGLabelIso (LabAt ρ F (componentRoots (tcChiLn Tag.E8 5 d) i))
        (LabAt ρ F (componentRoots (tcChiPl Tag.E8 5 P) iJ)) ∨
      ∃ (c : Prop) (lab' : LargeEvenLabel),
        GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E8 5 d) i)) ∧
        LargeEvenHalfSplit 5 lab' c) → False :=
  CFSG.KC.TcRes.certificate715751_of_checks

end Certificates
