
module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDefs
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
public import CFSG.LieType.Steinberg.Adjoint.Pairs
import CFSG.Blueprint.ChevalleyRootsInputs
import CFSG.Blueprint.ChevalleyStringsInputs
import Certificates.Kernel.TcRes.Sound

public section

namespace Certificates

open CFSG.KD.TcRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.TableCRes in
open CFSG.Assembly (LargeEvenLabel LargeEvenSplit LargeEvenHalfSplit) in
open CFSG.StandardType (GGLabelIso) in
theorem certificate715752 : ∀ {p : ℕ} [Fact p.Prime], 13 ≤ p → ∀ {F : ℕ}, orderOf ((2 : ZMod p) ^ F) = 4 →
    ∀ (φ : AddMonoid.End (Fin Tag.E8.rank → ℤ)), (∀ x y, iform (φ x) (φ y) = iform x y) →
    (∀ γ, CFSG.Blueprint.Chevalley.IsRoot Tag.E8 γ → CFSG.Blueprint.Chevalley.IsRoot Tag.E8 (φ γ)) → (∀ x, φ (φ x) = -x) →
    ∀ (ρ : Equiv.Perm (Fin Tag.E8.rank → ℤ)), (∀ x, ρ x = φ x) →
    ∀ (P : Submodule (ZMod p) (Fin Tag.E8.rank → ZMod p)), Module.finrank (ZMod p) P = 2 →
    (∀ v ∈ P, ∀ j : Fin Tag.E8.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod p) * v k = ((2 ^ F : ℕ) : ZMod p) * v j) →
    ∀ (iJ : KernelComponent (tcChiPl Tag.E8 p P)),
    2 ≤ componentOrbitLength ρ (componentRoots (tcChiPl Tag.E8 p P) iJ) →
    (∃ a ∈ componentRoots (tcChiPl Tag.E8 p P) iJ,
      ∃ b ∈ componentRoots (tcChiPl Tag.E8 p P) iJ, iform a b = -1) →
    ∀ {x : Fin Tag.E8.rank → ZMod p}, x ∈ P → x ≠ 0 →
    ∀ (ix : KernelComponent (tcChiLn Tag.E8 p x)),
    componentRoots (tcChiPl Tag.E8 p P) iJ ⊆ componentRoots (tcChiLn Tag.E8 p x) ix →
    componentRoots (tcChiLn Tag.E8 p x) ix ≠ componentRoots (tcChiPl Tag.E8 p P) iJ →
    (∃ lab', GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E8 p x) ix)) ∧
      LargeEvenSplit p lab') →
    (∀ d ∈ P, d ≠ 0 → (∀ c : ZMod p, d ≠ c • x) →
      ∀ i : KernelComponent (tcChiLn Tag.E8 p d),
      componentRoots (tcChiPl Tag.E8 p P) iJ ⊆ componentRoots (tcChiLn Tag.E8 p d) i →
      GGLabelIso (LabAt ρ F (componentRoots (tcChiLn Tag.E8 p d) i))
        (LabAt ρ F (componentRoots (tcChiPl Tag.E8 p P) iJ)) ∨
      ∃ (c : Prop) (lab' : LargeEvenLabel),
        GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E8 p d) i)) ∧
        LargeEvenHalfSplit p lab' c) → False :=
  CFSG.KC.TcRes.certificate715752_of_checks

end Certificates
