module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDefs
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RRows
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
public import CFSG.LieType.Chevalley.WeylRoots
import Certificates.Certificate113
import Certificates.Certificate114
import Certificates.Kernel.TcRes.Sound

public section

namespace Certificates

open CFSG.KD.TcRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.TableCRes in
open CFSG.Assembly (LargeEvenLabel LargeEvenSplit LargeEvenHalfSplit) in
open CFSG.StandardType (GGLabelIso) in
theorem certificate715750 : (∀ (w : CFSG.LieType.Chevalley.WeylGroup Tag.E6) (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)),
    (∀ γ, CFSG.Blueprint.Chevalley.IsRoot Tag.E6 γ → ρ γ = w • γ) →
    ∀ {F : ℕ}, (F = 1 ∨ (3 ≤ F ∧ F % 2 = 1)) →
    ∀ (P : Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3)), Module.finrank (ZMod 3) P = 2 →
    (∀ v ∈ P, ∀ j : Fin Tag.E6.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod 3) * v k = 2 * v j) →
    ∀ (iJ : KernelComponent (tcChiPl Tag.E6 3 P)),
    2 ≤ componentOrbitLength ρ (componentRoots (tcChiPl Tag.E6 3 P) iJ) →
    ∀ {x : Fin Tag.E6.rank → ZMod 3}, x ∈ P → x ≠ 0 →
    ∀ (ix : KernelComponent (tcChiLn Tag.E6 3 x)),
    componentRoots (tcChiPl Tag.E6 3 P) iJ ⊆ componentRoots (tcChiLn Tag.E6 3 x) ix →
    componentRoots (tcChiLn Tag.E6 3 x) ix ≠ componentRoots (tcChiPl Tag.E6 3 P) iJ →
    (∃ lab', GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 x) ix)) ∧
      LargeEvenSplit 3 lab') →
    (∀ d ∈ P, d ≠ 0 → (∀ c : ZMod 3, d ≠ c • x) →
      ∀ i : KernelComponent (tcChiLn Tag.E6 3 d),
      componentRoots (tcChiPl Tag.E6 3 P) iJ ⊆ componentRoots (tcChiLn Tag.E6 3 d) i →
      GGLabelIso (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 d) i))
        (LabAt ρ F (componentRoots (tcChiPl Tag.E6 3 P) iJ)) ∨
      ∃ (c : Prop) (lab' : LargeEvenLabel),
        GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 d) i)) ∧
        LargeEvenHalfSplit 3 lab' c) →
    F = 1 ∧ TcC1Row ρ (componentRoots (tcChiPl Tag.E6 3 P) iJ)
      (componentRoots (tcChiLn Tag.E6 3 x) ix)) ∧
  (∀ (w : CFSG.LieType.Chevalley.WeylGroup Tag.E6) (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)),
    (∀ γ, CFSG.Blueprint.Chevalley.IsRoot Tag.E6 γ → ρ γ = -(w • γ)) →
    ∀ {F : ℕ}, (F = 1 ∨ (3 ≤ F ∧ F % 2 = 1)) →
    ∀ (P : Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3)), Module.finrank (ZMod 3) P = 2 →
    (∀ v ∈ P, ∀ j : Fin Tag.E6.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod 3) * v k = 2 * v j) →
    ∀ (iJ : KernelComponent (tcChiPl Tag.E6 3 P)),
    2 ≤ componentOrbitLength ρ (componentRoots (tcChiPl Tag.E6 3 P) iJ) →
    ∀ {x : Fin Tag.E6.rank → ZMod 3}, x ∈ P → x ≠ 0 →
    ∀ (ix : KernelComponent (tcChiLn Tag.E6 3 x)),
    componentRoots (tcChiPl Tag.E6 3 P) iJ ⊆ componentRoots (tcChiLn Tag.E6 3 x) ix →
    componentRoots (tcChiLn Tag.E6 3 x) ix ≠ componentRoots (tcChiPl Tag.E6 3 P) iJ →
    (∃ lab', GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 x) ix)) ∧
      LargeEvenSplit 3 lab') →
    (∀ d ∈ P, d ≠ 0 → (∀ c : ZMod 3, d ≠ c • x) →
      ∀ i : KernelComponent (tcChiLn Tag.E6 3 d),
      componentRoots (tcChiPl Tag.E6 3 P) iJ ⊆ componentRoots (tcChiLn Tag.E6 3 d) i →
      GGLabelIso (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 d) i))
        (LabAt ρ F (componentRoots (tcChiPl Tag.E6 3 P) iJ)) ∨
      ∃ (c : Prop) (lab' : LargeEvenLabel),
        GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 d) i)) ∧
        LargeEvenHalfSplit 3 lab' c) →
    F = 1 ∧ TcC1RowNegOne ρ (componentRoots (tcChiPl Tag.E6 3 P) iJ)
      (componentRoots (tcChiLn Tag.E6 3 x) ix)) ∧
  (∀ (w : CFSG.LieType.Chevalley.WeylGroup Tag.E6) (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)),
    (∀ γ, CFSG.Blueprint.Chevalley.IsRoot Tag.E6 γ → ρ γ = -(w • γ)) →
    ∀ {F : ℕ}, (2 ≤ F ∧ F % 2 = 0) →
    ∀ (P : Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3)), Module.finrank (ZMod 3) P = 2 →
    (∀ v ∈ P, ∀ j : Fin Tag.E6.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod 3) * v k = v j) →
    ∀ (iJ : KernelComponent (tcChiPl Tag.E6 3 P)),
    2 ≤ componentOrbitLength ρ (componentRoots (tcChiPl Tag.E6 3 P) iJ) →
    ∀ {x : Fin Tag.E6.rank → ZMod 3}, x ∈ P → x ≠ 0 →
    ∀ (ix : KernelComponent (tcChiLn Tag.E6 3 x)),
    componentRoots (tcChiPl Tag.E6 3 P) iJ ⊆ componentRoots (tcChiLn Tag.E6 3 x) ix →
    componentRoots (tcChiLn Tag.E6 3 x) ix ≠ componentRoots (tcChiPl Tag.E6 3 P) iJ →
    (∃ lab', GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 x) ix)) ∧
      LargeEvenSplit 3 lab') →
    (∀ d ∈ P, d ≠ 0 → (∀ c : ZMod 3, d ≠ c • x) →
      ∀ i : KernelComponent (tcChiLn Tag.E6 3 d),
      componentRoots (tcChiPl Tag.E6 3 P) iJ ⊆ componentRoots (tcChiLn Tag.E6 3 d) i →
      GGLabelIso (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 d) i))
        (LabAt ρ F (componentRoots (tcChiPl Tag.E6 3 P) iJ)) ∨
      ∃ (c : Prop) (lab' : LargeEvenLabel),
        GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 d) i)) ∧
        LargeEvenHalfSplit 3 lab' c) →
    TcC1RowNegTwo ρ (componentRoots (tcChiPl Tag.E6 3 P) iJ)
      (componentRoots (tcChiLn Tag.E6 3 x) ix)) :=
  CFSG.KC.TcRes.certificate715750_of_checks

end Certificates
