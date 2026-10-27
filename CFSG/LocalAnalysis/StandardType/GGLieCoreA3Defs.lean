module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenAltProof
public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
public import CFSG.LocalAnalysis.StandardType.GGFinModelRoots
public import CFSG.LocalAnalysis.StandardType.GGFinModelRat
public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGLatRootBridge

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

@[expose] def GGLieA3Alg :
    Prop :=
  ∀ (t : StatedLieTag), (t = .E6 ∨ t = .F4 ∨ t = .twistedE6) →
    ∀ (f : ℕ), 1 ≤ f → ∀ A K : Subgroup (ModGL (langTag t) GGL),
      A ≤ ggFixGp t f → IsElemAbelian 3 A → Nat.card A = 3 ^ 2 →
      IsComponentOf K (⁅ggFixGp t f, ggFixGp t f⁆ ⊓
        Subgroup.centralizer (A : Set (ModGL (langTag t) GGL))) →
      GGSixLSevenA3Case K →
      (t = .E6 → f = 1 ∧
        ∃ h ∈ ⁅ggFixGp t f, ggFixGp t f⁆, A.map (MulAut.conj h).toMonoidHom ≤ K) ∧
      (t = .F4 ∨ t = .twistedE6 → False)

@[expose] def GGLieA3AlgToral :
    Prop :=
  ∀ (t : StatedLieTag), (t = .E6 ∨ t = .F4 ∨ t = .twistedE6) →
    ∀ (f : ℕ), 1 ≤ f → ∀ A K : Subgroup (ModGL (langTag t) GGL),
      A ≤ ggFixGp t f → IsElemAbelian 3 A → Nat.card A = 3 ^ 2 →
      IsToralSubgroup (langTag t) GGL A →
      IsComponentOf K (⁅ggFixGp t f, ggFixGp t f⁆ ⊓
        Subgroup.centralizer (A : Set (ModGL (langTag t) GGL))) →
      GGSixLSevenA3Case K →
      (t = .E6 → f = 1 ∧
        ∃ h ∈ ⁅ggFixGp t f, ggFixGp t f⁆, A.map (MulAut.conj h).toMonoidHom ≤ K) ∧
      (t = .F4 ∨ t = .twistedE6 → False)

end CFSG.StandardType.LieCore
