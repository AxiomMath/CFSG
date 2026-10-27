module

public import CFSG.LocalAnalysis.StandardType.GGFinModelInput
public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)

@[expose] def ggLiePair {r : ℕ} (γ : Fin r → ℤ) (c : Fin r → ZMod 3) : ZMod 3 :=
  ∑ i, (γ i : ZMod 3) * c i

@[expose] def GGLieA3DatumHyp
    (t : StatedLieTag) (hΦ : IsSteinbergEnd (langTag t) GGL (2 ^ 1) (ggPhi t 1))
    (w : WeylGroup (langTag t)) (g : ModGL (langTag t) GGL)
    (hg : g ∈ adjointGroup (langTag t) GGL)
    (hlang : ggPhi t 1 g = g * canonicalRep (coxeterSystem (langTag t)) GGL w)
    (a₁ a₂ : Fin (langTag t).rank → GGLˣ) (ρ : Equiv.Perm (Fin (langTag t).rank → ℤ))
    (i : KernelComponent (jointChar a₁ a₂)) : Prop :=
  FrobRootMap (langDatumOfPosition hΦ w g hg hlang) ρ ∧
  rootDiagUnit (langTag t) a₁ ∈ (langDatumOfPosition hΦ w g hg hlang).torus ∧
  rootDiagUnit (langTag t) a₂ ∈ (langDatumOfPosition hΦ w g hg hlang).torus ∧
  rootDiagUnit (langTag t) a₁ ^ 3 = 1 ∧ rootDiagUnit (langTag t) a₂ ^ 3 = 1 ∧
  Nat.card (Subgroup.closure {rootDiagUnit (langTag t) a₁, rootDiagUnit (langTag t) a₂}) = 3 ^ 2 ∧
  compRank (componentRoots (jointChar a₁ a₂) i) = 3 ∧
  (componentRoots (jointChar a₁ a₂) i).ncard = 12 ∧
  (fun u => ρ u) '' componentRoots (jointChar a₁ a₂) i = componentRoots (jointChar a₁ a₂) i ∧
  twistInner (componentRoots (jointChar a₁ a₂) i) (fun u => ρ u)

@[expose] def GGLieA3DatumNo : Prop :=
  ∀ (t : StatedLieTag), (t = .F4 ∨ t = .twistedE6) →
    ∀ (hΦ : IsSteinbergEnd (langTag t) GGL (2 ^ 1) (ggPhi t 1)) (w : WeylGroup (langTag t))
      (g : ModGL (langTag t) GGL) (hg : g ∈ adjointGroup (langTag t) GGL)
      (hlang : ggPhi t 1 g = g * canonicalRep (coxeterSystem (langTag t)) GGL w)
      (a₁ a₂ : Fin (langTag t).rank → GGLˣ) (ρ : Equiv.Perm (Fin (langTag t).rank → ℤ))
      (i : KernelComponent (jointChar a₁ a₂)),
      GGLieA3DatumHyp t hΦ w g hg hlang a₁ a₂ ρ i → False

@[expose] def GGLieA3DatumE6 : Prop :=
  ∀ (hΦ : IsSteinbergEnd (langTag .E6) GGL (2 ^ 1) (ggPhi .E6 1)) (w : WeylGroup (langTag .E6))
    (g : ModGL (langTag .E6) GGL) (hg : g ∈ adjointGroup (langTag .E6) GGL)
    (hlang : ggPhi .E6 1 g = g * canonicalRep (coxeterSystem (langTag .E6)) GGL w)
    (a₁ a₂ : Fin (langTag .E6).rank → GGLˣ) (ρ : Equiv.Perm (Fin (langTag .E6).rank → ℤ))
    (i : KernelComponent (jointChar a₁ a₂)),
    GGLieA3DatumHyp .E6 hΦ w g hg hlang a₁ a₂ ρ i →
      ∃ h ∈ (langDatumOfPosition hΦ w g hg hlang).Γ,
        (Subgroup.closure {rootDiagUnit (langTag .E6) a₁, rootDiagUnit (langTag .E6) a₂}).map
            (MulAut.conj h).toMonoidHom ≤
          ratComp (fun u => ρ u) (langDatumOfPosition hΦ w g hg hlang).Γ
            (componentRoots (jointChar a₁ a₂) i)

@[expose] def GGLieA3LatticeNo : Prop :=
  ∀ (t : StatedLieTag), (t = .F4 ∨ t = .twistedE6) →
    ∀ (w : WeylGroup (langTag t)) (a₁ a₂ : Fin (langTag t).rank → GGLˣ),
      (∀ i, a₁ i ^ 3 = 1) → (∀ i, a₂ i ^ 3 = 1) →
      (∀ γ, IsRoot (langTag t) γ →
        rootChar a₁ (w • ggGraphLat t γ) = rootChar a₁ γ ^ 2) →
      (∀ γ, IsRoot (langTag t) γ →
        rootChar a₂ (w • ggGraphLat t γ) = rootChar a₂ γ ^ 2) →
      Nat.card (Subgroup.closure {rootDiagUnit (langTag t) a₁, rootDiagUnit (langTag t) a₂}) =
        3 ^ 2 →
      ∀ i : KernelComponent (jointChar a₁ a₂),
        (componentRoots (jointChar a₁ a₂) i).ncard = 12 →
        (fun u => w • ggGraphLat t u) '' componentRoots (jointChar a₁ a₂) i =
          componentRoots (jointChar a₁ a₂) i →
        twistInner (componentRoots (jointChar a₁ a₂) i) (fun u => w • ggGraphLat t u) → False

end CFSG.StandardType.LieCore
