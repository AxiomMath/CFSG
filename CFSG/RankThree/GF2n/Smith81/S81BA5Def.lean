module

public import CFSG.RankThree.GF2n.Smith81.S81A5Fixed
public import CFSG.RankThree.GF2n.Smith81.S81BGeom
public import CFSG.Open.StatedDefs
public import CFSG.CGT.Timmesfeld75.Forms
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.GroupTheory.HuppertProduct.Quotient
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.GF2n.Smith81.Bridge
public import CFSG.RankThree.GF2n.Smith81.TiFusion
public import CFSG.RankThree.GF2n.Stroth80.Consumers
public import CFSG.RankThree.GF2n.Stroth80.FrobClause
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec36
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.RankThree.GF2n.Tim81.Components
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.RankOne

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower CFSG.Open CFSG.RankThree.GF2n.Smith81.EGeom

variable (K : Type) [Field K]

@[expose] def rhoEquiv : GL (Fin 6) K →* (Cube K ≃ₗ[K] Cube K) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Cube K)).toMonoidHom.comp
    (TauCeti.extPowerRep K 6 3).asGroupHom

variable {K}

theorem rhoEquiv_apply (g : GL (Fin 6) K) (ξ : Cube K) : rhoEquiv K g ξ = rho K g ξ := rfl

variable (K)

@[expose] def Gam : Subgroup (Cube K ≃ₗ[K] Cube K) := (StatedSL 6 K).map (rhoEquiv K)

@[expose] def S024 : Set.powersetCard (Fin 6) 3 :=
  tripleSet 0 2 4 (by decide) (by decide) (by decide)

@[expose] def S034 : Set.powersetCard (Fin 6) 3 :=
  tripleSet 0 3 4 (by decide) (by decide) (by decide)

@[expose] def p0 : Cube K := cubeBasis K S024

@[expose] def r0 : Cube K := cubeBasis K S034

@[expose] def rootSet : Set (Cube K ≃ₗ[K] Cube K) :=
  {u | ∃ (a b : Fin 6) (hab : a.val % 2 = 0 ∧ b.val % 2 = 1) (c : K),
    u = rhoEquiv K (transvGL K a b (fun h => by
      subst h; have h1 := hab.1; have h2 := hab.2; omega) c)}

@[expose] def U0 : Subgroup (Cube K ≃ₗ[K] Cube K) := Subgroup.closure (rootSet K)

end CFSG.RankThree.GF2n.Smith81.A5Cube
