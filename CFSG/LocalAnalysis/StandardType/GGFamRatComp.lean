module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import Certificates.Certificate113
public import Certificates.Certificate114
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

@[expose] def rationalRootsM {τ : Tag} {M : Type*} [CommGroup M]
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (i : KernelComponent χ) : Set (Fin τ.rank → ℤ) :=
  {γ | ∃ (k : ℕ) (δ : Fin τ.rank → ℤ), δ ∈ componentRoots χ i ∧
    γ = (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] δ}

@[expose] noncomputable def rationalSpanM
    {τ : Tag} {L : Type} [Field L] {M : Type*} [CommGroup M]
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (Γ : Subgroup (ModGL τ L))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ) :
    Subgroup (ModGL τ L) :=
  rootSpan τ L (rationalRootsM ρ χ i) ⊓ Γ

@[expose] noncomputable def rationalComponentM
    {τ : Tag} {L : Type} [Field L] {M : Type*} [CommGroup M]
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (Γ : Subgroup (ModGL τ L))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ) :
    Subgroup (ModGL τ L) :=
  ⁅rationalSpanM ρ Γ χ i, rationalSpanM ρ Γ χ i⁆

theorem rationalComponentM_eq
    {τ : Tag} {L : Type} [Field L] (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (Γ : Subgroup (ModGL τ L))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ) (i : KernelComponent χ) :
    rationalComponentM ρ Γ χ i = rationalComponent ρ Γ χ i :=
  rfl

end CFSG.StandardType.TableCRes
