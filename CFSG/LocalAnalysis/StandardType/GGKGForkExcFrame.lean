module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LocalAnalysis.StandardType.GGKGForkTransfer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
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

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

structure ExcFrame
    (τ : Tag) (K : Type) [Field K] [Finite K] (p : ℕ) (E : Subgroup (adjointGroup τ K)) where
  D : LangDatum τ (AlgebraicClosure K)
  w : WeylGroup τ
  q_eq : D.q = Nat.card K
  frob : ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
    ∀ g, D.Φ g = Units.map (entrywiseHom Fr) g
  n_eq : D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w
  mem_iff : ∀ x : adjointGroup τ K, x ∈ E ↔ x ^ p = 1 ∧
    D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * D.g0 ∈ D.torus

@[expose] def ExcIsLongest (τ : Tag) (w : WeylGroup τ) : Prop :=
  ∀ α : Fin τ.rank → ℤ, IsRoot τ α → (∀ i, 0 ≤ α i) → ∀ i, (w • α) i ≤ 0

@[expose] def ExcSCTorusInput
    (τ : Tag) (K : Type) [Field K] [Finite K] (p r₀ : ℕ) : Prop :=
  ∀ E : Subgroup (adjointGroup τ K), IsElemAbelian p E → p ^ 3 ≤ Nat.card E →
    p ^ r₀ ≤ Nat.card E →
    (∀ g : adjointGroup τ K, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
    ∃ F : ExcFrame τ K p E, (p ∣ Nat.card K - 1 → F.w = 1) ∧
      (p ∣ Nat.card K + 1 → ExcIsLongest τ F.w)

end CFSG.StandardType
