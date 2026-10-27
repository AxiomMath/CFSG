module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
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

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel LargeEvenInLambda2 LargeEvenLieTag)

open Classical in
@[expose] noncomputable def twistKindOf {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (Ψ : Set (Fin τ.rank → ℤ)) : TwistKind :=
  if twistInner Ψ ((ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength ρ Ψ]) then .inner
  else if (compRank Ψ = 6 ∧ Ψ.ncard = 72) ∨
      (compRank Ψ = 4 ∧ Ψ.ncard = 24 ∧
        ¬ twistInner Ψ ((ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[2 * componentOrbitLength ρ Ψ]))
    then .exc
  else if 4 ≤ compRank Ψ ∧ Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1) then .twoD
  else if 2 ≤ compRank Ψ ∧ Ψ.ncard = compRank Ψ * (compRank Ψ + 1) then .suN
  else .inner

@[expose] def componentLabel (r N : ℕ) (k : TwistKind) (n : ℕ) : LargeEvenLabel :=
  match k with
  | .inner =>
    if N = r * (r + 1) then ⟨LargeEvenLieTag.A, r, n⟩
    else if N = 2 * r * (r - 1) then ⟨LargeEvenLieTag.D, r, n⟩
    else if r = 6 then ⟨LargeEvenLieTag.E6, 0, n⟩
    else if r = 7 then ⟨LargeEvenLieTag.E7, 0, n⟩
    else ⟨LargeEvenLieTag.E8, 0, n⟩
  | .suN => ⟨LargeEvenLieTag.twA, r, n⟩
  | .twoD => ⟨LargeEvenLieTag.twD, r, n⟩
  | .exc => if r = 6 then ⟨LargeEvenLieTag.twE6, 0, n⟩ else ⟨LargeEvenLieTag.triD4, 0, n⟩

@[expose] def GGCompLabelAt {G : Type} [Group G] (lab : LargeEvenLabel) (X : Subgroup G) : Prop :=
  LargeEvenInLambda2 lab ∧ CFSG.StandardType.markChar lab = 2 ∧
    CFSG.StandardType.GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) ∧
    ∃ (R : Type) (_ : Group R), CFSG.StandardType.MarkedModel lab R ∧
      Nonempty (↥X ⧸ Subgroup.center ↥X ≃* R)

@[expose] def LangFamilyCompLabel :
    Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ p : ℕ) (S : LangSetup τ L p₀),
    (τ = .E6 ∨ τ = .E8) → p.Prime → p ≠ 2 →
    ∀ (ι : Type) (a : ι → Fin τ.rank → Lˣ),
      (∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) → (∀ u j, a u j ^ p = 1) →
      ∀ K : Subgroup (ModGL τ L),
        IsComponentOf K (S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u))) →
        ∀ i : KernelComponent (Pi.monoidHom fun u => rootCharHom (a u)),
          K ≤ rootSpan τ L {γ | ∃ (k : ℕ) (δ : Fin τ.rank → ℤ),
              δ ∈ componentRoots (Pi.monoidHom fun u => rootCharHom (a u)) i ∧
                γ = (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] δ} →
          ∃ n : ℕ, 2 ^ n = S.D.q ^ componentOrbitLength S.ρ
              (componentRoots (Pi.monoidHom fun u => rootCharHom (a u)) i) ∧
            GGCompLabelAt
              (componentLabel
                (compRank (componentRoots (Pi.monoidHom fun u => rootCharHom (a u)) i))
                (componentRoots (Pi.monoidHom fun u => rootCharHom (a u)) i).ncard
                (twistKindOf S.ρ (componentRoots (Pi.monoidHom fun u => rootCharHom (a u)) i)) n) K

@[expose] def GGTCInputG6InnerDiagLang :
    Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ p : ℕ) (S : LangSetup τ L p₀),
    (τ = .E8 ∨ (τ = .E6 ∧ ¬ 3 ∣ S.D.q - 1)) →
    (∃ w : WeylGroup τ, ∀ γ, IsRoot τ γ → S.ρ γ = w • γ) → p.Prime → p ≠ 2 →
    ∀ d t : Fin τ.rank → Lˣ, rootDiagUnit τ d ∈ S.D.torus → rootDiagUnit τ t ∈ S.D.torus →
      (∀ j, d j ^ p = 1) → (∀ j, t j ^ p = 1) → rootDiagUnit τ d ≠ 1 →
      ∀ K : Subgroup (ModGL τ L), IsComponentOf K (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ d}) →
        CFSG.StandardType.GGInnerDiagOn (Subgroup.zpowers (rootDiagUnit τ t)) K

end CFSG.StandardType.TableCRes

end
