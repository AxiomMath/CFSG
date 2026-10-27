module

public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningGeneral
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

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

private theorem famNoDiagram_iform_iterate {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup τ L p₀) (n : ℕ) (x y : Fin τ.rank → ℤ) :
    iform ((S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[n] x)
      ((S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[n] y) = iform x y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      S.frob.iform_eq, ih]

private theorem famNoDiagram_iterate_neg {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup τ L p₀) (n : ℕ) (x : Fin τ.rank → ℤ) :
    (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[n] (-x) =
      -((S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      S.frob.neg_eq]

theorem fam_twistInner_of_noDiagram
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (i : KernelComponent χ)
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ)
    (hno : ¬ HasDiagramSymmetryType (componentRoots χ i)) :
    twistInner (componentRoots χ i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots χ i)]) := by
  classical
  have hΨ : IsRootComponent (componentRoots χ i) := isRootComponent_componentRoots i
  have hfin : (kernelRoots χ).Finite := (finite_setOf_isRoot τ).subset fun α hα => hα.1
  obtain ⟨d, hd, hfix⟩ := exists_iterate_eq_of_mapsTo
    (f := (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))) hfin (fun γ hγ => hρ γ hγ)
    S.ρ.injective.injOn
  have himg : (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[d] '' componentRoots χ i =
      componentRoots χ i := by
    apply Set.eq_of_subset_of_subset
    · rintro γ ⟨δ, hδ, rfl⟩
      rw [hfix δ hδ.1]
      exact hδ
    · intro γ hγ
      exact ⟨γ, hγ, hfix γ hγ.1⟩
  have hne : ({s : ℕ | 0 < s ∧
      (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[s] '' componentRoots χ i =
        componentRoots χ i}).Nonempty := ⟨d, hd, himg⟩
  have hspec := Nat.sInf_mem hne
  refine CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds τ (componentRoots χ i) hΨ
    hno ((S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength S.ρ
      (componentRoots χ i)])
    ⟨Set.image_subset_iff.1 (le_of_eq hspec.2), (S.ρ.injective.iterate _).injOn,
      le_of_eq hspec.2.symm⟩ ?_ ?_
  · intro γ _ δ _
    exact famNoDiagram_iform_iterate S _ γ δ
  · intro γ _
    exact famNoDiagram_iterate_neg S _ γ

end CFSG.StandardType.TableCRes
