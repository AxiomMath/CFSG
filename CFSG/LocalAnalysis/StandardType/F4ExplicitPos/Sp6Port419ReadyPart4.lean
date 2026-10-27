module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGTwoSL2
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepAPSp
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompNormal
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Defs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeyl
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LieType.AlgebraicGroups.TangentSpace
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalNormalizer
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Prop98Defs
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
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

@[expose] public section

public section
open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LocalAnalysis.ComponentInitial

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
open scoped CFSG.ConvolutionPoints

public noncomputable section
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.AlgebraicGroups WithConv
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped CFSG.ConvolutionPoints

public section

public section

namespace CFSG.StandardType.F4ExplicitPos.FixedCover
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped commutatorElement
variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem range_eq_derived_fixed_component_pinnedX
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) (σ : L ≃+* L) (z : ModGL τ L)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots χ i) (c : fixSubfield σ) :
    let f := (MulAut.conj z).toMonoidHom.comp
      ((baseChangeGL (fixSubfield σ).subtype).comp
        (componentRootSpan (fixSubfield σ) χ i).subtype)
    f ⟨pinnedX τ (fixSubfield σ) γ c, pinnedX_mem_rootSpan hγ c⟩ =
      z * pinnedX τ L γ (c : L) * z⁻¹ := by
  change (MulAut.conj z).toMonoidHom
      (baseChangeGL (fixSubfield σ).subtype (pinnedX τ (fixSubfield σ) γ c)) =
    z * pinnedX τ L γ (c : L) * z⁻¹
  rw [baseChangeGL_pinnedX]
  show (MulAut.conj z) (pinnedX τ L γ ((fixSubfield σ).subtype c)) =
    z * pinnedX τ L γ (c : L) * z⁻¹
  rw [MulAut.conj_apply, fixSubfield_subtype_apply]

end CFSG.StandardType.F4ExplicitPos.FixedCover

public section

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups

public section

open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

namespace CFSG.StandardType.F4ExplicitPos.DistinguishedL

variable {X : Type} [Group X] [Finite X]

variable {n f : ℕ} {p : ℕ}

variable {G₀ B₁ D J L : Subgroup X} {x : X}

theorem f4_distinguished_L_cyclic_centralizer
    {ψ : (ggU .F4 n f).K →* X}
    (hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x) :
    ∃ d ∈ D, d ≠ 1 ∧ d ∉ Subgroup.centralizer (L : Set X) ∧
      Subgroup.closure ({x, d} : Set X) = D ∧
      L ⊓ Subgroup.centralizer (D : Set X) =
        L ⊓ Subgroup.centralizer ({d} : Set X) ∧
      CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set X)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  have hLx : L ≤ Subgroup.centralizer ({x} : Set X) := h20.1.trans inf_le_right
  have hxCL : x ∈ Subgroup.centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ Subgroup.centralizer ({x} : Set X) := hLx hy
    rw [Subgroup.mem_centralizer_iff] at hy'
    exact (hy' x rfl).symm
  obtain ⟨d, hdD, hdCL⟩ : ∃ d : X, d ∈ D ∧ d ∉ Subgroup.centralizer (L : Set X) := by
    by_contra h
    apply h22
    rw [SetLike.le_def]
    intro y hy
    by_contra hyC
    exact h ⟨y, hy, hyC⟩
  have hd1 : d ≠ 1 := by
    intro hd
    exact hdCL (hd ▸ Subgroup.one_mem _)
  have hzx : Subgroup.zpowers x ≤ Subgroup.centralizer (L : Set X) :=
    Subgroup.zpowers_le.mpr hxCL
  have hdzx : d ∉ Subgroup.zpowers x := fun hd => hdCL (hzx hd)
  have hxp : x ^ p = 1 := h9.2 x (h11 h17)
  have hgen : Subgroup.closure ({x, d} : Set X) = D :=
    ggClosure_pair_eq h5 h12 h17 hdD h18 hxp hdzx
  have hcentral : L ⊓ Subgroup.centralizer (D : Set X) =
      L ⊓ Subgroup.centralizer ({d} : Set X) := by
    conv_lhs => rw [← hgen]
    rw [ggCentralizer_closure_pair, ← inf_assoc, inf_eq_left.mpr hLx]
  have hJcomp : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set X)) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le h15
      (le_inf h21 (h15.1.trans inf_le_right))
      (inf_le_inf_right (Subgroup.centralizer (D : Set X)) h19)
  have hJcomp' : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set X)) := by
    rw [← hcentral]
    exact hJcomp
  exact ⟨d, hdD, hd1, hdCL, hgen, hcentral, hJcomp'⟩

end CFSG.StandardType.F4ExplicitPos.DistinguishedL

end
end
end
end
end
end
end
end

end
