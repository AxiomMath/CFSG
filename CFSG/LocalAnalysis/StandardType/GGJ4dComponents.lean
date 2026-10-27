module

public import CFSG.LocalAnalysis.StandardType.GGJ4dOrthogonalRank
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

public noncomputable section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

def FConn (F : Set (Fin τ.rank → ℤ)) (x y : Fin τ.rank → ℤ) : Prop :=
  Relation.ReflTransGen (fun a b => a ∈ F ∧ b ∈ F ∧ iform a b ≠ 0) x y

def FComp (F : Set (Fin τ.rank → ℤ)) (α : Fin τ.rank → ℤ) : Set (Fin τ.rank → ℤ) :=
  {β | β ∈ F ∧ FConn F α β}

private theorem FConn_symm
    {F : Set (Fin τ.rank → ℤ)} {x y : Fin τ.rank → ℤ}
    (h : FConn F x y) : FConn F y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hstep ih =>
      exact Relation.ReflTransGen.head ⟨hstep.2.1, hstep.1, by
        rw [iform_comm]
        exact hstep.2.2⟩ ih

private theorem FConn_neg
    {F : Set (Fin τ.rank → ℤ)} (hFneg : ∀ x ∈ F, -x ∈ F)
    {x y : Fin τ.rank → ℤ} (h : FConn F x y) : FConn F (-x) (-y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hstep ih =>
      refine ih.tail ⟨hFneg b hstep.1, hFneg c hstep.2.1, ?_⟩
      have hform : iform (-b) (-c) = iform b c := by
        rw [← neg_one_smul ℤ b, ← neg_one_smul ℤ c, iform_smul_left, iform_smul_right]
        ring
      rw [hform]
      exact hstep.2.2

private theorem mem_of_mem_of_FConn
    {F : Set (Fin τ.rank → ℤ)} {α : Fin τ.rank → ℤ}
    {S : Set (Fin τ.rank → ℤ)}
    (hSsub : S ⊆ FComp F α)
    (horth : ∀ x ∈ S, ∀ y ∈ FComp F α, y ∉ S → iform x y = 0)
    {x y : Fin τ.rank → ℤ} (h : FConn F x y) (hx : x ∈ FComp F α) (hy : y ∈ S) : x ∈ S := by
  revert hx
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun _ => hy
  | head hstep hrest ih =>
      intro hx
      have hcS : _ ∈ S := ih ⟨hstep.2.1, hx.2.tail hstep⟩
      by_contra hxS
      exact hstep.2.2 (by
        rw [iform_comm]
        exact horth _ hcS _ hx hxS)

theorem j4d_fcomp_isRootComponent
    {τ : Tag} {F : Set (Fin τ.rank → ℤ)} {α : Fin τ.rank → ℤ}
    (hFroot : ∀ x ∈ F, IsRoot τ x)
    (hFneg : ∀ x ∈ F, -x ∈ F)
    (hFadd : ∀ x ∈ F, ∀ y ∈ F, IsRoot τ (x + y) → x + y ∈ F)
    (hFrefl : ∀ x ∈ F, ∀ y ∈ F, rootReflection y • x ∈ F)
    (hα : α ∈ F) :
    IsRootComponent (FComp F α) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro β hβ
    exact hFroot β hβ.1
  ·
    intro β hβ
    have hαroot : IsRoot τ α := hFroot α hα
    have hαα : iform α α ≠ 0 := (iform_self_pos hαroot.ne_zero).ne'
    have hαneg : FConn F α (-α) := by
      refine Relation.ReflTransGen.single ⟨hα, hFneg α hα, ?_⟩
      have hform : iform α (-α) = -iform α α := by
        rw [← neg_one_smul ℤ α, iform_smul_right]
        ring
      rwa [hform, neg_ne_zero]
    refine ⟨hFneg β hβ.1, hαneg.trans (FConn_neg hFneg hβ.2)⟩
  ·
    intro x hx y hy hxy
    have hxF : x ∈ F := hx.1
    have hyF : y ∈ F := hy.1
    have hsumF : x + y ∈ F := hFadd x hxF y hyF hxy
    refine ⟨hsumF, ?_⟩
    have hpos := iform_self_pos_of_isRoot hxy
    rw [iform_add_right] at hpos
    by_cases hx0 : iform (x + y) x = 0
    · rw [hx0, zero_add] at hpos
      exact hy.2.trans (Relation.ReflTransGen.single ⟨hyF, hsumF, by
        rw [iform_comm]
        exact hpos.ne'⟩)
    · exact hx.2.trans (Relation.ReflTransGen.single ⟨hxF, hsumF, by
        rw [iform_comm]
        exact hx0⟩)
  ·
    intro x hx y hy
    have hxF : x ∈ F := hx.1
    have hyF : y ∈ F := hy.1
    have hyroot : IsRoot τ y := hFroot y hyF
    have hrefF : rootReflection y • x ∈ F := hFrefl x hxF y hyF
    refine ⟨hrefF, ?_⟩
    by_cases h0 : iform x y = 0
    · have hfix : rootReflection y • x = x :=
        rootReflection_smul_of_iform_eq_zero hyroot (by rwa [iform_comm] at h0)
      rw [hfix]
      exact hx.2
    · have hadj : iform (rootReflection y • x) y ≠ 0 := by
        intro hzero
        have h1 := iform_smul (rootReflection y) x y
        rw [rootReflection_smul_self hyroot, ← neg_one_smul ℤ y, iform_smul_right] at h1
        rw [hzero, mul_zero] at h1
        exact h0 h1.symm
      exact hy.2.trans (Relation.ReflTransGen.single ⟨hyF, hrefF, by
        rw [iform_comm]
        exact hadj⟩)
  ·
    intro S hSsub horth
    by_cases hS : S = ∅
    · exact Or.inl hS
    · right
      obtain ⟨γ, hγS⟩ := Set.nonempty_iff_ne_empty.2 hS
      have hγF : γ ∈ FComp F α := hSsub hγS
      have hαS : α ∈ S :=
        mem_of_mem_of_FConn hSsub horth hγF.2 ⟨hα, Relation.ReflTransGen.refl⟩ hγS
      refine Set.Subset.antisymm hSsub ?_
      intro β hβ
      exact mem_of_mem_of_FConn hSsub horth (FConn_symm hβ.2) hβ hαS

end CFSG.StandardType.LangRat

end
