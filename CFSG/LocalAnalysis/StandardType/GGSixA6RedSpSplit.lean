module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaSplit
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj
public import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteenFourteenP
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)
open CFSG.StandardType.LayerCores

private theorem ggA6_sp_avg_selfadj {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V] (B : BilinForm F V) (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]
    (hAB : A ≤ TauCeti.BilinForm.isometryGroup B) (v w : V) :
    B (OrthSplit.avg A v) w = B v (OrthSplit.avg A w) := by
  rw [OrthSplit.avg_apply, OrthSplit.avg_apply, map_smul, LinearMap.smul_apply, map_smul,
    map_sum, map_sum, LinearMap.sum_apply]
  congr 1
  refine Fintype.sum_equiv (Equiv.inv A) _ _ fun a => ?_
  calc B ((a : V ≃ₗ[F] V) v) w
      = B ((a : V ≃ₗ[F] V) v)
          ((a : V ≃ₗ[F] V) (((a⁻¹ : A) : V ≃ₗ[F] V) w)) := by
        rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
        rfl
    _ = B v (((a⁻¹ : A) : V ≃ₗ[F] V) w) :=
        TauCeti.BilinForm.mem_isometryGroup_iff.mp (hAB a.2) _ _

private theorem ggA6_sp_fixed_eq {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hA : (Fintype.card A : F) ≠ 0) :
    ggA6SpFixed A = OrthSplit.fixSp A := by
  ext v
  change (∀ a ∈ A, a v = v) ↔ v ∈ OrthSplit.fixSp A
  exact (OrthSplit.mem_fixSp_iff hA).symm

private theorem ggA6_sp_fix_orth_free {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V] (B : BilinForm F V) (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]
    (hA : (Fintype.card A : F) ≠ 0) (hAB : A ≤ TauCeti.BilinForm.isometryGroup B) :
    ∀ x ∈ ggA6SpFixed A, ∀ y ∈ OrthSplit.freeSp A, B x y = 0 := by
  intro x hx y hy
  rw [ggA6_sp_fixed_eq A hA] at hx
  obtain ⟨u, rfl⟩ := hx
  rw [ggA6_sp_avg_selfadj B A hAB]
  rw [LinearMap.mem_ker.mp hy, map_zero]

private theorem ggA6_sp_orthogonal_eq_freeSp {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V] (B : BilinForm F V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hA : (Fintype.card A : F) ≠ 0)
    (hAB : A ≤ TauCeti.BilinForm.isometryGroup B) :
    B.orthogonal (ggA6SpFixed A) = OrthSplit.freeSp A := by
  apply le_antisymm
  · intro v hv
    rw [OrthSplit.freeSp, LinearMap.mem_ker]
    refine hnd.1 (OrthSplit.avg A v) fun w => ?_
    rw [ggA6_sp_avg_selfadj B A hAB]
    have hw : OrthSplit.avg A w ∈ ggA6SpFixed A := by
      rw [ggA6_sp_fixed_eq A hA]
      exact OrthSplit.avg_mem_fixSp w
    exact (hB.isRefl.eq_iff).mpr (LinearMap.BilinForm.mem_orthogonal_iff.mp hv _ hw)
  · intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [ggA6_sp_fixed_eq A hA, OrthSplit.fixSp] at hn
    obtain ⟨u, rfl⟩ := hn
    rw [ggA6_sp_avg_selfadj B A hAB]
    rw [LinearMap.mem_ker.mp hv, map_zero]

theorem ggA6_sp_fixed_nondegenerate {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [Finite F] [CharP F 2] [FiniteDimensional F V] (B : BilinForm F V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate)
    (A : Subgroup (V ≃ₗ[F] V)) (hAB : A ≤ TauCeti.BilinForm.isometryGroup B)
    (hodd : Odd (Nat.card A)) :
    (B.restrict (ggA6SpFixed A)).Nondegenerate ∧
      IsCompl (ggA6SpFixed A) (B.orthogonal (ggA6SpFixed A)) := by
  classical
  have := finite_linearEquiv (K := F) (V := V)
  haveI : Fintype A := Fintype.ofFinite A
  have hA : (Fintype.card A : F) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact natCast_card_ne_zero_of_odd hodd
  have hnondeg : (B.restrict (ggA6SpFixed A)).Nondegenerate := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · apply Subtype.ext
      refine hnd.1 (x : V) fun v => ?_
      have h1 : B (x : V) (OrthSplit.avg A v) = 0 :=
        hx ⟨OrthSplit.avg A v, by
          rw [ggA6_sp_fixed_eq A hA]
          exact OrthSplit.avg_mem_fixSp v⟩
      have h2 : B (x : V) (v - OrthSplit.avg A v) = 0 :=
        ggA6_sp_fix_orth_free B A hA hAB x x.2 (v - OrthSplit.avg A v)
          (OrthSplit.sub_avg_mem_freeSp hA v)
      calc B (x : V) v
          = B (x : V) (OrthSplit.avg A v + (v - OrthSplit.avg A v)) := by
            rw [add_sub_cancel]
        _ = B (x : V) (OrthSplit.avg A v) + B (x : V) (v - OrthSplit.avg A v) := by
            rw [map_add]
        _ = 0 := by rw [h1, h2, add_zero]
    · apply Subtype.ext
      refine hnd.2 (x : V) fun v => ?_
      have h1 : B (OrthSplit.avg A v) (x : V) = 0 :=
        hx ⟨OrthSplit.avg A v, by
          rw [ggA6_sp_fixed_eq A hA]
          exact OrthSplit.avg_mem_fixSp v⟩
      have h2 : B (v - OrthSplit.avg A v) (x : V) = 0 :=
        (hB.isRefl.eq_iff).mp
          (ggA6_sp_fix_orth_free B A hA hAB x x.2 (v - OrthSplit.avg A v)
            (OrthSplit.sub_avg_mem_freeSp hA v))
      calc B v (x : V)
          = B (OrthSplit.avg A v + (v - OrthSplit.avg A v)) (x : V) := by
            rw [add_sub_cancel]
        _ = B (OrthSplit.avg A v) (x : V) + B (v - OrthSplit.avg A v) (x : V) := by
            rw [map_add, LinearMap.add_apply]
        _ = 0 := by rw [h1, h2, add_zero]
  exact ⟨hnondeg,
    (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal (W := ggA6SpFixed A)
      hB.isRefl).mp hnondeg⟩

private theorem ggA6_sp_B_add_add {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (B : BilinForm F V) (a b c d : V) :
    B (a + b) (c + d) = B a c + B a d + B b c + B b d := by
  simp only [map_add, LinearMap.add_apply]
  abel

private theorem ggA6_sp_isometry_of_fix_free {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V] (B : BilinForm F V) (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]
    (hA : (Fintype.card A : F) ≠ 0)
    (horth : ∀ x ∈ OrthSplit.fixSp A, ∀ y ∈ OrthSplit.freeSp A, B x y = 0)
    (hrefl : B.IsRefl)
    {g f : V ≃ₗ[F] V} (hgfix : ∀ x ∈ OrthSplit.fixSp A, g x ∈ OrthSplit.fixSp A)
    (hgb : ∀ v w, B (g v) (g w) = B v w)
    (hfix : ∀ x ∈ OrthSplit.fixSp A, f x = g x)
    (hfr : ∀ y ∈ OrthSplit.freeSp A, f y = y) :
    ∀ v w, B (f v) (f w) = B v w := by
  intro v w
  have hfv : f v = g (OrthSplit.avg A v) + (v - OrthSplit.avg A v) := by
    conv_lhs => rw [← add_sub_cancel (OrthSplit.avg A v) v]
    rw [map_add, hfix _ (OrthSplit.avg_mem_fixSp v),
      hfr _ (OrthSplit.sub_avg_mem_freeSp hA v)]
  have hfw : f w = g (OrthSplit.avg A w) + (w - OrthSplit.avg A w) := by
    conv_lhs => rw [← add_sub_cancel (OrthSplit.avg A w) w]
    rw [map_add, hfix _ (OrthSplit.avg_mem_fixSp w),
      hfr _ (OrthSplit.sub_avg_mem_freeSp hA w)]
  rw [hfv, hfw]
  have hgav : g (OrthSplit.avg A v) ∈ OrthSplit.fixSp A := hgfix _ (OrthSplit.avg_mem_fixSp v)
  have hgaw : g (OrthSplit.avg A w) ∈ OrthSplit.fixSp A := hgfix _ (OrthSplit.avg_mem_fixSp w)
  have hrv : v - OrthSplit.avg A v ∈ OrthSplit.freeSp A := OrthSplit.sub_avg_mem_freeSp hA v
  have hrw : w - OrthSplit.avg A w ∈ OrthSplit.freeSp A := OrthSplit.sub_avg_mem_freeSp hA w
  have h1 : B (g (OrthSplit.avg A v)) (w - OrthSplit.avg A w) = 0 := horth _ hgav _ hrw
  have h2 : B (v - OrthSplit.avg A v) (g (OrthSplit.avg A w)) = 0 :=
    (hrefl.eq_iff).mp (horth _ hgaw _ hrv)
  have h3 : B (g (OrthSplit.avg A v)) (g (OrthSplit.avg A w)) =
      B (OrthSplit.avg A v) (OrthSplit.avg A w) := hgb _ _
  have h4 : B (OrthSplit.avg A v) (w - OrthSplit.avg A w) = 0 :=
    horth _ (OrthSplit.avg_mem_fixSp v) _ hrw
  have h5 : B (v - OrthSplit.avg A v) (OrthSplit.avg A w) = 0 :=
    (hrefl.eq_iff).mp (horth _ (OrthSplit.avg_mem_fixSp w) _ hrv)
  conv_rhs => rw [← add_sub_cancel (OrthSplit.avg A v) v,
    ← add_sub_cancel (OrthSplit.avg A w) w]
  rw [ggA6_sp_B_add_add B, ggA6_sp_B_add_add B, h3, h1, h2, h4, h5]

private theorem ggA6_sp_isometry_of_free_fix {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V] (B : BilinForm F V) (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]
    (hA : (Fintype.card A : F) ≠ 0)
    (horth : ∀ x ∈ OrthSplit.fixSp A, ∀ y ∈ OrthSplit.freeSp A, B x y = 0)
    (hrefl : B.IsRefl)
    {g f : V ≃ₗ[F] V} (hgfree : ∀ y ∈ OrthSplit.freeSp A, g y ∈ OrthSplit.freeSp A)
    (hgb : ∀ v w, B (g v) (g w) = B v w)
    (hfr : ∀ y ∈ OrthSplit.freeSp A, f y = g y)
    (hfix : ∀ x ∈ OrthSplit.fixSp A, f x = x) :
    ∀ v w, B (f v) (f w) = B v w := by
  intro v w
  have hfv : f v = OrthSplit.avg A v + g (v - OrthSplit.avg A v) := by
    conv_lhs => rw [← add_sub_cancel (OrthSplit.avg A v) v]
    rw [map_add, hfix _ (OrthSplit.avg_mem_fixSp v),
      hfr _ (OrthSplit.sub_avg_mem_freeSp hA v)]
  have hfw : f w = OrthSplit.avg A w + g (w - OrthSplit.avg A w) := by
    conv_lhs => rw [← add_sub_cancel (OrthSplit.avg A w) w]
    rw [map_add, hfix _ (OrthSplit.avg_mem_fixSp w),
      hfr _ (OrthSplit.sub_avg_mem_freeSp hA w)]
  rw [hfv, hfw]
  have hgav : OrthSplit.avg A v ∈ OrthSplit.fixSp A := OrthSplit.avg_mem_fixSp v
  have hgaw : OrthSplit.avg A w ∈ OrthSplit.fixSp A := OrthSplit.avg_mem_fixSp w
  have hrv : v - OrthSplit.avg A v ∈ OrthSplit.freeSp A := OrthSplit.sub_avg_mem_freeSp hA v
  have hrw : w - OrthSplit.avg A w ∈ OrthSplit.freeSp A := OrthSplit.sub_avg_mem_freeSp hA w
  have hgrv : g (v - OrthSplit.avg A v) ∈ OrthSplit.freeSp A := hgfree _ hrv
  have hgrw : g (w - OrthSplit.avg A w) ∈ OrthSplit.freeSp A := hgfree _ hrw
  have h1 : B (OrthSplit.avg A v) (g (w - OrthSplit.avg A w)) = 0 := horth _ hgav _ hgrw
  have h2 : B (g (v - OrthSplit.avg A v)) (OrthSplit.avg A w) = 0 :=
    (hrefl.eq_iff).mp (horth _ hgaw _ hgrv)
  have h3 : B (g (v - OrthSplit.avg A v)) (g (w - OrthSplit.avg A w)) =
      B (v - OrthSplit.avg A v) (w - OrthSplit.avg A w) := hgb _ _
  have h4 : B (OrthSplit.avg A v) (w - OrthSplit.avg A w) = 0 := horth _ hgav _ hrw
  have h5 : B (v - OrthSplit.avg A v) (OrthSplit.avg A w) = 0 :=
    (hrefl.eq_iff).mp (horth _ hgaw _ hrv)
  conv_rhs => rw [← add_sub_cancel (OrthSplit.avg A v) v,
    ← add_sub_cancel (OrthSplit.avg A w) w]
  rw [ggA6_sp_B_add_add B, ggA6_sp_B_add_add B, h3, h1, h2, h4, h5]

theorem ggA6_sp_dichotomy {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [Finite F] [CharP F 2] [FiniteDimensional F V] (B : BilinForm F V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate)
    (A : Subgroup (V ≃ₗ[F] V)) (hAB : A ≤ TauCeti.BilinForm.isometryGroup B)
    (hodd : Odd (Nat.card A)) {J : Subgroup (V ≃ₗ[F] V)}
    (hJ : IsComponentOf J (TauCeti.BilinForm.isometryGroup B ⊓
      Subgroup.centralizer (A : Set (V ≃ₗ[F] V)))) :
    (∀ j ∈ J, ∀ v ∈ B.orthogonal (ggA6SpFixed A), j v = v) ∨
      (∀ j ∈ J, ∀ v ∈ ggA6SpFixed A, j v = v) := by
  classical
  haveI hfin : Finite (V ≃ₗ[F] V) := finite_linearEquiv (K := F) (V := V)
  haveI : Fintype A := Fintype.ofFinite A
  have hA : (Fintype.card A : F) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact natCast_card_ne_zero_of_odd hodd
  have hV0 : ggA6SpFixed A = OrthSplit.fixSp A := ggA6_sp_fixed_eq A hA
  have hV1 : B.orthogonal (ggA6SpFixed A) = OrthSplit.freeSp A :=
    ggA6_sp_orthogonal_eq_freeSp B hB hnd A hA hAB
  have horthFS : ∀ x ∈ OrthSplit.fixSp A, ∀ y ∈ OrthSplit.freeSp A, B x y = 0 := by
    intro x hx y hy
    exact ggA6_sp_fix_orth_free B A hA hAB x (by rw [hV0]; exact hx) y hy
  let C : Subgroup (V ≃ₗ[F] V) :=
    TauCeti.BilinForm.isometryGroup B ⊓ Subgroup.centralizer (A : Set (V ≃ₗ[F] V))
  let A₁ : Subgroup (V ≃ₗ[F] V) := C ⊓ ggA6SpFixer B (B.orthogonal (ggA6SpFixed A))
  let A₂ : Subgroup (V ≃ₗ[F] V) := C ⊓ ggA6SpFixer B (ggA6SpFixed A)
  have hpresV0 : ∀ c ∈ C, ∀ v ∈ ggA6SpFixed A, c v ∈ ggA6SpFixed A := by
    intro c hc v hv
    have hc' : c ∈ TauCeti.BilinForm.isometryGroup B ∧
        c ∈ Subgroup.centralizer (A : Set (V ≃ₗ[F] V)) := hc
    change ∀ a ∈ A, a (c v) = c v
    have hv' : ∀ a ∈ A, a v = v := hv
    intro a ha
    calc a (c v) = (a * c) v := rfl
      _ = (c * a) v := by rw [Subgroup.mem_centralizer_iff.mp hc'.2 a ha]
      _ = c (a v) := rfl
      _ = c v := by rw [hv' a ha]
  have hpresV1 : ∀ c ∈ C, ∀ v ∈ B.orthogonal (ggA6SpFixed A),
      c v ∈ B.orthogonal (ggA6SpFixed A) := by
    intro c hc v hv
    have hc' : c ∈ TauCeti.BilinForm.isometryGroup B ∧
        c ∈ Subgroup.centralizer (A : Set (V ≃ₗ[F] V)) := hc
    change ∀ n ∈ ggA6SpFixed A, B n (c v) = 0
    have hv' : ∀ n ∈ ggA6SpFixed A, B n v = 0 := hv
    intro n hn
    have hcn : (c⁻¹ : V ≃ₗ[F] V) n ∈ ggA6SpFixed A := hpresV0 c⁻¹ (C.inv_mem hc) n hn
    have hcc : c ((c⁻¹ : V ≃ₗ[F] V) n) = n := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    calc B n (c v) = B (c ((c⁻¹ : V ≃ₗ[F] V) n)) (c v) := by rw [hcc]
      _ = B ((c⁻¹ : V ≃ₗ[F] V) n) v :=
          TauCeti.BilinForm.mem_isometryGroup_iff.mp hc'.1 _ _
      _ = 0 := hv' _ hcn
  have key₁ : ∀ c ∈ C, ∀ h ∈ A₁, c * h * c⁻¹ ∈ A₁ := by
    intro c hc h hh
    have hc' : c ∈ TauCeti.BilinForm.isometryGroup B ∧
        c ∈ Subgroup.centralizer (A : Set (V ≃ₗ[F] V)) := hc
    have hh' : h ∈ C ∧ h ∈ ggA6SpFixer B (B.orthogonal (ggA6SpFixed A)) := hh
    refine ⟨?_, ?_⟩
    · exact C.mul_mem (C.mul_mem hc' hh'.1) (C.inv_mem hc')
    · refine ⟨?_, ?_⟩
      · exact (TauCeti.BilinForm.isometryGroup B).mul_mem
          ((TauCeti.BilinForm.isometryGroup B).mul_mem hc'.1 hh'.2.1)
          ((TauCeti.BilinForm.isometryGroup B).inv_mem hc'.1)
      · intro u hu
        have hcu : (c⁻¹ : V ≃ₗ[F] V) u ∈ B.orthogonal (ggA6SpFixed A) :=
          hpresV1 c⁻¹ (C.inv_mem hc') u hu
        have hcc : c ((c⁻¹ : V ≃ₗ[F] V) u) = u := by
          rw [← LinearEquiv.mul_apply, mul_inv_cancel]
          rfl
        show (c * h * c⁻¹) u = u
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hh'.2.2 _ hcu, hcc]
  have key₂ : ∀ c ∈ C, ∀ h ∈ A₂, c * h * c⁻¹ ∈ A₂ := by
    intro c hc h hh
    have hc' : c ∈ TauCeti.BilinForm.isometryGroup B ∧
        c ∈ Subgroup.centralizer (A : Set (V ≃ₗ[F] V)) := hc
    have hh' : h ∈ C ∧ h ∈ ggA6SpFixer B (ggA6SpFixed A) := hh
    refine ⟨?_, ?_⟩
    · exact C.mul_mem (C.mul_mem hc' hh'.1) (C.inv_mem hc')
    · refine ⟨?_, ?_⟩
      · exact (TauCeti.BilinForm.isometryGroup B).mul_mem
          ((TauCeti.BilinForm.isometryGroup B).mul_mem hc'.1 hh'.2.1)
          ((TauCeti.BilinForm.isometryGroup B).inv_mem hc'.1)
      · intro u hu
        have hcu : (c⁻¹ : V ≃ₗ[F] V) u ∈ ggA6SpFixed A :=
          hpresV0 c⁻¹ (C.inv_mem hc') u hu
        have hcc : c ((c⁻¹ : V ≃ₗ[F] V) u) = u := by
          rw [← LinearEquiv.mul_apply, mul_inv_cancel]
          rfl
        show (c * h * c⁻¹) u = u
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hh'.2.2 _ hcu, hcc]
  have hnormal₁ : (A₁.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (H := A₁) (K := C) inf_le_left]
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact key₁ c hc h hh
    · intro hh
      have h2 := key₁ c⁻¹ (C.inv_mem hc) (c * h * c⁻¹) hh
      have heq : c⁻¹ * (c * h * c⁻¹) * (c⁻¹)⁻¹ = h := by group
      rwa [heq] at h2
  have hnormal₂ : (A₂.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (H := A₂) (K := C) inf_le_left]
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact key₂ c hc h hh
    · intro hh
      have h2 := key₂ c⁻¹ (C.inv_mem hc) (c * h * c⁻¹) hh
      have heq : c⁻¹ * (c * h * c⁻¹) * (c⁻¹)⁻¹ = h := by group
      rwa [heq] at h2
  have hdecomp : ∀ g ∈ C, ∃ g₀ ∈ A₁, ∃ g₁ ∈ A₂, g = g₀ * g₁ := by
    intro g hg
    have hg' : g ∈ TauCeti.BilinForm.isometryGroup B ∧
        g ∈ Subgroup.centralizer (A : Set (V ≃ₗ[F] V)) := hg
    have hgs : g ∈ OrthSplit.stab A := OrthSplit.centralizer_le_stab hg'.2
    let f₀ : OrthSplit.fixSp A ≃ₗ[F] OrthSplit.fixSp A := OrthSplit.restrFix A ⟨g, hgs⟩
    let f₁ : OrthSplit.freeSp A ≃ₗ[F] OrthSplit.freeSp A := OrthSplit.restrFree A ⟨g, hgs⟩
    let g₀ : V ≃ₗ[F] V := OrthSplit.split hA (f₀, 1)
    let g₁ : V ≃ₗ[F] V := OrthSplit.split hA (1, f₁)
    have hgb : ∀ v w, B (g v) (g w) = B v w :=
      TauCeti.BilinForm.mem_isometryGroup_iff.mp hg'.1
    have hgfix : ∀ x ∈ OrthSplit.fixSp A, g x ∈ OrthSplit.fixSp A := by
      intro x hx
      obtain ⟨u, rfl⟩ := hx
      rw [OrthSplit.commute_avg hg'.2]
      exact OrthSplit.avg_mem_fixSp (g u)
    have hgfree : ∀ y ∈ OrthSplit.freeSp A, g y ∈ OrthSplit.freeSp A := by
      intro y hy
      rw [OrthSplit.freeSp, LinearMap.mem_ker] at hy ⊢
      rw [← OrthSplit.commute_avg hg'.2 y, hy, map_zero]
    have hg_split : g = g₀ * g₁ := by
      have h1 : OrthSplit.split hA (f₀, f₁) = g := by
        refine LinearEquiv.ext fun v => ?_
        rw [OrthSplit.split_apply]
        show g (OrthSplit.avg A v) + g (v - OrthSplit.avg A v) = g v
        rw [← map_add, add_sub_cancel]
      have h2 : (f₀, 1) * (1, f₁) = (f₀, f₁) :=
        Prod.ext (mul_one f₀) (one_mul f₁)
      calc g = OrthSplit.split hA (f₀, f₁) := h1.symm
        _ = OrthSplit.split hA ((f₀, 1) * (1, f₁)) := by rw [h2]
        _ = OrthSplit.split hA (f₀, 1) * OrthSplit.split hA (1, f₁) := by rw [map_mul]
        _ = g₀ * g₁ := rfl
    have hg₀_apply : ∀ v, g₀ v = g (OrthSplit.avg A v) + (v - OrthSplit.avg A v) := by
      intro v
      change OrthSplit.split hA (f₀, 1) v =
        g (OrthSplit.avg A v) + (v - OrthSplit.avg A v)
      rw [OrthSplit.split_apply]
      rfl
    have hg₁_apply : ∀ v, g₁ v = OrthSplit.avg A v + g (v - OrthSplit.avg A v) := by
      intro v
      change OrthSplit.split hA (1, f₁) v =
        OrthSplit.avg A v + g (v - OrthSplit.avg A v)
      rw [OrthSplit.split_apply]
      rfl
    have hfix₀ : ∀ x ∈ OrthSplit.fixSp A, g₀ x = g x := by
      intro x hx
      change OrthSplit.split hA (f₀, 1) (⟨x, hx⟩ : OrthSplit.fixSp A) = g x
      rw [OrthSplit.split_apply_fix]
      rfl
    have hfr₀ : ∀ y ∈ OrthSplit.freeSp A, g₀ y = y := by
      intro y hy
      change OrthSplit.split hA (f₀, 1) (⟨y, hy⟩ : OrthSplit.freeSp A) = y
      rw [OrthSplit.split_apply_free]
      rfl
    have hfr₁ : ∀ y ∈ OrthSplit.freeSp A, g₁ y = g y := by
      intro y hy
      change OrthSplit.split hA (1, f₁) (⟨y, hy⟩ : OrthSplit.freeSp A) = g y
      rw [OrthSplit.split_apply_free]
      rfl
    have hfix₁ : ∀ x ∈ OrthSplit.fixSp A, g₁ x = x := by
      intro x hx
      change OrthSplit.split hA (1, f₁) (⟨x, hx⟩ : OrthSplit.fixSp A) = x
      rw [OrthSplit.split_apply_fix]
      rfl
    have hiso₀ : g₀ ∈ TauCeti.BilinForm.isometryGroup B :=
      TauCeti.BilinForm.mem_isometryGroup_iff.mpr
        (ggA6_sp_isometry_of_fix_free B A hA horthFS hB.isRefl hgfix hgb hfix₀ hfr₀)
    have hiso₁ : g₁ ∈ TauCeti.BilinForm.isometryGroup B :=
      TauCeti.BilinForm.mem_isometryGroup_iff.mpr
        (ggA6_sp_isometry_of_free_fix B A hA horthFS hB.isRefl hgfree hgb hfr₁ hfix₁)
    have hcomm₀ : g₀ ∈ Subgroup.centralizer (A : Set (V ≃ₗ[F] V)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      refine LinearEquiv.ext fun v => ?_
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      rw [hg₀_apply, hg₀_apply, OrthSplit.avg_apply_apply ha v, map_add]
      congr 1
      · rw [← LinearEquiv.mul_apply, Subgroup.mem_centralizer_iff.mp hg'.2 a ha,
          LinearEquiv.mul_apply, OrthSplit.apply_avg ha v]
      · rw [map_sub, OrthSplit.apply_avg ha v]
    have hcomm₁ : g₁ ∈ Subgroup.centralizer (A : Set (V ≃ₗ[F] V)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      refine LinearEquiv.ext fun v => ?_
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      rw [hg₁_apply, hg₁_apply, OrthSplit.avg_apply_apply ha v, map_add]
      congr 1
      · rw [OrthSplit.apply_avg ha v]
      · rw [← LinearEquiv.mul_apply, Subgroup.mem_centralizer_iff.mp hg'.2 a ha,
          LinearEquiv.mul_apply, map_sub, OrthSplit.apply_avg ha v]
    have hg₀C : g₀ ∈ C := ⟨hiso₀, hcomm₀⟩
    have hg₁C : g₁ ∈ C := ⟨hiso₁, hcomm₁⟩
    have hg₀fixV₁ : ∀ u ∈ B.orthogonal (ggA6SpFixed A), g₀ u = u := by
      intro u hu
      exact hfr₀ u (by rw [← hV1]; exact hu)
    have hg₁fixV₀ : ∀ u ∈ ggA6SpFixed A, g₁ u = u := by
      intro u hu
      exact hfix₁ u (by rw [← hV0]; exact hu)
    exact ⟨g₀, ⟨hg₀C, ⟨hiso₀, hg₀fixV₁⟩⟩, g₁, ⟨hg₁C, ⟨hiso₁, hg₁fixV₀⟩⟩, hg_split⟩
  have hsup : A₁.subgroupOf C ⊔ A₂.subgroupOf C = ⊤ := by
    apply le_antisymm le_top
    intro x _
    obtain ⟨g₀, hg₀A₁, g₁, hg₁A₂, hxg⟩ := hdecomp (x : V ≃ₗ[F] V) x.2
    have hxg' : x = ⟨g₀, hg₀A₁.1⟩ * ⟨g₁, hg₁A₂.1⟩ := by
      apply Subtype.ext
      exact hxg
    rw [hxg']
    exact (A₁.subgroupOf C ⊔ A₂.subgroupOf C).mul_mem
      (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hg₀A₁))
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr hg₁A₂))
  have hJsub : CFSG.Assembly.IsComponentOf (J.subgroupOf C) (C.subgroupOf C) :=
    ggIsComponentOf_subgroupOf hJ le_rfl
  have hJtop : CFSG.Assembly.IsComponentOf (J.subgroupOf C) ⊤ := by
    simpa [Subgroup.subgroupOf_self] using hJsub
  have hJopen : CFSG.Open.IsComponentOf (J.subgroupOf C) ⊤ :=
    CFSG.Assembly.isComponentOf_iff_open.mp hJtop
  haveI := hnormal₁
  haveI := hnormal₂
  have hchoice := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_component_le_or_le
    (X := ↥C) (A₁ := A₁.subgroupOf C) (A₂ := A₂.subgroupOf C)
    (K' := J.subgroupOf C) hsup hJopen
  rcases hchoice with hle₁ | hle₂
  · left
    intro j hj
    have hjm : (⟨j, hJ.1 hj⟩ : ↥C) ∈ A₁.subgroupOf C := hle₁ (Subgroup.mem_subgroupOf.mpr hj)
    have hjA₁ : j ∈ A₁ := Subgroup.mem_subgroupOf.mp hjm
    have hjfix : j ∈ ggA6SpFixer B (B.orthogonal (ggA6SpFixed A)) :=
      (Subgroup.mem_inf.mp hjA₁).2
    intro v hv
    exact hjfix.2 v hv
  · right
    intro j hj
    have hjm : (⟨j, hJ.1 hj⟩ : ↥C) ∈ A₂.subgroupOf C := hle₂ (Subgroup.mem_subgroupOf.mpr hj)
    have hjA₂ : j ∈ A₂ := Subgroup.mem_subgroupOf.mp hjm
    have hjfix : j ∈ ggA6SpFixer B (ggA6SpFixed A) := (Subgroup.mem_inf.mp hjA₂).2
    intro v hv
    exact hjfix.2 v hv

end CFSG.StandardType.A6Red
