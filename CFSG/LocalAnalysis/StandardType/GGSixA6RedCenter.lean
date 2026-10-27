module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedDefs
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
public import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
public import CFSG.LieType.Steinberg.Adjoint.Perfect
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Steinberg.CentralExt.SpCentrallyClosed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Chevalley

section Genuine

theorem ggA6_center_le
    (t : StatedLieTag) (ht : t = .PSp ∨ t = .F4)
    (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ B₁ : Subgroup X) :
    ψ.range = G₀ → ψ.ker ≤ Subgroup.center (ggU t n f).K →
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f → p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card (Subgroup.centralizer (G₀ : Set X)) →
    B₁ ≤ Subgroup.normalizer (G₀ : Set X) →
    (∀ b ∈ B₁, GGPsiInnerDiag (ggU t n f).D ψ b) → IsElemAbelian p B₁ →
    Subgroup.center ↥G₀ = ⊥ ∧ B₁ ≤ G₀ := by
  intro hr hk hLie hp _hp2 hcop hBN hdiag hab
  have hadm : StatedLieAdmissible t n 2 f := LieModel.admissible hLie
  have hZK : Subgroup.center (ggU t n f).K = ⊥ := by
    rcases ht with rfl | rfl
    · have hn : 2 ≤ n := hadm.2.2.1
      exact CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (m := n)
        (F := GaloisField 2 f) (by omega)
    · exact CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .F4) (K := GaloisField 2 f)
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hk.trans hZK.le
  have hperfK : commutator (ggU t n f).K = ⊤ := by
    rcases ht with rfl | rfl
    · have hcard : Nat.card (GaloisField 2 f) = 2 ^ f :=
        GaloisField.card 2 f (by have := hadm.2.1; omega)
      exact (Symplectic.isQuasisimple_of_admissible n (GaloisField 2 f) hadm hcard).1.commutator_eq_top
    · exact (CFSG.LieType.Steinberg.Adjoint.isPerfect_f4 (K := GaloisField 2 f)).commutator_eq_top
  have hperfG : commutator ↥G₀ = ⊤ := by
    have hKperf : Group.IsPerfect (ggU t n f).K := Group.isPerfect_def.mpr hperfK
    have hsurj : Function.Surjective (ψ.codRestrict G₀ (fun a => hr ▸ ⟨a, rfl⟩)) := by
      intro g
      have hg : (g : X) ∈ ψ.range := by rw [hr]; exact g.2
      obtain ⟨a, ha⟩ := hg
      exact ⟨a, Subtype.ext ha⟩
    haveI : Group.IsPerfect (ggU t n f).K := hKperf
    exact Group.isPerfect_def.mp (Group.IsPerfect.ofSurjective
      (f := ψ.codRestrict G₀ (fun a => hr ▸ ⟨a, rfl⟩)) hsurj)
  have hpres : GGPresentsG0 G₀ (ggU t n f).D t n f ψ :=
    ⟨⟨hadm, by rcases ht with rfl | rfl <;> first
        | exact hadm.2.2.1
        | (show 2 ≤ 4; norm_num)⟩, ⟨hr, hk⟩, hperfG, hLie⟩
  have hZG : Subgroup.center ↥G₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, ha⟩ : (x : X) ∈ ψ.range := by rw [hr]; exact x.2
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hza : a ∈ Subgroup.center (ggU t n f).K := by
      rw [Subgroup.mem_center_iff]
      intro b
      apply hinj
      have h1 := Subgroup.mem_center_iff.mp hx ⟨ψ b, hr ▸ ⟨b, rfl⟩⟩
      have h2 := congrArg Subtype.val h1
      simpa only [Subgroup.coe_mul, ha, map_mul] using h2
    rw [hZK, Subgroup.mem_bot] at hza
    rw [← ha, hza, map_one]
    rfl
  refine ⟨hZG, ?_⟩
  intro b hb
  have htag : GGInnerTag t := by rcases ht with rfl | rfl <;> simp [GGInnerTag]
  obtain ⟨g, hg, hbg⟩ := ggPsiDiagInnerAt_of_ggInnerTag t htag X n f ψ G₀ hpres b (hBN hb)
    (hdiag b hb)
  have hbp : b ^ p = 1 := hab.2 b hb
  let c : X := b * g
  have hcC : c ∈ Subgroup.centralizer (G₀ : Set X) := hbg
  have hb_eq : b = c * g⁻¹ := by dsimp [c]; group
  have hcg : c * g = g * c := (Subgroup.mem_centralizer_iff.mp hcC g hg).symm
  have hcomm : Commute c g := hcg
  have hbp' : (c * g⁻¹) ^ p = 1 := by rw [← hb_eq]; exact hbp
  have hcp_eq : c ^ p = g ^ p := by
    have h1 : c ^ p * (g ^ p)⁻¹ = 1 := by
      rw [hcomm.inv_right.mul_pow, inv_pow] at hbp'
      exact hbp'
    calc c ^ p = c ^ p * (g ^ p)⁻¹ * g ^ p := by group
      _ = 1 * g ^ p := by rw [h1]
      _ = g ^ p := by group
  have hcpmem : c ^ p ∈ G₀ := by rw [hcp_eq]; exact Subgroup.pow_mem G₀ hg p
  have hzmem : (⟨c ^ p, hcpmem⟩ : ↥G₀) ∈ Subgroup.center ↥G₀ := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp
      (Subgroup.pow_mem (Subgroup.centralizer (G₀ : Set X)) hcC p) (y : X) y.2
  have hz1 : (⟨c ^ p, hcpmem⟩ : ↥G₀) = 1 := by
    rw [hZG, Subgroup.mem_bot] at hzmem
    exact hzmem
  have hcp1 : c ^ p = 1 := by simpa using congrArg Subtype.val hz1
  have hc1 : c = 1 := by
    have hdvd : orderOf c ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hcp1
    have hdvd' : orderOf c ∣ Nat.card (Subgroup.centralizer (G₀ : Set X)) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.centralizer (G₀ : Set X)) hcC
    rcases hp.eq_one_or_self_of_dvd (orderOf c) hdvd with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · exact absurd (h1 ▸ hdvd') hcop
  rw [hb_eq, hc1, one_mul]
  exact Subgroup.inv_mem G₀ hg

end Genuine

end CFSG.StandardType.A6Red
