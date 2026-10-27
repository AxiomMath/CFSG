module

public import CFSG.LocalAnalysis.StandardType.GGNsq2QuotHyp
public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks
import CFSG.LocalAnalysis.StandardType.GGQTwoDGNUnitGen
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType

open scoped commutatorElement
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary CFSG.ClassicalInvolution.Phan

private theorem p9uNSG_commutator_sup_center_le {Y : Type*} [Group Y] (J : Subgroup Y) :
    ⁅J ⊔ Subgroup.center Y, J ⊔ Subgroup.center Y⁆ ≤ ⁅J, J⁆ := by
  rw [Subgroup.commutator_le]
  intro u hu v hv
  obtain ⟨j₁, hj₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hu
  obtain ⟨j₂, hj₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hv
  have h1 : z₁ * (j₂ * z₂) = (j₂ * z₂) * z₁ := (Subgroup.mem_center_iff.1 hz₁ _).symm
  have h2 : z₂ * j₁⁻¹ = j₁⁻¹ * z₂ := (Subgroup.mem_center_iff.1 hz₂ _).symm
  have e : ⁅j₁ * z₁, j₂ * z₂⁆ = ⁅j₁, j₂⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc j₁ * z₁ * (j₂ * z₂) * (j₁ * z₁)⁻¹ * (j₂ * z₂)⁻¹
        = j₁ * (z₁ * (j₂ * z₂)) * z₁⁻¹ * j₁⁻¹ * z₂⁻¹ * j₂⁻¹ := by group
      _ = j₁ * j₂ * (z₂ * j₁⁻¹) * z₂⁻¹ * j₂⁻¹ := by rw [h1]; group
      _ = j₁ * j₂ * j₁⁻¹ * j₂⁻¹ := by rw [h2]; group
  rw [e]
  exact Subgroup.commutator_mem_commutator hj₁ hj₂

namespace NsQuot

variable {G : Type} [Group G] [Finite G] {Q : Type} [Group Q]

theorem Datum.eq_iSup_of_img_coordBlockSU {p : ℕ} {N : Subgroup G} {f : ↥N →* Q}
    {X Bs Z : Subgroup G} (hD : Datum p N f X Bs Z) (hX : commutator ↥X = ⊤) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) {n : ℕ} (hn : 4 ≤ n)
    (ψ : Su K 2 1 n →* Q) (hψ : ψ.range = img N f X) (E : Finset (Fin n) → Subgroup G)
    (hEX : ∀ T : Finset (Fin n), T.card = 3 → E T ≤ X)
    (hE : ∀ T : Finset (Fin n), T.card = 3 → img N f (E T) = (coordBlockSU K 2 1 T).map ψ) :
    X = ⨆ (T : Finset (Fin n)) (_ : T.card = 3), E T := by
  set P := ⨆ (T : Finset (Fin n)) (_ : T.card = 3), E T with hP
  have hPX : P ≤ X := iSup₂_le fun T hT => hEX T hT
  have himg : img N f X ≤ img N f P := by
    rw [← hψ, MonoidHom.range_eq_map, ← QTwo.iSup_coordBlockSU_card_three_eq_top hK hn,
      Subgroup.map_iSup]
    refine iSup_le fun T => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hT => ?_
    rw [← hE T hT]
    exact img_mono (le_iSup₂_of_le T hT le_rfl)
  have hdec : ∀ x ∈ X, ∃ u ∈ P, ∃ z ∈ Z, x = u * z := by
    intro x hx
    have hxN : x ∈ N := hD.LN hx
    obtain ⟨u, huP, hu⟩ := mem_img.mp (himg (mem_img.mpr ⟨⟨x, hxN⟩, hx, rfl⟩))
    have hker : u⁻¹ * ⟨x, hxN⟩ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hu, inv_mul_cancel]
    refine ⟨u, huP, (u : G)⁻¹ * x, (hD.mem_ker_iff _).mp hker, by group⟩
  have htop : (⊤ : Subgroup ↥X) ≤ P.subgroupOf X ⊔ Subgroup.center ↥X := by
    intro x _
    obtain ⟨u, huP, z, hz, hxuz⟩ := hdec x x.2
    have huX : (u : G) ∈ X := hPX huP
    have hzX : z ∈ X := hD.ZL hz
    have hx : x = ⟨u, huX⟩ * ⟨z, hzX⟩ := Subtype.ext hxuz
    rw [hx]
    refine mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr huP))
      (Subgroup.mem_sup_right ?_)
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (hD.Zcent z hz l l.2)
  have hle : (⊤ : Subgroup ↥X) ≤ P.subgroupOf X := by
    calc (⊤ : Subgroup ↥X) = commutator ↥X := hX.symm
      _ = ⁅(⊤ : Subgroup ↥X), ⊤⁆ := commutator_def ↥X
      _ ≤ ⁅P.subgroupOf X ⊔ Subgroup.center ↥X, P.subgroupOf X ⊔ Subgroup.center ↥X⁆ :=
          Subgroup.commutator_mono htop htop
      _ ≤ ⁅P.subgroupOf X, P.subgroupOf X⁆ := p9uNSG_commutator_sup_center_le _
      _ ≤ P.subgroupOf X := Subgroup.commutator_le.mpr fun g hg h hh => by
          rw [commutatorElement_def]
          exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  refine le_antisymm (fun x hx => ?_) hPX
  exact Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_top (⟨x, hx⟩ : ↥X)))

end NsQuot

end CFSG.StandardType

end
